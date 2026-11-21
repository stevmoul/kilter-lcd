#!/usr/bin/env python3
"""Climb data for the Kilter LCD.

Two jobs:

  ledmap   Run once on your computer. Reads the Aurora-era kilter.db
           (from `boardlib database kilter kilter.db`) and saves your wall's
           hold -> LED mapping and the grade names to board.json. The LED
           wiring of your board never changes, so this never needs redoing.

  build    Run every night (GitHub Actions does it for you). Downloads the
           latest public Kilter climb snapshot from Boardsesh, matches every
           climb against board.json, and writes climbs.bin + climbs.txt for
           the screen to download.

  inspect  Shows what the Boardsesh manifest contains and which files
           `build` would download. Use it if `build` can't find the snapshot.

Examples:
  python kilter_data.py ledmap kilter.db --list-sizes
  python kilter_data.py ledmap kilter.db --size-id 17 --angle 40 -o ../board.json
  python kilter_data.py build --board ../board.json --out ../site
  python kilter_data.py build --board ../board.json --out ../site --snapshot kilter-8.db.gz
"""
import argparse
import gzip
import hashlib
import json
import math
import re
import shutil
import sqlite3
import ssl
import struct
import sys
import tempfile
import time
import unicodedata
import urllib.parse
import urllib.request
from pathlib import Path

DEFAULT_MANIFESTS = [
    "https://snapshots.boardsesh.com/board-snapshots/v1-gzip/manifest.json",
    "https://boardsesh-board-snapshots.t3.tigrisfiles.io/board-snapshots/v1/manifest.json",
]
USER_AGENT = "kilter-lcd/2 (+home display; one download per day)"
MAX_DOWNLOAD = 400 * 1024 * 1024        # per compressed file
MAX_DECODED = 2 * 1024 * 1024 * 1024    # per decompressed file (bomb guard)
FRAME_TOKEN = re.compile(r"p(\d+)r(\d+)")
SHA256_HEX = re.compile(r"^[0-9a-fA-F]{64}$")
MAX_NAME = 48
WALL_LEN = 40
GRADE_LEN = 16
MAGIC, COMMIT_MAGIC, FORMAT_VERSION = b"KLCD", b"KCOK", 2
SECTOR = 4096


# ---------------------------------------------------------------- helpers
def die(msg):
    sys.exit(f"error: {msg}")


def hash_positions(positions):
    """FNV-1a 64 over sorted unique LED positions (2 bytes LE each).

    A non-cryptographic lookup key only. Must match aurora::hashPositions().
    """
    h = 0xCBF29CE484222325
    for p in sorted(set(positions)):
        for byte in (p & 0xFF, (p >> 8) & 0xFF):
            h = ((h ^ byte) * 0x100000001B3) & 0xFFFFFFFFFFFFFFFF
    return h


def ascii_text(text, limit):
    folded = unicodedata.normalize("NFKD", text or "").encode("ascii", "ignore").decode("ascii")
    folded = " ".join("".join(c for c in folded if 32 <= ord(c) < 127).split())
    return folded[:limit].rstrip()


def open_ro(path):
    return sqlite3.connect(Path(path).resolve().as_uri() + "?mode=ro", uri=True)


def tables(conn):
    return {r[0] for r in conn.execute("SELECT name FROM sqlite_master WHERE type='table'")}


def columns(conn, table):
    # table comes from sqlite_master of a file we opened, and is quoted
    return {r[1] for r in conn.execute(f'PRAGMA table_info("{table}")')}


def pick(cols, *names):
    return next((n for n in names if n in cols), None)


# ---------------------------------------------------------------- ledmap
def cmd_ledmap(args):
    conn = open_ro(args.database)
    need = {"placements", "leds", "product_sizes", "layouts", "difficulty_grades"}
    if not need <= tables(conn):
        die("that file doesn't look like kilter.db from boardlib")
    if args.list_sizes or args.size_id is None:
        products = dict(conn.execute("SELECT id, name FROM products")) if "products" in tables(conn) else {}
        print("Wall sizes (use yours with --size-id):")
        for sid, pid, name, desc in conn.execute(
                "SELECT id, product_id, name, description FROM product_sizes ORDER BY product_id, id"):
            print(f"  size-id {sid:>3}  {products.get(pid, pid)!s:<26} {name or ''} {desc or ''}")
        return
    row = conn.execute("SELECT product_id, name, description FROM product_sizes WHERE id = ?",
                       (args.size_id,)).fetchone()
    if not row:
        die(f"no wall size {args.size_id}; run with --list-sizes")
    layout_id = args.layout_id
    if layout_id is None:
        layouts = conn.execute("SELECT id, name FROM layouts WHERE product_id = ?", (row[0],)).fetchall()
        if len(layouts) != 1:
            die("several layouts fit: " + ", ".join(f"{i} ({n})" for i, n in layouts) + "; add --layout-id")
        layout_id = layouts[0][0]
    leds = {str(pid): int(pos) for pid, pos in conn.execute(
        "SELECT p.id, l.position FROM placements p JOIN leds l ON l.hole_id = p.hole_id "
        "WHERE p.layout_id = ? AND l.product_size_id = ?", (layout_id, args.size_id))}
    if not leds:
        die("no LEDs for that size/layout pair")
    grades = {str(int(d)): str(n) for d, n in conn.execute("SELECT difficulty, boulder_name FROM difficulty_grades")}
    board = {
        "format": 1,
        "board_type": "kilter",
        "wall": ascii_text(" ".join(x for x in row[1:] if x), WALL_LEN),
        "size_id": args.size_id,
        "layout_id": layout_id,
        "angle": args.angle,
        "leds": leds,
        "grades": grades,
    }
    Path(args.out).write_text(json.dumps(board, indent=1, sort_keys=True))
    print(f"Saved {len(leds)} holds for '{board['wall']}' (layout {layout_id}) to {args.out}")


def load_board(path):
    try:
        b = json.loads(Path(path).read_text())
        assert b.get("format") == 1
        b["leds"] = {int(k): int(v) for k, v in b["leds"].items()}
        b["grades"] = {int(k): str(v) for k, v in b["grades"].items()}
        for key in ("size_id", "layout_id", "angle"):
            b[key] = int(b[key])
        assert 0 <= b["angle"] <= 90 and b["leds"] and all(0 <= v < 65536 for v in b["leds"].values())
        return b
    except (OSError, ValueError, KeyError, AssertionError, TypeError) as exc:
        die(f"{path} is missing or invalid ({exc.__class__.__name__}); re-run `ledmap`")


# ---------------------------------------------------------------- download
def tls_context():
    """Certificate-checking TLS. Uses certifi's up-to-date roots when installed (older macOS Pythons need this)."""
    try:
        import certifi
        return ssl.create_default_context(cafile=certifi.where())
    except ImportError:
        return ssl.create_default_context()


def fetch(url, dest=None, limit=MAX_DOWNLOAD):
    if urllib.parse.urlparse(url).scheme != "https":
        die(f"refusing non-HTTPS URL: {url}")
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    sha, total = hashlib.sha256(), 0
    with urllib.request.urlopen(req, timeout=60, context=tls_context()) as resp:  # verifies certificates
        out = open(dest, "wb") if dest else None
        chunks = []
        try:
            while True:
                block = resp.read(1 << 16)
                if not block:
                    break
                total += len(block)
                if total > limit:
                    die(f"download larger than {limit // 2**20} MB: {url}")
                sha.update(block)
                (out.write(block) if out else chunks.append(block))
        finally:
            if out:
                out.close()
    return (b"".join(chunks) if not dest else total), sha.hexdigest()


def load_manifest(urls):
    for url in urls:
        try:
            body, _ = fetch(url, limit=20 * 1024 * 1024)
            return url, json.loads(body)
        except (OSError, ValueError) as exc:
            print(f"  manifest not available at {url} ({exc.__class__.__name__})")
    die("couldn't load a Boardsesh manifest; pass --manifest URL or --snapshot FILE")


ARTIFACT = re.compile(r"\.(db|sqlite3?)(\.gz)?$|\.gz$", re.I)
BOARD_KEYS = ("boardType", "board_type", "board", "boardName")
LAYOUT_KEYS = ("layoutId", "layout_id", "layout")
BOARD_NAMES = {"kilter", "tension", "decoy", "touchstone", "grasshopper", "moonboard", "soill", "woods", "spray"}


def _as_int(v):
    try:
        return int(v)
    except (TypeError, ValueError):
        return None


def _key_context(key):
    m = re.fullmatch(r"([a-z]+)(?:[:/_-](\d+))?", str(key).lower())
    if m:
        return m.group(1), _as_int(m.group(2))
    return (None, int(key)) if str(key).isdigit() else (None, None)


def _add_ref(out, val, sha, board, layout, field):
    m = re.search(r"(?:^|/)([a-z]+)[/_:-](\d+)(?:[/_.-]|$)", val.lower())
    out.append({"ref": val, "sha256": sha, "board": board or (m and m.group(1)),
                "layout": layout if layout is not None else (m and int(m.group(2))), "field": field})


def _is_artifact(val):
    return isinstance(val, str) and bool(ARTIFACT.search(urllib.parse.urlparse(val).path))


def find_artifacts(node, board=None, layout=None, out=None):
    """Walk any manifest shape, remembering which board/layout each file belongs to."""
    out = [] if out is None else out
    if isinstance(node, list):
        for item in node:
            if _is_artifact(item):
                _add_ref(out, item, None, board, layout, "list")
            else:
                find_artifacts(item, board, layout, out)
    elif isinstance(node, dict):
        b = next((str(node[k]).lower() for k in BOARD_KEYS if isinstance(node.get(k), str)), board)
        l = next((_as_int(node[k]) for k in LAYOUT_KEYS if _as_int(node.get(k)) is not None), layout)
        sha = next((str(v) for k, v in node.items()
                    if isinstance(v, str) and SHA256_HEX.match(v) and ("sha" in k.lower() or "checksum" in k.lower())), None)
        for key, val in node.items():
            if _is_artifact(val):
                _add_ref(out, val, sha, b, l, key)
            elif isinstance(val, (dict, list)):
                kb, kl = _key_context(key)
                if kb and kb not in BOARD_NAMES:
                    kb = None  # an ordinary key such as "entries"
                find_artifacts(val, kb or b, kl if kl is not None else l, out)
    return out


def resolve(base, ref):
    """Turn a manifest reference into a full URL.

    Boardsesh lists each file both as a full URL and as a path from the site
    root ("board-snapshots/v1-gzip/..."), so a path whose first folder matches
    the manifest's first folder is resolved from the site root, not the manifest folder.
    """
    if urllib.parse.urlparse(ref).scheme:
        return ref
    parsed = urllib.parse.urlparse(base)
    first = parsed.path.lstrip("/").split("/", 1)[0]
    if ref.startswith("/") or (first and ref.split("/", 1)[0] == first):
        return f"{parsed.scheme}://{parsed.netloc}/{ref.lstrip('/')}"
    return urllib.parse.urljoin(base, ref)


def choose_artifacts(found, board_type, layout_id, base):
    exact = [a for a in found if a["board"] == board_type and a["layout"] == layout_id]
    board_wide = [a for a in found if a["board"] == board_type and a["layout"] is None
                  and "catalog" not in a["ref"].lower()]
    by_file = {}
    for a in exact + board_wide:
        url = resolve(base, a["ref"])
        name = urllib.parse.urlparse(url).path.rsplit("/", 1)[-1]
        prev = by_file.get(name)
        # one download per file name: prefer a full URL from the manifest, keep any checksum
        if prev is None or (urllib.parse.urlparse(a["ref"]).scheme and not urllib.parse.urlparse(prev["ref"]).scheme):
            by_file[name] = dict(a, url=url, sha256=a["sha256"] or (prev or {}).get("sha256"))
        elif a["sha256"] and not prev["sha256"]:
            prev["sha256"] = a["sha256"]
    return list(by_file.values())


def download_snapshots(manifest_urls, board_type, layout_id, workdir):
    base, manifest = load_manifest(manifest_urls)
    chosen = choose_artifacts(find_artifacts(manifest), board_type, layout_id, base)
    if not chosen:
        die(f"the manifest has no {board_type} layout {layout_id} files; run `inspect` and pass --snapshot")
    paths = []
    for i, art in enumerate(chosen):
        url = art["url"]
        raw = Path(workdir) / f"snap{i}.bin"
        print(f"  downloading {url}")
        _, digest = fetch(url, raw)
        if art["sha256"]:
            if digest.lower() != art["sha256"].lower():
                die(f"checksum mismatch for {url}")
            print("  checksum OK")
        else:
            print("  (manifest lists no SHA-256 for this file; relying on HTTPS)")
        paths.append(decompress(raw))
    return paths


def decompress(path):
    path = Path(path)
    with open(path, "rb") as f:
        gz = f.read(2) == b"\x1f\x8b"
    if not gz:
        return path
    out, total = path.with_suffix(".db"), 0
    with gzip.open(path, "rb") as src, open(out, "wb") as dst:
        while True:
            block = src.read(1 << 20)
            if not block:
                break
            total += len(block)
            if total > MAX_DECODED:
                die("snapshot decompresses to more than 2 GB; refusing")
            dst.write(block)
    return out


# ---------------------------------------------------------------- reading climbs
def read_climbs(db_paths, board_type, layout_id):
    """Returns {uuid: (name, frames)} and a list of (path, sql, extra_params) stats queries."""
    climbs, stat_queries = {}, []
    for path in db_paths:
        conn = open_ro(path)
        have = tables(conn)
        ctable = pick(have, "board_climbs", "climbs")
        if ctable:
            c = columns(conn, ctable)
            uid, name, frames = pick(c, "uuid", "climb_uuid"), pick(c, "name", "climb_name"), pick(c, "frames")
            if not (uid and name and frames):
                die(f"{ctable} has unexpected columns: {sorted(c)}")
            where, params = [], []
            if "board_type" in c:
                where.append("board_type = ?"); params.append(board_type)
            if "layout_id" in c:
                where.append("layout_id = ?"); params.append(layout_id)
            if "is_listed" in c:
                where.append("COALESCE(is_listed, 1) = 1")
            if "is_draft" in c:
                where.append("COALESCE(is_draft, 0) = 0")
            sql = f'SELECT "{uid}", "{name}", "{frames}" FROM "{ctable}"' + (f" WHERE {' AND '.join(where)}" if where else "")
            for u, n, f in conn.execute(sql, params):
                climbs[u] = (n, f)
        stable = pick(have, "board_climb_stats", "climb_stats")
        if stable:
            c = columns(conn, stable)
            ref, angle = pick(c, "climb_uuid", "uuid"), pick(c, "angle")  # angle is required
            disp = pick(c, "display_difficulty", "difficulty_average")
            bench = pick(c, "benchmark_difficulty")
            sends = pick(c, "ascensionist_count", "ascent_count", "ascents")
            quality = pick(c, "quality_average", "quality")
            if not (ref and angle and disp):
                die(f"{stable} has unexpected columns: {sorted(c)}")
            diff = f'COALESCE("{bench}", "{disp}")' if bench else f'"{disp}"'
            cols = ", ".join([f'"{ref}"', f'"{angle}"', diff, f'"{sends}"' if sends else "0",
                              f'"{quality}"' if quality else "NULL"])
            where, extra = ["1 = 1"], []
            if "board_type" in c:
                where.append("board_type = ?"); extra.append(board_type)
            stat_queries.append((path, f'SELECT {cols} FROM "{stable}" WHERE {" AND ".join(where)}', extra))
    return climbs, stat_queries


MAX_ANGLES = 16


def build_records(board, climbs, stat_queries):
    """Returns (records, angles, outside). Each record carries a grade for every angle."""
    led_of = board["leds"]
    per_climb = {}  # uuid -> {angle: (difficulty, sends, quality)}
    for path, sql, extra in stat_queries:
        for uuid, angle, diff, sends, quality in open_ro(path).execute(sql, extra):
            a = _as_int(angle)
            if a is not None and 0 <= a <= 90:
                per_climb.setdefault(uuid, {})[a] = (diff, sends or 0, quality)

    matched, outside = [], 0
    for uuid, (name, frames) in climbs.items():
        tokens = FRAME_TOKEN.findall((frames or "").split(",")[0])
        if not tokens:
            continue
        positions = [led_of.get(int(p)) for p, _ in tokens]
        if any(p is None for p in positions):
            outside += 1
            continue
        matched.append((hash_positions(positions), ascii_text(name, MAX_NAME) or "Untitled", per_climb.get(uuid, {})))

    # Angles that actually have stats; keep the most-used ones if there are too many.
    use = {}
    for _, _, st in matched:
        for a, (_, sends, _) in st.items():
            use[a] = use.get(a, 0) + 1 + int(sends)
    angles = sorted(sorted(use, key=lambda a: -use[a])[:MAX_ANGLES]) or [board["angle"]]

    best = {}
    for key, name, st in matched:
        cells, total = [], 0
        for a in angles:
            diff, sends, quality = st.get(a, (None, 0, None))
            d = int(math.floor(diff + 0.5)) if isinstance(diff, (int, float)) else 0
            q = int(round(quality * 10)) if isinstance(quality, (int, float)) else 0
            cells.append((max(0, min(d, 255)), max(0, min(q, 255)), min(int(sends), 65535)))
            total += int(sends)
        if key not in best or total > best[key][3]:
            best[key] = (key, name, cells, total)  # identical hold sets: keep the most repeated
    return sorted(best.values()), angles, outside


# ---------------------------------------------------------------- output
def pack(board, records, angles, built):
    """climbs.bin format 2 (see firmware climb_table.h)."""
    grade_count = min(64, max([0] + list(board["grades"]) + [c[0] for r in records for c in r[2]]) + 1)
    names, offsets = bytearray(), []
    for r in records:
        offsets.append(len(names))
        names += r[1].encode("ascii") + b"\0"
    default = board["angle"] if board["angle"] in angles else angles[len(angles) // 2]
    head = struct.pack("<4sHHIIIHH", MAGIC, FORMAT_VERSION, default, len(records), len(names),
                       int(built), board["size_id"], grade_count)
    head += board["wall"].encode("ascii")[:WALL_LEN - 1].ljust(WALL_LEN, b"\0")
    head += bytes([len(angles)]) + bytes(angles).ljust(MAX_ANGLES - 1, b"\0")
    assert len(head) == 80
    grades = b"".join(ascii_text(board["grades"].get(d, ""), GRADE_LEN - 1).encode("ascii").ljust(GRADE_LEN, b"\0")
                      for d in range(grade_count))
    recs = bytearray()
    for r, off in zip(records, offsets):
        recs += struct.pack("<QI", r[0], off)
        for d, q, n in r[2]:
            recs += struct.pack("<BBH", d if d < grade_count else 0, q, n)
    return head + grades + bytes(recs) + bytes(names)


def write_site(out_dir, blob, count, built):
    out = Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)
    digest = hashlib.sha256(blob).hexdigest()
    (out / "climbs.bin").write_bytes(blob)
    stamp = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(built))
    (out / "climbs.txt").write_text(f"version={FORMAT_VERSION}\nsize={len(blob)}\nsha256={digest}\n"
                                    f"count={count}\nbuilt={stamp}\n")
    commit = (COMMIT_MAGIC + struct.pack("<I", len(blob)) + bytes.fromhex(digest)).ljust(SECTOR, b"\xff")
    (out / "climbs_flash.bin").write_bytes(commit + blob)  # for flashing over USB
    (out / "index.html").write_text("<p>Kilter LCD climb list: climbs.txt / climbs.bin</p>\n")
    return digest


def cmd_build(args):
    board = load_board(args.board)
    with tempfile.TemporaryDirectory() as tmp:
        if args.snapshot:
            paths = [decompress(shutil.copy(p, Path(tmp) / f"local{i}.bin")) for i, p in enumerate(args.snapshot)]
        else:
            manifests = [args.manifest] if args.manifest else DEFAULT_MANIFESTS
            paths = download_snapshots(manifests, board["board_type"], board["layout_id"], tmp)
        climbs, stat_queries = read_climbs(paths, board["board_type"], board["layout_id"])
        if not climbs:
            die("no climbs table found in the snapshot files")
        if not stat_queries:
            print("warning: no stats table found, so grades will be blank")
        records, angles, outside = build_records(board, climbs, stat_queries)
    if len(records) < 100 and not args.allow_small:
        die(f"only {len(records)} climbs matched your wall; refusing to publish (use --allow-small to override)")
    built = int(time.time())
    blob = pack(board, records, angles, built)
    if len(blob) > 4 * 1024 * 1024 - SECTOR:
        die(f"climb list is {len(blob) / 1e6:.2f} MB, more than the ESP32's 4 MB slot")
    digest = write_site(args.out, blob, len(records), built)
    graded = sum(1 for r in records if any(c[0] for c in r[2]))
    print(f"{board['wall']}: {len(records):,} climbs ({graded:,} graded at one or more angles), "
          f"{outside:,} skipped (holds outside your wall)")
    print("angles: " + ", ".join(str(a) for a in angles))
    print(f"climbs.bin {len(blob) / 1e6:.2f} MB, sha256 {digest[:16]}...")


def cmd_inspect(args):
    base, manifest = load_manifest([args.manifest] if args.manifest else DEFAULT_MANIFESTS)
    found = find_artifacts(manifest)
    print(f"Manifest: {base}\nTop-level keys: {list(manifest)[:20] if isinstance(manifest, dict) else type(manifest).__name__}")
    for a in found:
        print(f"  board={a['board']!s:<10} layout={a['layout']!s:<4} sha={'yes' if a['sha256'] else 'no ':<3} {a['ref']}")
    chosen = choose_artifacts(found, args.board_type, args.layout_id, base)
    print(f"\n`build` would download for {args.board_type} layout {args.layout_id}:")
    for a in chosen:
        print("  " + a["url"])
    if not chosen:
        print("  nothing - download the right file by hand and use `build --snapshot FILE`")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("ledmap", help="save your wall's LED map from kilter.db")
    p.add_argument("database")
    p.add_argument("--list-sizes", action="store_true")
    p.add_argument("--size-id", type=int)
    p.add_argument("--layout-id", type=int)
    p.add_argument("--angle", type=int, default=40, choices=range(0, 91), metavar="0-90")
    p.add_argument("-o", "--out", default="board.json")
    p.set_defaults(func=cmd_ledmap)
    p = sub.add_parser("build", help="build climbs.bin from the latest snapshot")
    p.add_argument("--board", default="board.json")
    p.add_argument("--out", default="site")
    p.add_argument("--manifest", help="override the Boardsesh manifest URL")
    p.add_argument("--snapshot", nargs="+", help="use local snapshot/database file(s) instead of downloading")
    p.add_argument("--allow-small", action="store_true")
    p.set_defaults(func=cmd_build)
    p = sub.add_parser("inspect", help="show what the Boardsesh manifest offers")
    p.add_argument("--manifest")
    p.add_argument("--board-type", default="kilter")
    p.add_argument("--layout-id", type=int, default=8)
    p.set_defaults(func=cmd_inspect)
    args = ap.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
