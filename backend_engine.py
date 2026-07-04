"""
backend_engine.py
──────────────────────────────────────────────────────────────────────────
"Haqiqiy backend" qo'shimchasi — server.py (SrvManager) uchun.

Bu modul ALOHIDA fayl sifatida ishlaydi va asosiy server.py ga faqat 2 qator
bilan ulanadi (pastdagi INTEGRATSIYA.md ga qarang). Bu ataylab qilingan:
3000+ qatorlik asosiy faylni qo'lda qayta yozish xavfli (xato qilish oson);
alohida modul esa mustaqil tekshirish/testlash imkonini beradi.

NIMA QILADI:
  • Har loyiha uchun foydalanuvchi Python "handler" funksiyalarini
    (marshrutlarni) saqlaydi va so'rov kelganda ularni ISHGA TUSHIRADI.
  • Har loyiha o'zining ALOHIDA, jismonan ajratilgan SQLite bazasiga ega
    (asosiy server_data.db bilan hech qachon aralashmaydi).
  • Ijro RestrictedPython bilan cheklangan muhitda, ALOHIDA PROTSESSDA
    (multiprocessing) va QATIY VAQT/XOTIRA CHEGARASI bilan bajariladi —
    cheksiz sikl yozilgan kod ham serverni band qilib qo'ymaydi.
  • Rate-limit va audit-log bilan.

XAVFSIZLIK ESLATMASI (majburiy o'qing):
  RestrictedPython 100% "qochib bo'lmas" qamoq emas. Bu yerdagi choralar
  shaxsiy/kichik-jamoa loyihalari uchun oqilona minimal himoya beradi.
  Ochiq internetga (ngrok/global) chiqarilgan, ko'p-foydalanuvchili muhitda
  jiddiy foydalanish uchun bu funksiyani ALBATTA konteyner (Docker+gVisor
  yoki Firecracker) ichida qayta ishga tushirish bilan mustahkamlang.
"""

import os
import re
import sys
import json
import time
import sqlite3
import traceback
import multiprocessing as mp
from pathlib import Path
from datetime import datetime, timedelta
from functools import wraps

# ── RestrictedPython — ixtiyoriy bog'liqlik ────────────────────────────────
try:
    from RestrictedPython import compile_restricted, safe_globals
    from RestrictedPython.Guards import (
        safe_builtins, guarded_iter_unpack_sequence, full_write_guard,
    )
    from RestrictedPython.Eval import default_guarded_getiter
    RESTRICTED_OK = True
except ImportError:
    RESTRICTED_OK = False

# ╔══════════════════════════════════════════════════════════════════════╗
# ║                          SOZLAMALAR                                   ║
# ╚══════════════════════════════════════════════════════════════════════╝
EXEC_TIMEOUT_SEC   = 3          # bir chaqiruv uchun maksimal ijro vaqti
MEM_LIMIT_MB       = 128        # protsess uchun taxminiy xotira chegarasi (Linux)
RATE_LIMIT_PER_MIN = 30         # foydalanuvchi/loyiha uchun daqiqasiga chaqiruv
HISTORY_LOG_KEEP   = 500        # backend_exec_logs jadvalida saqlanadigan maksimal yozuv

PROJECT_DB_DIR = Path("project_dbs")
PROJECT_DB_DIR.mkdir(exist_ok=True)

# Foydalanuvchi kodi ichida "import X" ga ruxsat etilgan modullar RO'YXATI.
# Boshqa hamma narsa (os, sys, socket, subprocess, shutil, ctypes, ...) taqiqlangan.
ALLOWED_IMPORTS = {"json", "math", "random", "re", "datetime", "string", "statistics"}

# SQL darajasida taqiqlangan kalit so'zlar (xavfli buyruqlar / ko'p-statement)
_SQL_FORBIDDEN = re.compile(
    r"\b(ATTACH|DETACH|PRAGMA|VACUUM|DROP\s+DATABASE|LOAD_EXTENSION)\b", re.I)


# ╔══════════════════════════════════════════════════════════════════════╗
# ║                    DB SXEMASI (asosiy bazaga qo'shiladi)              ║
# ╚══════════════════════════════════════════════════════════════════════╝
def setup_backend_tables(db_exec, ensure_column):
    """server.py ning setup_db() ichidan chaqiriladi."""
    stmts = [
        """CREATE TABLE IF NOT EXISTS project_backend_routes (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            project_id INTEGER NOT NULL,
            path TEXT NOT NULL,
            method TEXT DEFAULT 'GET',
            code TEXT NOT NULL,
            updated_at TEXT DEFAULT (datetime('now')),
            UNIQUE(project_id, path, method))""",

        """CREATE TABLE IF NOT EXISTS backend_exec_logs (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            project_id INTEGER,
            user_id INTEGER,
            path TEXT,
            duration_ms INTEGER,
            ok INTEGER,
            error TEXT,
            created_at TEXT DEFAULT (datetime('now')))""",

        """CREATE TABLE IF NOT EXISTS backend_rate_limit (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            called_at TEXT DEFAULT (datetime('now')))""",
    ]
    for s in stmts:
        db_exec(s, fetch=False)
    ensure_column("projects", "backend_enabled", "INTEGER DEFAULT 0")


# ╔══════════════════════════════════════════════════════════════════════╗
# ║              HAR LOYIHA UCHUN AJRATILGAN SQL BAZASI                   ║
# ╚══════════════════════════════════════════════════════════════════════╝
def project_db_path(puuid: str) -> Path:
    # UUID formatini tekshirib, path-traversal imkoniyatini butunlay yo'q qilamiz
    safe = re.sub(r"[^a-zA-Z0-9-]", "", puuid)
    return PROJECT_DB_DIR / f"{safe}.db"


def ensure_project_db(puuid: str):
    p = project_db_path(puuid)
    if not p.exists():
        conn = sqlite3.connect(str(p))
        conn.close()
    return p


class SafeDB:
    """Foydalanuvchi kodiga beriladigan yagona SQL interfeysi.
    Xom sqlite3.Connection HECH QACHON foydalanuvchi kodiga uzatilmaydi —
    faqat quyidagi 3 ta metod orqali cheklangan kirish beriladi."""

    def __init__(self, db_path):
        self._conn = sqlite3.connect(str(db_path), timeout=5)
        self._conn.row_factory = sqlite3.Row
        self._cur = self._conn.cursor()

    def _check(self, sql):
        if ";" in sql.strip().rstrip(";"):
            raise ValueError("Bir chaqiruvda faqat bitta SQL buyrug'iga ruxsat")
        if _SQL_FORBIDDEN.search(sql):
            raise ValueError("Bu SQL buyrug'i taqiqlangan")

    def execute(self, sql, params=()):
        self._check(sql)
        self._cur.execute(sql, tuple(params))
        return self

    def fetchone(self):
        r = self._cur.fetchone()
        return dict(r) if r else None

    def fetchall(self):
        return [dict(r) for r in self._cur.fetchall()]

    def commit(self):
        self._conn.commit()

    def close(self):
        try:
            self._conn.commit()
            self._conn.close()
        except Exception:
            pass


# ╔══════════════════════════════════════════════════════════════════════╗
# ║           CHEKLANGAN IJRO MUHITI (RestrictedPython asosida)           ║
# ╚══════════════════════════════════════════════════════════════════════╝
def _guarded_import(name, *args, **kwargs):
    root = name.split(".")[0]
    if root not in ALLOWED_IMPORTS:
        raise ImportError(f"'{name}' moduliga ruxsat yo'q (whitelist: {sorted(ALLOWED_IMPORTS)})")
    return __import__(name, *args, **kwargs)


def _build_restricted_globals():
    g = dict(safe_globals)
    g["__builtins__"] = dict(safe_builtins)
    g["__builtins__"]["__import__"] = _guarded_import
    g["_getiter_"] = default_guarded_getiter
    g["_iter_unpack_sequence_"] = guarded_iter_unpack_sequence
    g["_write_"] = full_write_guard
    # Foydali, xavfsiz qo'shimcha builtin'lar:
    for name in ("len", "range", "enumerate", "zip", "sorted", "min", "max",
                 "sum", "abs", "round", "isinstance", "str", "int", "float",
                 "bool", "list", "dict", "set", "tuple"):
        g["__builtins__"][name] = __builtins__[name] if isinstance(__builtins__, dict) else getattr(__builtins__, name)
    return g


def compile_user_code(code_str):
    """Foydalanuvchi kodini kompilyatsiya qiladi. Kodda albatta
    `def handler(request_json, db): ...` funksiyasi bo'lishi shart."""
    if not RESTRICTED_OK:
        raise RuntimeError("RestrictedPython o'rnatilmagan: pip install RestrictedPython")
    byte_code = compile_restricted(code_str, filename="<backend-handler>", mode="exec")
    return byte_code


def _child_worker(conn, code_str, request_json, db_path):
    """ALOHIDA PROTSESSDA ishlaydi. Natijani `conn` (multiprocessing.Pipe) orqali qaytaradi."""
    # Linuxda qo'shimcha xotira/CPU chegarasi (mavjud bo'lsa)
    try:
        import resource
        resource.setrlimit(resource.RLIMIT_CPU, (EXEC_TIMEOUT_SEC + 1, EXEC_TIMEOUT_SEC + 1))
        resource.setrlimit(resource.RLIMIT_AS, (MEM_LIMIT_MB * 1024 * 1024, MEM_LIMIT_MB * 1024 * 1024))
    except Exception:
        pass  # Windows yoki resource moduli yo'q — davom etamiz (kamroq himoya bilan)

    db = None
    try:
        byte_code = compile_user_code(code_str)
        ns = _build_restricted_globals()
        exec(byte_code, ns)
        handler = ns.get("handler")
        if not callable(handler):
            raise ValueError("Kodda `def handler(request_json, db):` funksiyasi topilmadi")
        db = SafeDB(db_path)
        result = handler(request_json, db)
        json.dumps(result)  # JSON-serializable ekanini oldindan tekshiramiz
        conn.send({"ok": True, "result": result})
    except Exception as e:
        conn.send({"ok": False, "error": f"{type(e).__name__}: {e}"})
    finally:
        if db:
            db.close()
        conn.close()


def run_user_backend(code_str, request_json, db_path, timeout=EXEC_TIMEOUT_SEC):
    """Foydalanuvchi kodini ALOHIDA protsessda, vaqt chegarasi bilan ishga tushiradi.
    Qaytaradi: (ok: bool, payload: dict|str, duration_ms: int)"""
    t0 = time.time()
    parent_conn, child_conn = mp.Pipe()
    proc = mp.Process(target=_child_worker, args=(child_conn, code_str, request_json, str(db_path)))
    proc.start()
    proc.join(timeout)
    duration_ms = int((time.time() - t0) * 1000)

    if proc.is_alive():
        proc.terminate()
        proc.join(1)
        if proc.is_alive():
            proc.kill()
        return False, f"Vaqt tugadi ({timeout}s ichida yakunlanmadi — cheksiz sikl bo'lishi mumkin)", duration_ms

    if parent_conn.poll():
        data = parent_conn.recv()
        if data.get("ok"):
            return True, data.get("result"), duration_ms
        return False, data.get("error", "Noma'lum xato"), duration_ms

    return False, "Protsessdan javob kelmadi (kutilmagan xato)", duration_ms


# ╔══════════════════════════════════════════════════════════════════════╗
# ║                          RATE-LIMIT                                   ║
# ╚══════════════════════════════════════════════════════════════════════╝
def check_rate_limit(db_exec, q1, user_id):
    cutoff = (datetime.now() - timedelta(minutes=1)).strftime("%Y-%m-%d %H:%M:%S")
    row = q1("SELECT COUNT(*) c FROM backend_rate_limit WHERE user_id=? AND called_at>?", (user_id, cutoff))
    if row and row["c"] >= RATE_LIMIT_PER_MIN:
        return False
    db_exec("INSERT INTO backend_rate_limit (user_id) VALUES (?)", (user_id,), fetch=False)
    return True


def log_exec(db_exec, project_id, user_id, path, duration_ms, ok, error=""):
    db_exec("INSERT INTO backend_exec_logs (project_id,user_id,path,duration_ms,ok,error) VALUES (?,?,?,?,?,?)",
            (project_id, user_id, path, duration_ms, 1 if ok else 0, (error or "")[:500]), fetch=False)
    old = db_exec("SELECT id FROM backend_exec_logs ORDER BY id DESC LIMIT -1 OFFSET ?", (HISTORY_LOG_KEEP,)) or []
    for r in old:
        db_exec("DELETE FROM backend_exec_logs WHERE id=?", (r["id"],), fetch=False)


# ╔══════════════════════════════════════════════════════════════════════╗
# ║      MARSHRUTLARNI RO'YXATDAN O'TKAZISH — server.py dan chaqiriladi   ║
# ╚══════════════════════════════════════════════════════════════════════╝
def register_backend(app, ctx):
    """
    ctx quyidagi kalitlarni o'z ichiga olishi shart (barchasi server.py dan):
      db_exec, q1, get_setting, set_setting, session, request, jsonify,
      abort, redirect, role_rank, ROLE_RANK, user_req, admin_req, write_req,
      csrf_field, mode_on, get_ip, pg  (ya'ni _pg funksiyasi)
    """
    db_exec, q1 = ctx["db_exec"], ctx["q1"]
    get_setting, set_setting = ctx["get_setting"], ctx["set_setting"]
    session, request, jsonify = ctx["session"], ctx["request"], ctx["jsonify"]
    abort, redirect = ctx["abort"], ctx["redirect"]
    role_rank, ROLE_RANK = ctx["role_rank"], ctx["ROLE_RANK"]
    user_req, admin_req, write_req = ctx["user_req"], ctx["admin_req"], ctx["write_req"]
    csrf_field, mode_on, pg = ctx["csrf_field"], ctx["mode_on"], ctx["pg"]

    def backend_globally_enabled():
        return RESTRICTED_OK and get_setting("backend_enabled", "0") == "1"

    def project_or_403(puuid, need_write=False):
        proj = q1("SELECT * FROM projects WHERE uuid=?", (puuid,))
        if not proj:
            abort(404)
        is_owner = proj["owner_id"] == session.get("user_id")
        if not is_owner and not session.get("admin"):
            abort(403)
        if need_write and role_rank(session.get("role")) < ROLE_RANK["user"]:
            abort(403)
        return proj

    # ── Admin: global yoqish/o'chirish + loglar ─────────────────────────
    @app.route("/admin/backend/toggle", methods=["POST"])
    @admin_req
    def backend_admin_toggle():
        if not RESTRICTED_OK:
            return redirect(request.referrer or "/admin/settings")
        cur = get_setting("backend_enabled", "0")
        set_setting("backend_enabled", "0" if cur == "1" else "1")
        return redirect(request.referrer or "/admin/settings")

    @app.route("/admin/backend/logs")
    @admin_req
    def backend_admin_logs():
        rows = db_exec("""SELECT l.*, p.name as pname, u.username FROM backend_exec_logs l
                           LEFT JOIN projects p ON l.project_id=p.id
                           LEFT JOIN users u ON l.user_id=u.id
                           ORDER BY l.id DESC LIMIT 200""") or []
        tr = "".join(f"""<tr>
          <td>{r.get('pname') or '—'}</td><td>{r.get('username') or '—'}</td>
          <td><code style="font-size:.72rem">{r['path']}</code></td>
          <td>{r['duration_ms']} ms</td>
          <td><span class="bx {'xg' if r['ok'] else 'xr'}">{'OK' if r['ok'] else 'Xato'}</span></td>
          <td class="tm" style="font-size:.72rem">{(r.get('error') or '')[:80]}</td>
          <td class="tm" style="font-size:.72rem">{str(r['created_at'])[:19]}</td>
        </tr>""" for r in rows)
        status = ("✅ RestrictedPython o'rnatilgan" if RESTRICTED_OK
                  else "⚠️ RestrictedPython O'RNATILMAGAN — pip install RestrictedPython (backend rejimi ishlamaydi)")
        on = get_setting("backend_enabled", "0") == "1"
        body = f"""
        <div class="fl mb"><h2 style="color:#fff">🐍 Backend — ijro loglari</h2>
          <span class="bx {'xg' if RESTRICTED_OK else 'xr'} mla">{status}</span></div>
        <form method="POST" action="/admin/backend/toggle" class="mb">{csrf_field()}
          <button class="btn {'br' if on else 'bg'} bsm" {'' if RESTRICTED_OK else 'disabled'}>
            {"🔴 Global backendni o'chirish" if on else "🟢 Global backendni yoqish"}</button>
        </form>
        <div class="card" style="padding:0"><div class="tw">
          <table><thead><tr><th>Loyiha</th><th>Foydalanuvchi</th><th>Yo'l</th><th>Vaqt</th>
          <th>Holat</th><th>Xato</th><th>Vaqt belgisi</th></tr></thead>
          <tbody>{tr or "<tr><td colspan=7 style='text-align:center;color:var(--mt);padding:16px'>Hali chaqiruv yo'q</td></tr>"}</tbody></table>
        </div></div>"""
        return pg("Backend loglari", body, "backend")

    # ── Loyiha egasi: o'z loyihasi uchun backendni yoqish ───────────────
    @app.route("/projects/<puuid>/backend/toggle", methods=["POST"])
    @user_req
    @write_req
    def backend_project_toggle(puuid):
        proj = project_or_403(puuid, need_write=True)
        if not backend_globally_enabled():
            abort(403)
        new_val = 0 if proj.get("backend_enabled") else 1
        db_exec("UPDATE projects SET backend_enabled=? WHERE id=?", (new_val, proj["id"]), fetch=False)
        if new_val:
            ensure_project_db(puuid)
        return redirect(request.referrer or "/projects")

    # ── Marshrutlar CRUD (muharrirdagi "Backend" tab shu bilan ishlaydi) ─
    @app.route("/editor/backend/routes/<puuid>", methods=["GET", "POST"])
    @user_req
    def backend_routes_list(puuid):
        proj = project_or_403(puuid)
        if request.method == "GET":
            rows = db_exec("SELECT id,path,method,updated_at FROM project_backend_routes WHERE project_id=? ORDER BY path",
                           (proj["id"],)) or []
            return jsonify({"routes": rows, "backend_enabled": bool(proj.get("backend_enabled")),
                             "global_enabled": backend_globally_enabled()})
        if role_rank(session.get("role")) < ROLE_RANK["user"]:
            return jsonify({"ok": False, "error": "Ruxsat yo'q"}), 403
        if not proj.get("backend_enabled"):
            return jsonify({"ok": False, "error": "Bu loyihada backend yoqilmagan"}), 403
        d = request.get_json() or {}
        path = "/" + (d.get("path") or "").strip().lstrip("/")
        method = (d.get("method") or "GET").upper()
        code = d.get("code", "")
        if method not in ("GET", "POST") or path == "/" or not code.strip():
            return jsonify({"ok": False, "error": "Noto'g'ri ma'lumot"}), 400
        db_exec("""INSERT INTO project_backend_routes (project_id,path,method,code) VALUES (?,?,?,?)
                   ON CONFLICT(project_id,path,method) DO UPDATE SET code=excluded.code, updated_at=datetime('now')""",
                (proj["id"], path, method, code), fetch=False)
        return jsonify({"ok": True})

    @app.route("/editor/backend/routes/<puuid>/<int:rid>", methods=["GET", "DELETE"])
    @user_req
    def backend_route_item(puuid, rid):
        proj = project_or_403(puuid)
        if request.method == "DELETE":
            if role_rank(session.get("role")) < ROLE_RANK["user"]:
                return jsonify({"ok": False}), 403
            db_exec("DELETE FROM project_backend_routes WHERE id=? AND project_id=?", (rid, proj["id"]), fetch=False)
            return jsonify({"ok": True})
        row = q1("SELECT * FROM project_backend_routes WHERE id=? AND project_id=?", (rid, proj["id"]))
        if not row:
            abort(404)
        return jsonify({"route": row})

    @app.route("/editor/backend/test/<puuid>/<int:rid>", methods=["POST"])
    @user_req
    @write_req
    def backend_route_test(puuid, rid):
        proj = project_or_403(puuid, need_write=True)
        row = q1("SELECT * FROM project_backend_routes WHERE id=? AND project_id=?", (rid, proj["id"]))
        if not row:
            abort(404)
        if not backend_globally_enabled():
            return jsonify({"ok": False, "error": "Backend global o'chirilgan"}), 403
        test_input = (request.get_json() or {}).get("input", {})
        db_path = ensure_project_db(puuid)
        ok, payload, dur = run_user_backend(row["code"], test_input, db_path)
        log_exec(db_exec, proj["id"], session["user_id"], f"[TEST]{row['path']}", dur, ok, "" if ok else str(payload))
        return jsonify({"ok": ok, "result": payload if ok else None, "error": None if ok else payload, "duration_ms": dur})

    # ── OMMAVIY IJRO ENDPOINTI — loyihaning frontend fetch() lari shu yerga chaqiradi ──
    @app.route("/api/backend/<puuid>/<path:route_path>", methods=["GET", "POST"])
    def backend_run(puuid, route_path):
        if not backend_globally_enabled():
            abort(403)
        # Guest yoki "global" (ngrok) rejimda backend ijrosi TAQIQLANADI:
        if session.get("_guest"):
            abort(403)
        if mode_on("global"):
            abort(403)
        if "user_id" not in session:
            abort(401)
        proj = q1("SELECT * FROM projects WHERE uuid=?", (puuid,))
        if not proj or not proj.get("backend_enabled"):
            abort(404)
        path = "/" + route_path.lstrip("/")
        row = q1("SELECT * FROM project_backend_routes WHERE project_id=? AND path=? AND method=?",
                 (proj["id"], path, request.method))
        if not row:
            abort(404)
        if not check_rate_limit(db_exec, q1, session["user_id"]):
            return jsonify({"error": f"Juda ko'p so'rov. Daqiqasiga maksimal {RATE_LIMIT_PER_MIN} marta chaqiring."}), 429
        payload_in = request.get_json(silent=True) or dict(request.args)
        db_path = ensure_project_db(puuid)
        ok, payload, dur = run_user_backend(row["code"], payload_in, db_path)
        log_exec(db_exec, proj["id"], session["user_id"], path, dur, ok, "" if ok else str(payload))
        if ok:
            return jsonify(payload)
        return jsonify({"error": payload}), 400
