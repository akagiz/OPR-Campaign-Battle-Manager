#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
===============================================================================
 OPR Campaign & Battle Manager  v5
 Gestor de campañas y tableros para One Page Rules / for One Page Rules
===============================================================================
 Requisitos / Requirements : Python 3.8+  and  pygame 2.x  (pip install pygame)
 Ejecución / Run           : python opr_campaign_manager.py

 ES  · Pestañas: 1 Mapa de campaña · 2 Generador de batalla · 3 Facciones/Recursos
     · F11: pantalla completa · botones ES/EN: idioma · Ctrl+S: guardar
     · Ctrl+L: archivos de campaña (carpeta «campaign/»)
     · Recursos: CR (campaña, sirven para construir) y RR (reclutamiento).
     · Construir exige territorio ocupado y descuenta el coste a su facción.
     · Facciones > «Ejército»: listas de ejército editables; importación desde
       Army Forge (texto exportado, enlace compartido/ID, archivo de texto/JSON).
     · Batalla: pestañas Terreno / Despliegue (6 estilos OPR) / Reglas
       (condiciones geológicas y misteriosas + reglas por tipo de terreno o pieza).
     · v4: logística y rutas, fuerzas móviles en el mapa, XP y avances de unidades,
       historial de combates por territorio y perfiles de sistemas OPR.
     · v5: un ejército independiente por fuerza, catálogo OPR local (Army Forge con caché
       en «opr_db/»), economía austera, reclutamiento en Cuartel/Fortaleza, mantenimiento,
       rutas dinámicas, edificios locales y varias campañas simultáneas «[Tipo] nombre».
 EN  · Tabs: 1 Campaign map · 2 Battle generator · 3 Factions/Resources
     · F11: fullscreen · ES/EN buttons: language · Ctrl+S: save
     · Ctrl+L: campaign files ("campaign/" folder)
     · Resources: CR (campaign, used to build) and RR (recruitment).
     · Building requires an occupied territory and charges its faction.
     · Factions > "Army": editable army lists; import from Army Forge
       (exported text, shared link/ID, text/JSON file).

 Batalla / Battle : arrastrar/drag = mover/move · clic der./right-click = borrar/delete
                    R = rotar/rotate · Supr/Del = borrar/delete · G = generar/generate
 Steppers         : SHIFT = ±5      Text fields: Ctrl+V pega / pastes
===============================================================================
"""

import json
import math
import os
import random
import re
import subprocess
import sys
import threading
import time
import urllib.parse
import urllib.request
from dataclasses import dataclass, field, asdict, fields
from typing import Dict, List, Optional, Tuple

import pygame

# =============================================================================
#  CONSTANTES GENERALES
# =============================================================================
WIN_W, WIN_H = 1280, 720
FPS = 60
TOPBAR_H = 48
STATUS_H = 24

try:
    BASE_DIR = os.path.dirname(os.path.abspath(__file__))
except NameError:  # intérprete interactivo
    BASE_DIR = os.getcwd()
CAMPAIGN_DIR = os.path.join(BASE_DIR, "campaign")      # partidas guardadas
EXPORT_DIR = os.path.join(BASE_DIR, "exports")         # exportaciones de batalla
SETTINGS_FILE = os.path.join(BASE_DIR, "opr_settings.json")

ARMY_FORGE_API = "https://army-forge.onepagerules.com/api/tts?id="

# Ingresos base por territorio ocupado
START_CR = 10               # recursos de campaña iniciales
START_RR = 15               # recursos de reclutamiento iniciales
BASE_RR = 1                 # RR por territorio abastecido y turno
# CR base: max(1, territorios_abastecidos // 2) -> la expansión sola casi no financia nada
FORCE_COST_CR = 6           # crear un ejército nuevo (aparece en la base principal)
ROUTE_COST_CR = 5           # construir una ruta entre dos territorios propios
UPKEEP_PTS_PER_CR = 200     # mantenimiento: ceil(puntos / 200) CR por unidad activa y turno
RECRUIT_BUILDINGS = ("barracks", "fortress")   # edificios que permiten reclutar
STATUSES = ("active", "reserve", "fallen", "destroyed")

# Paleta de la interfaz
C_BG = (22, 25, 31)
C_PANEL = (33, 37, 46)
C_PANEL2 = (44, 49, 61)
C_LINE = (74, 82, 99)
C_TEXT = (232, 235, 242)
C_DIM = (152, 160, 176)
C_ACCENT = (236, 168, 52)
C_BTN = (58, 65, 81)
C_BTN_H = (80, 90, 110)
C_BTN_ON = (192, 130, 38)
C_BTN_OFF = (40, 44, 54)
C_GOOD = (96, 205, 126)
C_BAD = (226, 84, 84)
C_WARN = (232, 188, 56)

FACTION_COLORS = [
    (214, 64, 64), (66, 128, 224), (84, 184, 96), (232, 188, 56),
    (166, 96, 214), (230, 128, 52), (64, 196, 200), (220, 120, 170),
]
DEFAULT_FACTION_NAMES = {
    "es": ["Legión Carmesí", "Clan del Acero", "Enjambre Verde", "Pacto Dorado",
           "Orden Violeta", "Hijos del Fuego"],
    "en": ["Crimson Legion", "Steel Clan", "Green Swarm", "Golden Pact",
           "Violet Order", "Sons of Fire"],
}

# Edificios. cr/rr = ingreso por turno; rec = bajas recuperadas por turno;
# ini/df = bonus de iniciativa/defensa. cost_cr/cost_rr = coste de construcción.
BUILDINGS: Dict[str, dict] = {
    "barracks": dict(color=(200, 74, 74), rr=2, cost_cr=12, cost_rr=0),
    "hospital": dict(color=(88, 200, 140), rec=2, cost_cr=12, cost_rr=0),
    "workshop": dict(color=(210, 150, 70), cr=2, cost_cr=9, cost_rr=0),
    "market": dict(color=(230, 200, 80), cr=1, rr=1, cost_cr=10, cost_rr=0),
    "tower": dict(color=(120, 170, 230), ini=1, cost_cr=7, cost_rr=0),
    "fortress": dict(color=(170, 170, 184), df=1, cost_cr=16, cost_rr=3),
}
BONUS_KEYS = ("cr", "rr", "rec", "ini", "df")

# Fuerzas móviles por facción
MAX_FORCES = 4

# Rangos y avances de unidades: se alcanza un rango al llegar a su XP mínimo y cada rango
# superior al primero concede 1 punto de avance.
RANK_XP = [0, 3, 6, 10]
ADVANCES = ["quality", "defense", "attack", "furious", "fearless", "scout", "strider", "stealth"]
ADV_RULES = {"furious": "Furious", "fearless": "Fearless", "scout": "Scout",
             "strider": "Strider", "stealth": "Stealth"}
ADV_MAX = {"quality": 2, "defense": 2, "attack": 2}      # veces; las reglas solo una vez

# Perfiles de sistemas OPR. Valores de referencia EDITABLES:
#   pts = puntos por defecto, pct = máx. % de la lista por unidad (0 = sin límite),
#   per = 1 unidad por cada N pts (0 = sin límite), board = índice en BOARD_SIZES,
#   terrain = mínimo recomendado de piezas de terreno (0 = no ajustar).
SYS_ORDER = ["GEN", "GF", "GFF", "AoF", "AoFS", "AoFR", "GFW"]
SYSTEMS: Dict[str, dict] = {
    "GEN": dict(pts=0, pct=0, per=0, board=1, terrain=0),
    "GF": dict(pts=1000, pct=35, per=150, board=3, terrain=10),
    "GFF": dict(pts=300, pct=0, per=0, board=2, terrain=20),
    "AoF": dict(pts=1000, pct=35, per=150, board=3, terrain=10),
    "AoFS": dict(pts=300, pct=0, per=0, board=2, terrain=0),
    "AoFR": dict(pts=2000, pct=35, per=150, board=3, terrain=10),
    "GFW": dict(pts=1000, pct=0, per=0, board=3, terrain=0),
}
# Tipos de campaña y formato obligatorio de nombre: «[Gen|GF|GFF|AoF|AoFS|AoFR] nombre»
CAMPAIGN_TYPES = ["GEN", "GF", "GFF", "AoF", "AoFS", "AoFR"]
CAMPAIGN_TAGS = {"GEN": "Gen", "GF": "GF", "GFF": "GFF", "AoF": "AoF", "AoFS": "AoFS", "AoFR": "AoFR"}
_NAME_RE = re.compile(r"^\[(Gen|GF|GFF|AoF|AoFS|AoFR)\] (\S.*)$")

# Base de datos OPR local (caché de Army Forge)
OPR_DB_DIR = os.path.join(BASE_DIR, "opr_db")
AF_BASE = "https://army-forge.onepagerules.com"
SYSTEM_IDS = {"GF": 2, "GFF": 3, "AoF": 4, "AoFS": 5, "AoFR": 6}      # ids numéricos de la API
SYSTEM_SLUGS = {"GF": "gf", "GFF": "gff", "GFW": "gfw", "AoF": "aof", "AoFS": "aofs", "AoFR": "aofr"}
CATALOG_SYSTEMS = tuple(SYSTEM_SLUGS)

_SYS_ALIASES = {
    "gen": "GEN", "gf": "GF", "grimdarkfuture": "GF",
    "gff": "GFF", "firefight": "GFF", "grimdarkfuturefirefight": "GFF",
    "aof": "AoF", "ageoffantasy": "AoF",
    "aofs": "AoFS", "skirmish": "AoFS", "ageoffantasyskirmish": "AoFS",
    "aofr": "AoFR", "regiments": "AoFR", "ageoffantasyregiments": "AoFR",
    "gfw": "GFW", "warfleets": "GFW", "grimdarkfuturewarfleets": "GFW",
}

# Biomas (multiplicadores de terreno para la batalla)
BIOMES: List[dict] = [
    dict(color=(104, 126, 82),
         mult={"hill": 0.6, "forest": 0.5, "ruins": 0.5, "building": 0.4, "obstacle": 0.8,
               "marsh": 0.3, "crates": 0.6}),
    dict(color=(48, 98, 62),
         mult={"forest": 2.4, "hill": 0.8, "marsh": 0.8, "ruins": 0.5, "building": 0.3,
               "crates": 0.4}),
    dict(color=(110, 108, 112),
         mult={"ruins": 2.2, "building": 2.0, "obstacle": 1.5, "crates": 1.3, "forest": 0.3,
               "marsh": 0.2}),
    dict(color=(136, 112, 78),
         mult={"hill": 2.4, "forest": 0.8, "obstacle": 0.8, "building": 0.3, "marsh": 0.2}),
    dict(color=(72, 92, 66),
         mult={"marsh": 3.0, "forest": 1.3, "hill": 0.4, "building": 0.2, "ruins": 0.5}),
    dict(color=(124, 96, 80),
         mult={"crates": 2.4, "obstacle": 2.0, "building": 1.4, "ruins": 1.0, "forest": 0.2,
               "marsh": 0.2}),
]

NAME_PARTS = {
    "es": (["Cráter", "Valle", "Colina", "Paso", "Bastión", "Yermo", "Cuenca", "Meseta",
            "Ciénaga", "Puesto", "Sector", "Enclave", "Risco", "Nexo"],
           ["Ceniza", "Hierro", "Sombra", "Tormenta", "Ámbar", "Espectro", "Alba", "Cobre",
            "Niebla", "Basalto", "Lamento", "Fénix", "Obsidiana", "Escarcha"]),
    "en": (["Crater", "Valley", "Hill", "Pass", "Bastion", "Wasteland", "Basin", "Plateau",
            "Marsh", "Outpost", "Sector", "Enclave", "Ridge", "Nexus"],
           ["Ash", "Iron", "Shadow", "Storm", "Amber", "Spectre", "Dawn", "Copper",
            "Mist", "Basalt", "Lament", "Phoenix", "Obsidian", "Frost"]),
}

BOARD_SIZES = [(60, 60), (120, 60), (120, 120), (180, 120)]
MAX_TERRAIN_TYPES = 10
# Estilos de despliegue de OPR (orden de la tirada aleatoria de D6)
DEPLOY_TYPES = ["frontline", "side", "ambush", "spearhead", "flank", "cornered"]

# Catálogo de reglas especiales de terreno / condiciones del campo de batalla
RULE_CATS = {
    "cover": "core", "difficult": "core", "dangerous": "core", "sight": "core",
    "barrier": "effect", "vigor": "effect",
    "earthquake": "geo", "storm": "geo", "mud": "geo",
    "damnation": "myst", "arcane": "myst", "inspiration": "myst",
    "vortex": "myst", "fog": "myst", "echoes": "myst",
}
RULE_ORDER = list(RULE_CATS)
GEO_RULES = [k for k, c in RULE_CATS.items() if c == "geo"]
MYST_RULES = [k for k, c in RULE_CATS.items() if c == "myst"]
RULE_COLORS = {"core": (110, 118, 134), "effect": (70, 150, 205),
               "geo": (190, 130, 60), "myst": (156, 90, 200)}

BOARD_COL = (108, 122, 94)
BOARD_GRID = (96, 110, 84)

# =============================================================================
#  INTERNACIONALIZACIÓN  (ES / EN)   ·   T[clave] = (español, english)
# =============================================================================
LANG = "es"
LANGS = ("es", "en")

T: Dict[str, Tuple[str, str]] = {
    # --- aplicación / barra superior ---
    "tab.campaign": ("1 · Mapa de Campaña", "1 · Campaign Map"),
    "tab.battle": ("2 · Generador de Batalla", "2 · Battle Generator"),
    "tab.factions": ("3 · Facciones / Recursos", "3 · Factions / Resources"),
    "top.files": ("Archivos de campaña", "Campaign files"),
    "top.files_tip": ("Guardar y cargar campañas (carpeta «campaign»). Ctrl+L",
                      "Save and load campaigns (\"campaign\" folder). Ctrl+L"),
    "top.fs_on": ("Pantalla completa (F11)", "Fullscreen (F11)"),
    "top.fs_off": ("Salir de pantalla completa (F11)", "Exit fullscreen (F11)"),
    "top.lang_tip": ("Cambiar idioma", "Switch language"),
    "status.hint": ("1/2/3: pestañas · F11: pantalla completa · Ctrl+S: guardar · Ctrl+L: archivos",
                    "1/2/3: tabs · F11: fullscreen · Ctrl+S: save · Ctrl+L: files"),
    "status.saved": ("Guardado: {path}", "Saved: {path}"),
    "status.save_err": ("Error al guardar: {err}", "Save error: {err}"),
    "status.loaded": ("Campaña cargada: {name}", "Campaign loaded: {name}"),
    "status.load_err": ("No se pudo cargar: {err}", "Could not load: {err}"),
    "status.exported": ("Exportado en {path}", "Exported to {path}"),
    "status.export_err": ("Error al exportar: {err}", "Export error: {err}"),
    "status.turn_done": ("Turno {n} resuelto.", "Turn {n} resolved."),
    "status.battle_ready": ("Batalla preparada según el bioma del territorio.",
                            "Battle prepared according to the territory biome."),
    "status.built": ("{b} construido en {q} (-{cost}).", "{b} built in {q} (-{cost})."),
    # --- diálogo de archivos ---
    "dlg.title": ("ARCHIVOS DE CAMPAÑA", "CAMPAIGN FILES"),
    "dlg.folder": ("Carpeta: {path}", "Folder: {path}"),
    "dlg.name": ("Nombre de la campaña:", "Campaign name:"),
    "dlg.save": ("Guardar", "Save"),
    "dlg.save_tip": ("Guarda (o sobrescribe) «campaign/<nombre>.json»",
                     "Saves (or overwrites) \"campaign/<name>.json\""),
    "dlg.load": ("Cargar", "Load"),
    "dlg.close": ("Cerrar", "Close"),
    "dlg.empty": ("Todavía no hay campañas guardadas.", "No saved campaigns yet."),
    "dlg.saved_list": ("CAMPAÑAS GUARDADAS", "SAVED CAMPAIGNS"),
    "dlg.default_name": ("Campaña 1", "Campaign 1"),
    # --- mapa de campaña ---
    "camp.title": ("MAPA DE CAMPAÑA", "CAMPAIGN MAP"),
    "camp.grid": ("Cuadrícula:", "Grid:"),
    "camp.grid_tip": ("Cambia el tamaño y genera un mapa nuevo (se pierde el actual).",
                      "Changes the size and generates a new map (the current one is lost)."),
    "camp.generate": ("Generar mapa aleatorio", "Generate random map"),
    "camp.generate_tip": ("Nuevo mapa procedural; las facciones vuelven a sus posiciones de inicio.",
                          "New procedural map; factions return to their starting positions."),
    "camp.seed": ("Semilla: {n}", "Seed: {n}"),
    "camp.maxb": ("Máx. edificios/territorio:", "Max buildings/territory:"),
    "camp.maxb_tip": ("Límite de construcciones por territorio. «Sin límite» = sin huecos fijos.",
                      "Building limit per territory. \"No limit\" = no fixed slots."),
    "camp.unlimited": ("Sin límite", "No limit"),
    "camp.details": ("DETALLES DEL TERRITORIO", "TERRITORY DETAILS"),
    "camp.hint1": ("Haz clic en un territorio del mapa para", "Click a territory on the map to"),
    "camp.hint2": ("ver sus detalles y editarlo.", "see its details and edit it."),
    "camp.legend": ("Edificios (coste de construcción)", "Buildings (construction cost)"),
    "camp.biome": ("Bioma: {b}", "Biome: {b}"),
    "camp.occupied": ("OCUPADO por {f}", "OCCUPIED by {f}"),
    "camp.free": ("LIBRE", "FREE"),
    "camp.assign": ("Asignar a:", "Assign to:"),
    "camp.release": ("Liberar territorio", "Release territory"),
    "camp.buildings": ("EDIFICIOS ({n}{lim})", "BUILDINGS ({n}{lim})"),
    "camp.none_built": ("- sin edificios -", "- no buildings -"),
    "camp.demolish_tip": ("Clic para demoler (sin reembolso).", "Click to demolish (no refund)."),
    "camp.build": ("CONSTRUIR (paga la facción propietaria):", "BUILD (paid by the owner faction):"),
    "camp.need_owner": ("Ocupa el territorio para construir", "Occupy the territory to build"),
    "camp.bonus": ("Bonificación de edificios:", "Building bonus:"),
    "camp.none": ("ninguna", "none"),
    "camp.more": ("+{n} más", "+{n} more"),
    "camp.prepare": ("Preparar batalla en este territorio  >", "Prepare battle in this territory  >"),
    "camp.prepare_short": ("Preparar batalla >", "Prepare battle >"),
    "camp.prepare_tip": ("Ajusta el pool de terreno al bioma, genera el tablero y abre el generador.",
                         "Adjusts the terrain pool to the biome, generates the board and opens the generator."),
    "err.free": ("Solo se puede construir en territorios ocupados.",
                 "You can only build in occupied territories."),
    "err.full": ("El territorio alcanzó su límite de edificios.",
                 "The territory reached its building limit."),
    "err.funds": ("Recursos insuficientes: hacen falta {cost}.",
                  "Not enough resources: {cost} required."),
    "log.newmap": ("Nuevo mapa {n}x{n} (semilla {seed}).", "New {n}x{n} map (seed {seed})."),
    "log.turn": ("T{t} · {f}: +{cr} CR, +{rr} RR, recupera {rec}/{fallen} bajas.",
                 "T{t} · {f}: +{cr} CR, +{rr} RR, recovers {rec}/{fallen} casualties."),
    "log.build": ("T{t} · {f} construye {b} en {q} (-{cost}).",
                  "T{t} · {f} builds {b} in {q} (-{cost})."),
    "bonus.cr": ("CR", "CR"),
    "bonus.rr": ("RR", "RR"),
    "bonus.rec": ("Recup.", "Recov."),
    "bonus.ini": ("Inic.", "Init."),
    "bonus.df": ("Def.", "Def."),
    # --- edificios ---
    "b.barracks": ("Cuartel", "Barracks"),
    "b.barracks.d": ("+2 RR por turno", "+2 RR per turn"),
    "b.barracks.s": ("C", "B"),
    "b.hospital": ("Hospital", "Hospital"),
    "b.hospital.d": ("Recupera hasta 2 unidades caídas por turno",
                     "Recovers up to 2 fallen units per turn"),
    "b.hospital.s": ("H", "H"),
    "b.workshop": ("Taller", "Workshop"),
    "b.workshop.d": ("+2 CR por turno", "+2 CR per turn"),
    "b.workshop.s": ("T", "W"),
    "b.market": ("Mercado", "Market"),
    "b.market.d": ("+1 CR y +1 RR por turno", "+1 CR and +1 RR per turn"),
    "b.market.s": ("M", "M"),
    "b.tower": ("Torre vigía", "Watchtower"),
    "b.tower.d": ("+1 a la iniciativa/despliegue en batallas del territorio",
                  "+1 to initiative/deployment in battles in the territory"),
    "b.tower.s": ("V", "T"),
    "b.fortress": ("Fortaleza", "Fortress"),
    "b.fortress.d": ("+1 a la defensa de los defensores del territorio",
                     "+1 defense for the territory's defenders"),
    "b.fortress.s": ("F", "F"),
    # --- biomas ---
    "biome.0": ("Llanuras", "Plains"),
    "biome.1": ("Bosque denso", "Dense forest"),
    "biome.2": ("Ruinas urbanas", "Urban ruins"),
    "biome.3": ("Colinas", "Hills"),
    "biome.4": ("Pantanal", "Swamp"),
    "biome.5": ("Páramo industrial", "Industrial wasteland"),
    # --- terreno ---
    "terrain.hill": ("Colina", "Hill"),
    "terrain.hill.fx": ("Terreno elevado: mejor visión", "Elevated terrain: better sight"),
    "terrain.forest": ("Bosque", "Forest"),
    "terrain.forest.fx": ("Cobertura; terreno difícil", "Cover; difficult terrain"),
    "terrain.ruins": ("Ruinas", "Ruins"),
    "terrain.ruins.fx": ("Cobertura; bloquea LdV parcial", "Cover; partially blocks LoS"),
    "terrain.building": ("Edificio", "Building"),
    "terrain.building.fx": ("Bloquea línea de visión", "Blocks line of sight"),
    "terrain.obstacle": ("Obstáculo / Muro", "Obstacle / Wall"),
    "terrain.obstacle.fx": ("Cobertura lineal", "Linear cover"),
    "terrain.marsh": ("Pantano", "Swamp"),
    "terrain.marsh.fx": ("Terreno peligroso", "Dangerous terrain"),
    "terrain.crates": ("Contenedores", "Containers"),
    "terrain.crates.fx": ("Cobertura ligera", "Light cover"),
    "terrain.custom": ("Personalizado {n}", "Custom {n}"),
    "terrain.custom.fx": ("Definido por el usuario", "User defined"),
    # --- batalla ---
    "bt.size": ("TAMAÑO DEL TABLERO", "BOARD SIZE"),
    "bt.size_tip": ("Cambiar de tamaño limpia el tablero y reescala las cantidades del pool.",
                    "Changing size clears the board and rescales the pool quantities."),
    "bt.seed": ("Semilla: {n}", "Seed: {n}"),
    "bt.random": ("Aleatoria", "Random"),
    "bt.pool": ("POOL DE TERRENO", "TERRAIN POOL"),
    "bt.pool_hint": ("(clic: seleccionar · +/-: cantidad)", "(click: select · +/-: quantity)"),
    "bt.auto": ("Auto cantidad", "Auto quantity"),
    "bt.auto_tip": ("Cantidades sugeridas según el área del tablero.",
                    "Suggested quantities based on the board area."),
    "bt.clear_pool": ("Vaciar pool", "Empty pool"),
    "bt.clear_pool_tip": ("Pone todas las cantidades a 0.", "Sets every quantity to 0."),
    "bt.gen": ("Generar nuevo (G)", "Generate new (G)"),
    "bt.gen_tip": ("Borra el tablero y distribuye todo el pool de forma procedural.",
                   "Clears the board and distributes the whole pool procedurally."),
    "bt.fill": ("Completar", "Fill up"),
    "bt.fill_tip": ("Conserva las piezas actuales y añade las que falten según el pool.",
                    "Keeps current pieces and adds the missing ones according to the pool."),
    "bt.clear": ("Limpiar tablero", "Clear board"),
    "bt.clear_tip": ("Elimina todas las piezas colocadas.", "Removes every placed piece."),
    "bt.zones": ("Zonas desp.: {s}", "Deploy zones: {s}"),
    "bt.zones_tip": ("Muestra las zonas de despliegue (12'' ≈ 30 cm).",
                     "Shows deployment zones (12'' ≈ 30 cm)."),
    "bt.manual": ("Colocar manual: {s}", "Manual placing: {s}"),
    "bt.manual_tip": ("ON: un clic en zona vacía del tablero añade una pieza del tipo seleccionado.",
                      "ON: clicking an empty board spot adds a piece of the selected type."),
    "bt.export": ("Exportar PNG+JSON", "Export PNG+JSON"),
    "bt.export_tip": ("Guarda imagen y datos del tablero en la carpeta exports/.",
                      "Saves image and board data into the exports/ folder."),
    "bt.onboard": ("En mesa: {n} piezas   ·   Pool: {m}", "On table: {n} pieces   ·   Pool: {m}"),
    "bt.title": ("Tablero {w} x {h} cm  (≈ {fw}' x {fh}')", "Board {w} x {h} cm  (≈ {fw}' x {fh}')"),
    "bt.help": ("Arrastrar: mover · Clic der.: borrar · R: rotar · Supr: borrar",
                "Drag: move · Right-click: delete · R: rotate · Del: delete"),
    "bt.editor": ("EDITOR DEL TIPO SELECCIONADO / PIEZA", "SELECTED TYPE / PIECE EDITOR"),
    "bt.w": ("Ancho", "Width"),
    "bt.h": ("Alto", "Height"),
    "bt.shape": ("Forma: {s}", "Shape: {s}"),
    "bt.ellipse": ("Elipse", "Ellipse"),
    "bt.rect": ("Rect.", "Rect."),
    "bt.shape_tip": ("Alterna entre forma elíptica (colinas, bosques) y rectangular (muros, ruinas).",
                     "Toggles between elliptical (hills, forests) and rectangular (walls, ruins)."),
    "bt.del_type": ("Eliminar tipo", "Delete type"),
    "bt.del_type_tip": ("Elimina el tipo del pool y todas sus piezas del tablero.",
                        "Removes the type from the pool and all its pieces from the board."),
    "bt.new_type": ("+ Nuevo tipo", "+ New type"),
    "bt.new_type_tip": ("Crea un tipo de terreno personalizado (máx. 10 tipos).",
                        "Creates a custom terrain type (max. 10 types)."),
    "bt.piece": ("Pieza #{i}: {n}  {w:g} x {h:g} cm  pos ({x:.0f}, {y:.0f})",
                 "Piece #{i}: {n}  {w:g} x {h:g} cm  pos ({x:.0f}, {y:.0f})"),
    "bt.rotate": ("Rotar (R)", "Rotate (R)"),
    "bt.delete": ("Borrar (Supr)", "Delete (Del)"),
    "bt.select_hint": ("Selecciona una pieza del tablero para rotarla o borrarla.",
                       "Select a board piece to rotate or delete it."),
    "bt.ready": ("Listo. Pulsa «Generar nuevo».", "Ready. Press \"Generate new\"."),
    "bt.size_msg": ("Tablero {w}x{h} cm. Cantidades reescaladas.", "Board {w}x{h} cm. Quantities rescaled."),
    "bt.placed": ("Colocadas {p}/{w} piezas nuevas.", "Placed {p}/{w} new pieces."),
    "bt.placed_miss": (" {m} no cupieron (reduce cantidades).", " {m} did not fit (reduce quantities)."),
    "bt.cleared": ("Tablero limpio.", "Board cleared."),
    "bt.added": ("Añadido: {n}.", "Added: {n}."),
    "bt.exported": ("Exportado: {f}", "Exported: {f}"),
    "bt.deploy_a": ("DESPLIEGUE A ({d} cm)", "DEPLOYMENT A ({d} cm)"),
    "bt.deploy_b": ("DESPLIEGUE B ({d} cm)", "DEPLOYMENT B ({d} cm)"),
    "bt.exp_title": ("OPR · Tablero {w}x{h} cm · {n} piezas · semilla {s}",
                     "OPR · Board {w}x{h} cm · {n} pieces · seed {s}"),
    "bt.ctx_defends": (" · defiende {f}", " · defended by {f}"),
    "bt.ctx_free": (" · territorio libre", " · free territory"),
    "on": ("ON", "ON"),
    "off": ("OFF", "OFF"),
    # --- facciones ---
    "fac.title": ("FACCIONES", "FACTIONS"),
    "fac.h_name": ("Nombre", "Name"),
    "fac.h_terr": ("Terr.", "Terr."),
    "fac.h_bld": ("Edif.", "Bldg."),
    "fac.h_cr": ("Rec. campaña (CR)", "Campaign res. (CR)"),
    "fac.h_rr": ("Rec. reclutar (RR)", "Recruit res. (RR)"),
    "fac.h_units": ("Ejército", "Army"),
    "fac.h_fallen": ("Bajas", "Fallen"),
    "fac.h_income": ("Ingreso por turno", "Income per turn"),
    "fac.color_tip": ("Clic para cambiar de color.", "Click to change color."),
    "fac.army": ("Ejército", "Army"),
    "fac.army_tip": ("Abrir la lista de ejército de esta facción (editar / importar de Army Forge).",
                     "Open this faction's army list (edit / import from Army Forge)."),
    "fac.delete": ("Eliminar", "Delete"),
    "fac.add": ("+ Añadir facción", "+ Add faction"),
    "fac.add_tip": ("Máximo 6 facciones.", "Maximum 6 factions."),
    "fac.turn": ("Turno: {n}", "Turn: {n}"),
    "fac.ptsrr": ("Pts por 1 RR:", "Pts per 1 RR:"),
    "fac.ptsrr_tip": ("Coste de reclutamiento por defecto = puntos de la unidad / este valor.",
                      "Default recruitment cost = unit points / this value."),
    "fac.end_turn": ("Finalizar turno (aplicar ingresos)", "End turn (apply income)"),
    "fac.end_turn_tip": ("Suma CR y RR de todos y recupera bajas según los hospitales.",
                         "Adds CR and RR to everyone and recovers casualties via hospitals."),
    "fac.log": ("REGISTRO DE CAMPAÑA", "CAMPAIGN LOG"),
    "fac.income1": ("+{cr} CR   +{rr} RR   Recup. {rec}", "+{cr} CR   +{rr} RR   Recov. {rec}"),
    "fac.income2": ("Inic. +{ini}   Def. +{df}", "Init. +{ini}   Def. +{df}"),
    "fac.units_val": ("{n} uds · {pts} pts", "{n} units · {pts} pts"),
    # --- ejército ---
    "army.title": ("LISTA DE EJÉRCITO · {f}", "ARMY LIST · {f}"),
    "army.list_name": ("Nombre de la lista", "List name"),
    "army.system": ("Sistema", "System"),
    "army.totals": ("{n} unidades · {pts} pts en total · {a} pts activos · {f} caídas",
                    "{n} units · {pts} pts total · {a} pts active · {f} fallen"),
    "army.h_unit": ("Unidad", "Unit"),
    "army.h_mod": ("Mod.", "Mod."),
    "army.h_q": ("Q", "Q"),
    "army.h_d": ("D", "D"),
    "army.h_pts": ("Pts", "Pts"),
    "army.h_rr": ("RR", "RR"),
    "army.back": ("< Volver a facciones", "< Back to factions"),
    "army.no_units": ("La lista está vacía. Importa una o añade unidades.",
                      "The list is empty. Import one or add units."),
    "army.scroll": ("{a}-{b} de {n}", "{a}-{b} of {n}"),
    "army.import_title": ("IMPORTAR DESDE ARMY FORGE", "IMPORT FROM ARMY FORGE"),
    "army.src_hint": ("Enlace «Share as Link», ID de lista, o ruta a un .txt/.json  (Ctrl+V pega)",
                      "\"Share as Link\" URL, list ID, or path to a .txt/.json  (Ctrl+V pastes)"),
    "army.import": ("Importar", "Import"),
    "army.import_tip": ("Descarga el enlace/ID de Army Forge (requiere internet) o lee el archivo indicado.",
                        "Downloads the Army Forge link/ID (needs internet) or reads the given file."),
    "army.clip": ("Importar texto del portapapeles", "Import clipboard text"),
    "army.clip_tip": ("En Army Forge: menú > «Export» > texto. Copia y pulsa aquí.",
                      "In Army Forge: menu > Export > text. Copy it and click here."),
    "army.mode_replace": ("Modo: reemplazar", "Mode: replace"),
    "army.mode_append": ("Modo: añadir", "Mode: append"),
    "army.mode_tip": ("Reemplazar la lista actual o añadir las unidades al final.",
                      "Replace the current list or append the units at the end."),
    "army.as_active": ("Entran como: activas", "Import as: active"),
    "army.as_reserve": ("Entran como: reserva", "Import as: reserve"),
    "army.as_tip": ("Estado de las unidades importadas (las de reserva se reclutan con RR).",
                    "Status of imported units (reserve units are recruited with RR)."),
    "army.fetching": ("Descargando de Army Forge...", "Downloading from Army Forge..."),
    "army.imported": ("Importadas {n} unidades ({pts} pts).", "Imported {n} units ({pts} pts)."),
    "army.err_src": ("Escribe un enlace, un ID o una ruta de archivo.",
                     "Enter a link, an ID or a file path."),
    "army.err_clip": ("El portapapeles está vacío o no se pudo leer.",
                      "The clipboard is empty or could not be read."),
    "army.err_parse": ("No se encontraron unidades en el contenido: {err}",
                       "No units were found in the content: {err}"),
    "army.err_net": ("No se pudo descargar ({err}). Usa la exportación de texto de Army Forge.",
                     "Download failed ({err}). Use Army Forge's text export instead."),
    "army.editor": ("EDITOR DE UNIDAD", "UNIT EDITOR"),
    "army.select_hint": ("Selecciona una unidad de la lista para editarla.",
                         "Select a unit from the list to edit it."),
    "army.lbl_name": ("Nombre", "Name"),
    "army.lbl_models": ("Modelos", "Models"),
    "army.lbl_q": ("Calidad", "Quality"),
    "army.lbl_d": ("Defensa", "Defense"),
    "army.lbl_pts": ("Puntos", "Points"),
    "army.lbl_rr": ("Coste RR", "RR cost"),
    "army.lbl_status": ("Estado", "Status"),
    "army.lbl_rules": ("Reglas", "Rules"),
    "army.lbl_weapons": ("Armas", "Weapons"),
    "army.lbl_notes": ("Notas", "Notes"),
    "army.prev_rules": ("Reglas: {t}", "Rules: {t}"),
    "army.prev_weapons": ("Armas: {t}", "Weapons: {t}"),
    "st.active": ("Activa", "Active"),
    "st.reserve": ("Reserva", "Reserve"),
    "st.fallen": ("Caída", "Fallen"),
    "army.new_unit": ("Nueva unidad", "New unit"),
    "army.new": ("+ Nueva unidad", "+ New unit"),
    "army.dup": ("Duplicar", "Duplicate"),
    "army.del": ("Borrar", "Delete"),
    "army.up": ("Subir", "Up"),
    "army.down": ("Bajar", "Down"),
    "army.recruit": ("Reclutar ({c} RR)", "Recruit ({c} RR)"),
    "army.recruit_tip": ("Solo unidades en reserva. Descuenta el coste RR de la facción.",
                         "Reserve units only. Charges the RR cost to the faction."),
    "army.recruited": ("{u} reclutada (-{c} RR).", "{u} recruited (-{c} RR)."),
    "army.no_rr": ("RR insuficientes para reclutar.", "Not enough RR to recruit."),
    "army.resources": ("Recursos: {cr} CR · {rr} RR", "Resources: {cr} CR · {rr} RR"),

    # --- v3: pestañas de batalla ---
    "bt.tab_terrain": ("Terreno", "Terrain"),
    "bt.tab_deploy": ("Despliegue", "Deployment"),
    "bt.tab_rules": ("Reglas", "Rules"),
    "bt.cond_label": ("Condición: {c}", "Condition: {c}"),
    # --- v3: despliegue ---
    "dep.title": ("TIPO DE DESPLIEGUE (OPR)", "DEPLOYMENT TYPE (OPR)"),
    "dep.random": ("Aleatorio (D6)", "Random (D6)"),
    "dep.random_tip": ("Tirada de D6 con la tabla de estilos de despliegue de OPR.",
                       "D6 roll on OPR's deployment style table."),
    "dep.rolled": ("D6 = {n}: {name}", "D6 = {n}: {name}"),
    "dep.swap": ("Intercambiar roles", "Swap roles"),
    "dep.swap_tip": ("Intercambia qué jugador (rojo/azul) ocupa cada zona.",
                     "Swaps which player (red/blue) holds each zone."),
    "dep.depth": ("Profundidad:", "Depth:"),
    "dep.auto": ("Auto", "Auto"),
    "dep.zones": ("Mostrar zonas: {s}", "Show zones: {s}"),
    "dep.reserve_label": ("Reservas: entran a menos de 3'' de cualquier borde (ronda 2+)",
                          "Reserves: enter within 3'' of any edge (round 2+)"),
    "dep.roles": ("Rojo: {a}   ·   Azul: {b}", "Red: {a}   ·   Blue: {b}"),
    "dep.note": ("Medidas aproximadas y ajustables con la profundidad. Consulta el Advanced Rulebook de OPR para las reglas exactas de cada estilo.",
                 "Measurements are approximate and adjustable via depth. See OPR's Advanced Rulebook for each style's exact rules."),
    "deploy.frontline": ("Primera línea", "Frontline"),
    "deploy.frontline.d": ("Despliegue estándar de OPR: cada jugador despliega junto a un borde largo del tablero, a menos de 12'' (≈30 cm) de él.",
                           "Standard OPR deployment: each player deploys along a long table edge, within 12'' (≈30 cm) of it."),
    "deploy.frontline.ra": ("Jugador A", "Player A"),
    "deploy.frontline.rb": ("Jugador B", "Player B"),
    "deploy.side": ("Batalla lateral", "Side Battle"),
    "deploy.side.d": ("Como la primera línea, pero los ejércitos despliegan junto a los bordes cortos del tablero.",
                      "Like Frontline, but the armies deploy along the short table edges."),
    "deploy.side.ra": ("Jugador A", "Player A"),
    "deploy.side.rb": ("Jugador B", "Player B"),
    "deploy.ambush": ("Emboscada", "Ambush"),
    "deploy.ambush.d": ("El defensor despliega en una zona central y el atacante lo rodea, desplegando cerca de los bordes (≈6'' / 15 cm).",
                        "The defender deploys in a central zone and the attacker surrounds it, deploying near the edges (≈6'' / 15 cm)."),
    "deploy.ambush.ra": ("Defensor", "Defender"),
    "deploy.ambush.rb": ("Atacante", "Attacker"),
    "deploy.spearhead": ("Punta de lanza", "Spearhead"),
    "deploy.spearhead.d": ("Esquinas opuestas: cada ejército ocupa una zona triangular en una esquina, en diagonal respecto al rival.",
                           "Opposite corners: each army holds a triangular zone in a corner, diagonally across from the enemy."),
    "deploy.spearhead.ra": ("Jugador A", "Player A"),
    "deploy.spearhead.rb": ("Jugador B", "Player B"),
    "deploy.flank": ("Asalto de flanco", "Flank Assault"),
    "deploy.flank.d": ("Despliegue de primera línea, pero cada jugador declara antes de empezar la mitad de su ejército como refuerzos: entran a menos de 3'' de cualquier borde a partir de la segunda ronda (franja verde).",
                       "Frontline deployment, but each player declares half their army as reinforcements before the game: they enter within 3'' of any table edge from round 2 (green strip)."),
    "deploy.flank.ra": ("Jugador A", "Player A"),
    "deploy.flank.rb": ("Jugador B", "Player B"),
    "deploy.cornered": ("Acorralado", "Cornered"),
    "deploy.cornered.d": ("Un ejército está acorralado en una esquina y el otro despliega en forma de L por los dos bordes opuestos.",
                          "One army is cornered in a table corner and the other deploys in an L shape along the two opposite edges."),
    "deploy.cornered.ra": ("Acorralado", "Cornered"),
    "deploy.cornered.rb": ("Atacante", "Attacker"),
    # --- v3: reglas ---
    "rl.title": ("CONDICIÓN DEL CAMPO DE BATALLA", "BATTLEFIELD CONDITION"),
    "rl.none": ("Ninguna", "None"),
    "rl.roll": ("Tirar dados", "Roll dice"),
    "rl.roll_tip": ("D6: 1-2 ninguna, 3-4 geológica, 5-6 misteriosa; después se elige una al azar.",
                    "D6: 1-2 none, 3-4 geological, 5-6 mysterious; then one is picked at random."),
    "rl.rolled_none": ("D6 = {d}: sin condición.", "D6 = {d}: no condition."),
    "rl.rolled": ("D6 = {d} ({k}): {c}.", "D6 = {d} ({k}): {c}."),
    "rl.kind_geo": ("geológica", "geological"),
    "rl.kind_myst": ("misteriosa", "mysterious"),
    "rl.geo": ("GEOLÓGICAS (clima)", "GEOLOGICAL (weather)"),
    "rl.myst": ("MISTERIOSAS", "MYSTERIOUS"),
    "rl.no_cond": ("Sin condición activa. Elige una o tira los dados.",
                   "No active condition. Pick one or roll the dice."),
    "rl.terrain_title": ("REGLAS DE TERRENO", "TERRAIN RULES"),
    "rl.target_type": ("Tipo: {n}", "Type: {n}"),
    "rl.target_piece": ("Pieza #{i}", "Piece #{i}"),
    "rl.target_tip": ("Las reglas del tipo se copian a las piezas nuevas; las de la pieza solo afectan a esa pieza.",
                      "Type rules are copied to new pieces; piece rules only affect that piece."),
    "rl.apply": ("Aplicar a todas las piezas del tipo", "Apply to all pieces of this type"),
    "rl.apply_tip": ("Copia las reglas del tipo a todas sus piezas ya colocadas.",
                     "Copies the type's rules to all of its placed pieces."),
    "rl.applied": ("Reglas aplicadas a {n} piezas.", "Rules applied to {n} pieces."),
    "rl.note": ("Resúmenes orientativos; consulta el reglamento de OPR.",
                "Indicative summaries; check the OPR rulebook."),
    "rule.cover": ("Cobertura", "Cover"),
    "rule.cover.d": ("Terreno de cobertura: +1 a las tiradas de defensa contra disparos.",
                     "Cover terrain: +1 to Defense rolls against shooting."),
    "rule.cover.c": ("Cb", "Cv"),
    "rule.difficult": ("Terreno difícil", "Difficult"),
    "rule.difficult.d": ("Terreno difícil: limita el movimiento total de las unidades que lo cruzan.",
                         "Difficult terrain: limits the total movement of units crossing it."),
    "rule.difficult.c": ("Df", "Df"),
    "rule.dangerous": ("Terreno peligroso", "Dangerous"),
    "rule.dangerous.d": ("Terreno peligroso: se tira un dado al cruzarlo o activarse en él; con un 1 la unidad sufre una herida.",
                         "Dangerous terrain: roll a die when crossing or activating in it; on a 1 the unit takes a wound."),
    "rule.dangerous.c": ("Pg", "Dg"),
    "rule.sight": ("Bloquea visión", "Blocks LoS"),
    "rule.sight.d": ("Bloquea la línea de visión.", "Blocks line of sight."),
    "rule.sight.c": ("LV", "LoS"),
    "rule.barrier": ("Barrera defensiva", "Defensive Barrier"),
    "rule.barrier.d": ("Efecto de terreno: una burbuja de energía protege a los ocupantes de los proyectiles.",
                       "Terrain effect: an energy bubble protects occupants from projectiles."),
    "rule.barrier.c": ("BD", "DB"),
    "rule.vigor": ("Vigor psíquico", "Psychic Vigor"),
    "rule.vigor.d": ("Efecto de terreno: un aura psíquica mejora las capacidades de combate de los ocupantes.",
                     "Terrain effect: a psychic aura enhances the combat abilities of its occupants."),
    "rule.vigor.c": ("VP", "PV"),
    "rule.earthquake": ("Terremoto", "Earthquake"),
    "rule.earthquake.d": ("Condición geológica: toda la mesa cuenta como terreno peligroso; el que ya lo era resulta más letal.",
                          "Geological condition: the whole table counts as dangerous terrain; terrain that already was becomes deadlier."),
    "rule.earthquake.c": ("Tm", "Eq"),
    "rule.storm": ("Tormenta intensa", "Heavy Storm"),
    "rule.storm.d": ("Condición geológica (clima): una tormenta que daña o dificulta a las unidades en pleno campo. Consulta el reglamento para el efecto exacto.",
                     "Geological (weather) condition: a storm that harms or hampers units in the open. See the rulebook for the exact effect."),
    "rule.storm.c": ("Tr", "St"),
    "rule.mud": ("Terreno embarrado", "Muddy Terrain"),
    "rule.mud.d": ("Condición geológica: el barro afecta al movimiento y a la resistencia de las unidades. Consulta el reglamento para el efecto exacto.",
                   "Geological condition: mud affects movement and unit toughness. See the rulebook for the exact effect."),
    "rule.mud.c": ("Ba", "Md"),
    "rule.damnation": ("Condenación", "Damnation"),
    "rule.damnation.d": ("Condición misteriosa: al inicio de cada ronda cada jugador sacrifica una unidad (D3 heridas); si no, sus unidades sufren -1 a ataque, defensa y moral esa ronda.",
                         "Mysterious condition: at the start of each round each player sacrifices a unit (D3 wounds); otherwise their units get -1 to attack, defense and morale rolls that round."),
    "rule.damnation.c": ("Cd", "Dm"),
    "rule.arcane": ("Poder arcano", "Arcane Power"),
    "rule.arcane.d": ("Condición misteriosa: los psíquicos obtienen +1 a lanzar y bloquear; con un 1 natural sufren D3 heridas.",
                      "Mysterious condition: psychics get +1 to casting and blocking; on a natural 1 they take D3 wounds."),
    "rule.arcane.c": ("PA", "AP"),
    "rule.inspiration": ("Inspiración", "Inspiration"),
    "rule.inspiration.d": ("Condición misteriosa: las unidades obtienen +1 a las tiradas de moral.",
                           "Mysterious condition: units get +1 to morale test rolls."),
    "rule.inspiration.c": ("In", "In"),
    "rule.vortex": ("Vórtice mortal", "Deadly Vortex"),
    "rule.vortex.d": ("Condición misteriosa letal que provoca daño automático a las unidades. Consulta el reglamento para el efecto exacto.",
                      "Lethal mysterious condition that deals automatic damage to units. See the rulebook for the exact effect."),
    "rule.vortex.c": ("VM", "DV"),
    "rule.fog": ("Niebla mística", "Mystical Fog"),
    "rule.fog.d": ("Condición misteriosa: las coberturas protegen aún más y las unidades sufren -2 para impactar.",
                   "Mysterious condition: cover terrain protects even more and units get -2 to hit rolls."),
    "rule.fog.c": ("NM", "MF"),
    "rule.echoes": ("Ecos siniestros", "Sinister Echoes"),
    "rule.echoes.d": ("Condición misteriosa: las unidades aturdidas sufren D3 heridas y las que pierden una melé dañan a las aliadas cercanas.",
                      "Mysterious condition: stunned units take D3 wounds and units losing a melee hurt nearby friendly units."),
    "rule.echoes.c": ("EC", "SE"),
    # --- v3: ejército ---
    "army.lbl_upgrades": ("Mejoras", "Upgrades"),
    "army.prev_upgrades": ("Mejoras: {t}", "Upgrades: {t}"),
    "army.list_pts_warn": (" Army Forge indica {n} pts en total.", " Army Forge reports {n} pts in total."),

    # --- v4: logística y mapa ---
    "camp.logistics": ("Logística: {s}", "Logistics: {s}"),
    "camp.logistics_tip": ("ON: construir, cobrar ingresos y avanzar sobre territorios nuevos exige estar conectado (por adyacencia o rutas) con la capital.",
                           "ON: building, collecting income and advancing into new territories requires a connection (adjacency or routes) to the capital."),
    "camp.end_turn": ("Finalizar turno >", "End turn >"),
    "camp.tab_terr": ("Territorio", "Territory"),
    "camp.tab_forces": ("Fuerzas", "Forces"),
    "camp.tab_hist": ("Historial", "History"),
    "camp.supplied": ("Conectado a la red de suministro", "Connected to the supply network"),
    "camp.cutoff": ("AISLADO: sin ruta hasta la capital", "CUT OFF: no route to the capital"),
    "camp.logi_off": ("Logística desactivada", "Logistics disabled"),
    "camp.forces": ("FUERZAS PRESENTES", "FORCES PRESENT"),
    "camp.no_forces": ("- ninguna -", "- none -"),
    "camp.move": ("Mover", "Move"),
    "camp.moved": ("movida", "moved"),
    "camp.move_tip": ("Selecciona la fuerza y haz clic en un territorio resaltado del mapa (verde = avance, rojo = ataque).",
                      "Select the force, then click a highlighted territory on the map (green = advance, red = attack)."),
    "camp.routes": ("RUTAS / PUERTOS", "ROUTES / PORTS"),
    "camp.no_routes": ("- sin rutas -", "- no routes -"),
    "camp.add_route": ("+ Añadir ruta", "+ Add route"),
    "camp.add_route_tip": ("Conecta este territorio con otro no adyacente (ruta marítima o puerto). Repetir la ruta la quita.",
                           "Links this territory to a non-adjacent one (sea route or port). Repeating a route removes it."),
    "camp.route_pick": ("Elige el destino en el mapa...", "Pick the destination on the map..."),
    "camp.route_del_tip": ("Quitar ruta", "Remove route"),
    "camp.record": ("Registrar resultado", "Record result"),
    "camp.record_tip": ("Registra una batalla en este territorio: ganador, bajas, XP e historial.",
                        "Records a battle in this territory: winner, losses, XP and history."),
    "camp.clash": ("Choque pendiente: {a} vs {d}", "Pending clash: {a} vs {d}"),
    "camp.force_line": ("{f} · {n} ({u} uds · {p} pts)", "{f} · {n} ({u} units · {p} pts)"),
    "camp.hist_title": ("HISTORIAL DE COMBATES ({n})", "BATTLE HISTORY ({n})"),
    "camp.hist_empty": ("Aún no se han librado batallas aquí.", "No battles have been fought here yet."),
    "camp.hist_l1": ("T{t} · {d}", "T{t} · {d}"),
    "camp.hist_l2": ("{a} vs {b} -> {w} · bajas {la}/{ld}", "{a} vs {b} -> {w} · losses {la}/{ld}"),
    "camp.won": ("gana {f}", "{f} wins"),
    "camp.draw": ("empate", "draw"),
    "camp.neutral": ("Neutral", "Neutral"),
    "err.cutoff": ("Territorio aislado: sin ruta de suministro hasta la capital.",
                   "Cut-off territory: no supply route to the capital."),
    "err.no_force": ("Esa fuerza no existe.", "That force does not exist."),
    "err.moved": ("Esa fuerza ya se movió este turno.", "That force has already moved this turn."),
    "err.move_far": ("Solo puedes moverte a territorios adyacentes o unidos por ruta.",
                     "You can only move to adjacent or route-linked territories."),
    "err.move_supply": ("Para avanzar sobre un territorio ajeno debes salir de un territorio propio conectado a la capital.",
                        "To advance into a foreign territory you must start from an own territory connected to the capital."),
    "status.moved": ("{f}: {n} se mueve a {q}.", "{f}: {n} moves to {q}."),
    "status.captured": ("{f}: {n} captura {q}.", "{f}: {n} captures {q}."),
    "status.clash": ("¡Choque en {q}! Juega la batalla y registra el resultado.",
                     "Clash in {q}! Play the battle and record the result."),
    "status.recorded": ("Resultado registrado en {q}.", "Result recorded in {q}."),
    "status.route_added": ("Ruta creada.", "Route created."),
    "status.route_removed": ("Ruta eliminada.", "Route removed."),
    "status.route_adjacent": ("Esos territorios ya están conectados por adyacencia.",
                              "Those territories are already connected by adjacency."),
    "log.move": ("T{t} · {f}: {n} se mueve a {q}.", "T{t} · {f}: {n} moves to {q}."),
    "log.capture": ("T{t} · {f}: {n} captura {q}.", "T{t} · {f}: {n} captures {q}."),
    "log.clash": ("T{t} · {a} ataca a {d} en {q}.", "T{t} · {a} attacks {d} in {q}."),
    "log.battle": ("T{t} · Batalla en {q}: {a} vs {d} -> {w} (bajas {la}/{ld}).",
                   "T{t} · Battle in {q}: {a} vs {d} -> {w} (losses {la}/{ld})."),
    "log.rankup": ("{u} asciende a {r}.", "{u} is promoted to {r}."),
    "force.name": ("Fuerza {n}", "Force {n}"),
    "fac.h_forces": ("Fuerzas", "Forces"),
    "fac.forces_tip": ("Número de fuerzas (fichas móviles) de la facción. Las nuevas aparecen en la capital.",
                       "Number of forces (movable tokens) for the faction. New ones appear at the capital."),
    # --- v4: resultado de batalla ---
    "res.title": ("REGISTRAR RESULTADO · {q}", "RECORD RESULT · {q}"),
    "res.att": ("Atacante: {f}", "Attacker: {f}"),
    "res.def": ("Defensor: {f}", "Defender: {f}"),
    "res.cycle_tip": ("Clic para cambiar de facción.", "Click to change faction."),
    "res.win_att": ("Gana atacante", "Attacker wins"),
    "res.win_draw": ("Empate", "Draw"),
    "res.win_def": ("Gana defensor", "Defender wins"),
    "res.att_units": ("UNIDADES DEL ATACANTE", "ATTACKER UNITS"),
    "res.def_units": ("UNIDADES DEL DEFENSOR", "DEFENDER UNITS"),
    "res.fallen": ("Baja", "Lost"),
    "res.none_units": ("- sin unidades activas -", "- no active units -"),
    "res.note": ("Notas:", "Notes:"),
    "res.save": ("Registrar", "Record"),
    "res.cancel": ("Cancelar", "Cancel"),
    "res.xp_hint": ("XP automática: +1 por participar, +1 más al ganar (editable).",
                    "Automatic XP: +1 for taking part, +1 more for winning (editable)."),
    # --- v4: XP y avances ---
    "army.tab_unit": ("Unidad", "Unit"),
    "army.tab_xp": ("XP y avances", "XP & advances"),
    "army.lbl_force": ("Fuerza", "Force"),
    "army.lbl_xp": ("XP", "XP"),
    "army.col_xp": ("XP", "XP"),
    "army.rank": ("Rango: {r}  (XP {x})", "Rank: {r}  (XP {x})"),
    "army.next_rank": ("Siguiente rango: {x} XP", "Next rank: {x} XP"),
    "army.max_rank": ("Rango máximo alcanzado", "Maximum rank reached"),
    "army.ap": ("Avances disponibles: {n}", "Advances available: {n}"),
    "army.adv_title": ("AVANCES (1 punto cada uno)", "ADVANCES (1 point each)"),
    "army.adv_applied": ("{u}: avance «{a}» aplicado.", "{u}: advance \"{a}\" applied."),
    "army.adv_done": ("Obtenidos: {t}", "Gained: {t}"),
    "army.adv_none": ("ninguno", "none"),
    "army.adv_undo": ("Deshacer último avance", "Undo last advance"),
    "army.prev_adv": ("Avances: {t}", "Advances: {t}"),
    "adv.quality": ("+1 Calidad", "+1 Quality"),
    "adv.quality.d": ("Mejora la calidad un paso (hasta 2+). Máx. 2 veces.", "Improves quality one step (down to 2+). Max 2 times."),
    "adv.defense": ("+1 Defensa", "+1 Defense"),
    "adv.defense.d": ("Mejora la defensa un paso (hasta 2+). Máx. 2 veces.", "Improves defense one step (down to 2+). Max 2 times."),
    "adv.attack": ("+1 Ataque", "+1 Attack"),
    "adv.attack.d": ("+1 ataque al arma principal (se anota; aplícalo al jugar). Máx. 2 veces.",
                     "+1 attack on the main weapon (noted; apply it in play). Max 2 times."),
    "adv.furious": ("Regla: Furious", "Rule: Furious"),
    "adv.furious.d": ("Añade la regla especial Furious.", "Adds the Furious special rule."),
    "adv.fearless": ("Regla: Fearless", "Rule: Fearless"),
    "adv.fearless.d": ("Añade la regla especial Fearless.", "Adds the Fearless special rule."),
    "adv.scout": ("Regla: Scout", "Rule: Scout"),
    "adv.scout.d": ("Añade la regla especial Scout.", "Adds the Scout special rule."),
    "adv.strider": ("Regla: Strider", "Rule: Strider"),
    "adv.strider.d": ("Añade la regla especial Strider.", "Adds the Strider special rule."),
    "adv.stealth": ("Regla: Stealth", "Rule: Stealth"),
    "adv.stealth.d": ("Añade la regla especial Stealth.", "Adds the Stealth special rule."),
    "rank.0": ("Recluta", "Rookie"),
    "rank.1": ("Veterano", "Veteran"),
    "rank.2": ("Élite", "Elite"),
    "rank.3": ("Leyenda", "Legend"),
    # --- v4: sistemas OPR ---
    "army.limit": ("Límite de puntos", "Points limit"),
    "army.system_tip": ("Clic para cambiar de sistema OPR. Ajusta el límite de puntos, las advertencias y el tablero recomendado.",
                        "Click to change OPR system. Adjusts the points limit, warnings and recommended board."),
    "army.limit_tip": ("0 = sin límite.", "0 = no limit."),
    "army.w_limit": ("Total {t} pts supera el límite de {l} pts.", "Total {t} pts exceeds the {l} pts limit."),
    "army.w_pct": ("{u} ({p} pts) supera el {pct}% de la lista (máx. {m} pts).",
                   "{u} ({p} pts) exceeds {pct}% of the list (max {m} pts)."),
    "army.w_units": ("{n} unidades: máx. recomendado {m} (1 por cada {per} pts).",
                     "{n} units: recommended max {m} (1 per {per} pts)."),
    "army.warn_more": (" (+{n} más)", " (+{n} more)"),
    "sys.GEN": ("Genérico (sin restricciones)", "Generic (no restrictions)"),
    "sys.GF": ("Grimdark Future", "Grimdark Future"),
    "sys.GFF": ("Grimdark Future: Firefight", "Grimdark Future: Firefight"),
    "sys.AoF": ("Age of Fantasy", "Age of Fantasy"),
    "sys.AoFS": ("Age of Fantasy: Skirmish", "Age of Fantasy: Skirmish"),
    "sys.AoFR": ("Age of Fantasy: Regiments", "Age of Fantasy: Regiments"),
    "sys.GFW": ("Grimdark Future: Warfleets", "Grimdark Future: Warfleets"),
    "sys.i_pts": ("{n} pts por defecto", "{n} pts by default"),
    "sys.i_pct": ("máx. {n}% por unidad", "max {n}% per unit"),
    "sys.i_per": ("1 unidad por cada {n} pts", "1 unit per {n} pts"),
    "sys.i_board": ("tablero {w}x{h} cm", "{w}x{h} cm board"),
    "sys.i_terrain": ("{n}+ piezas de terreno", "{n}+ terrain pieces"),
    "sys.note": ("Valores de referencia editables.", "Editable reference values."),
}



T.update({
    # --- textos modificados ---
    "b.barracks.d": ("+2 RR por turno. Permite reclutar unidades en reserva.",
                     "+2 RR per turn. Lets armies recruit reserve units."),
    "b.hospital.d": ("Recupera hasta 2 unidades caídas por turno, solo de los ejércitos presentes en este territorio.",
                     "Recovers up to 2 fallen units per turn, only from armies present in this territory."),
    "b.fortress.d": ("+1 defensa para el defensor en batallas de este territorio. Permite reclutar.",
                     "+1 defense for the defender in battles in this territory. Lets armies recruit."),
    "b.tower.d": ("+1 a la iniciativa/despliegue solo en las batallas libradas en este territorio.",
                  "+1 to initiative/deployment only in battles fought in this territory."),
    "fac.income1": ("+{cr} CR   +{rr} RR", "+{cr} CR   +{rr} RR"),
    "fac.income2": ("Mant.: -{up} CR/turno", "Upkeep: -{up} CR/turn"),
    "log.turn": ("T{t} · {f}: +{cr} CR, +{rr} RR.", "T{t} · {f}: +{cr} CR, +{rr} RR."),
    "camp.add_route": ("+ Añadir ruta ({c} CR)", "+ Add route ({c} CR)"),
    "camp.add_route_tip": ("Construye una ruta entre este territorio y otro de tu facción no adyacente. Se destruye si uno de los extremos cambia de dueño.",
                           "Builds a route between this territory and another non-adjacent one of your faction. It is destroyed if either end changes hands."),
    "camp.route_del_tip": ("Quitar ruta (sin reembolso)", "Remove route (no refund)"),
    "res.fallen": ("Caída", "Fallen"),
    "army.recruit_tip": ("Pasa la unidad de reserva a activa. Cuesta su coste en RR y exige que el ejército esté en un territorio propio con Cuartel o Fortaleza.",
                         "Moves the unit from reserve to active. Costs its RR cost and requires the army to be in an own territory with a Barracks or Fortress."),
    "dlg.title": ("CAMPAÑAS", "CAMPAIGNS"),
    "dlg.default_name": ("Campaña 1", "Campaign 1"),
    # --- v5: errores ---
    "err.force_max": ("Ya tienes el máximo de ejércitos.", "You already have the maximum number of armies."),
    "err.force_base": ("Los ejércitos nuevos solo aparecen en la base principal (casilla de salida), que debe seguir siendo tuya.",
                       "New armies only appear at the main base (starting square), which you must still own."),
    "err.force_funds": ("Crear un ejército cuesta {c} CR.", "Creating an army costs {c} CR."),
    "err.force_remove": ("Solo puedes eliminar un ejército vacío que no sea el principal.",
                         "You can only delete an empty army that is not the main one."),
    "err.recruit_loc": ("El ejército debe estar en un territorio propio con Cuartel o Fortaleza para reclutar.",
                        "The army must be in an own territory with a Barracks or Fortress to recruit."),
    "err.recruit_rr": ("RR insuficientes para reclutar esta unidad.", "Not enough RR to recruit this unit."),
    "err.status_destroyed": ("Una unidad destruida es irrecuperable.", "A destroyed unit is irrecoverable."),
    "err.status_fallen": ("Una unidad caída solo se recupera en un Hospital (o se da por destruida).",
                          "A fallen unit can only recover in a Hospital (or be written off as destroyed)."),
    "err.status_no": ("Ese cambio de estado no está permitido.", "That status change is not allowed."),
    "err.route_own": ("Las rutas solo pueden unir dos territorios controlados por la misma facción.",
                      "Routes can only link two territories controlled by the same faction."),
    "err.route_adjacent": ("Esos territorios ya están conectados por adyacencia.",
                           "Those territories are already connected by adjacency."),
    "err.route_exists": ("Ya existe una ruta entre esos territorios.", "A route between those territories already exists."),
    "err.route_funds": ("Una ruta cuesta {c} CR.", "A route costs {c} CR."),
    "status.route_built": ("Ruta construida (-{c} CR).", "Route built (-{c} CR)."),
    "status.route_lost": ("{n} ruta(s) destruida(s): uno de sus extremos cambió de dueño.",
                          "{n} route(s) destroyed: one of their ends changed hands."),
    "status.force_created": ("{n} creado en la base principal (-{c} CR).", "{n} created at the main base (-{c} CR)."),
    # --- v5: registro ---
    "log.route_built": ("T{t} · {f} construye una ruta {a} - {b} (-{c} CR).", "T{t} · {f} builds a route {a} - {b} (-{c} CR)."),
    "log.route_lost": ("T{t} · Ruta {a} - {b} destruida.", "T{t} · Route {a} - {b} destroyed."),
    "log.hospital": ("T{t} · Hospital de {q}: {n} unidad(es) recuperada(s).", "T{t} · Hospital in {q}: {n} unit(s) recovered."),
    "log.upkeep": ("T{t} · {f}: mantenimiento -{c} CR.", "T{t} · {f}: upkeep -{c} CR."),
    "log.unpaid": ("T{t} · {f}: sin CR para mantener a {n}; moral -1.", "T{t} · {f}: not enough CR to maintain {n}; morale -1."),
    "log.reverted": ("T{t} · {f}: {n} vuelve(n) a reserva por falta de mantenimiento.",
                     "T{t} · {f}: {n} return(s) to reserve for lack of upkeep."),
    "log.force_new": ("T{t} · {f} crea el ejército {n} (-{c} CR).", "T{t} · {f} creates army {n} (-{c} CR)."),
    # --- v5: facciones y ejércitos ---
    "fac.h_armies": ("Ejércitos", "Armies"),
    "fac.armies_n": ("{n}/{m}", "{n}/{m}"),
    "fac.new_army": ("+ {c} CR", "+ {c} CR"),
    "fac.new_army_tip": ("Crea un ejército nuevo en la base principal (casilla de salida).",
                         "Creates a new army at the main base (starting square)."),
    "fac.opr_line": ("{s} · {f}", "{s} · {f}"),
    "fac.no_opr": ("sin facción OPR", "no OPR faction"),
    "army.army_n": ("Ejército {n}", "Army {n}"),
    "army.opr_faction": ("Facción OPR", "OPR faction"),
    "army.opr_none": ("- elegir -", "- choose -"),
    "army.opr_tip": ("Elige la facción oficial de OPR (Army Forge) acorde al sistema de la campaña.",
                     "Pick the official OPR faction (Army Forge) matching the campaign system."),
    "army.catalog": ("Catálogo OPR", "OPR catalog"),
    "army.catalog_tip": ("Abre el catálogo local de la facción OPR: unidades, estadísticas, reglas, opciones y costes.",
                         "Opens the local catalog of the OPR faction: units, stats, rules, options and costs."),
    "army.catalog_need": ("Primero asigna una facción OPR (botón «Facción OPR»).",
                          "First assign an OPR faction (\"OPR faction\" button)."),
    "army.del_army": ("Eliminar ejército", "Delete army"),
    "army.new_army_btn": ("+ ({c} CR)", "+ ({c} CR)"),
    "army.upkeep": ("Mant.: {n} CR/turno", "Upkeep: {n} CR/turn"),
    "army.unpaid": ("Sin pagar: -1 moral", "Unpaid: -1 morale"),
    "army.sys_locked": ("El sistema lo fija el tipo de campaña.", "The system is set by the campaign type."),
    "army.sys_mismatch": (" Aviso: la lista es {a} y la facción {b}.", " Warning: the list is {a} and the faction {b}."),
    "army.refunded": ("{u} pasa a reserva (+{n} RR).", "{u} goes back to reserve (+{n} RR)."),
    "army.reserve_note": ("Las unidades importadas o añadidas entran en reserva.",
                          "Imported or added units start in reserve."),
    "tip.recruit": ("Cuesta {c} RR y exige estar en un territorio propio con Cuartel o Fortaleza.",
                    "Costs {c} RR and requires an own territory with a Barracks or Fortress."),
    "tip.refund": ("Devuelve la mitad del coste ({n} RR).", "Refunds half the cost ({n} RR)."),
    "tip.destroy": ("Elimina la unidad del juego de forma irrecuperable.", "Removes the unit from the game for good."),
    "st.destroyed": ("Destruida", "Destroyed"),
    # --- v5: resultado de batalla ---
    "res.ok": ("Ilesa", "Unhurt"),
    "res.destroyed": ("Destruida", "Destroyed"),
    "res.state_tip": ("Clic: ilesa -> caída (recuperable en Hospital) -> destruida (irrecuperable).",
                      "Click: unhurt -> fallen (recoverable in a Hospital) -> destroyed (irrecoverable)."),
    "camp.destroyed_note": (" · destruidas {a}/{d}", " · destroyed {a}/{d}"),
    "bt.local_bonus": (" · Locales: Inic. +{ini}, Def. +{df} para {f}", " · Local: Init. +{ini}, Def. +{df} for {f}"),
    # --- v5: campañas ---
    "dlg.new_title": ("NUEVA CAMPAÑA / RENOMBRAR   (formato obligatorio: [Gen|GF|GFF|AoF|AoFS|AoFR] nombre)",
                      "NEW CAMPAIGN / RENAME   (mandatory format: [Gen|GF|GFF|AoF|AoFS|AoFR] name)"),
    "dlg.type": ("Tipo: {t}", "Type: {t}"),
    "dlg.type_tip": ("Tipo de campaña: fija el sistema OPR de todas sus facciones («Gen» permite elegir).",
                     "Campaign type: fixes the OPR system of all its factions (\"Gen\" lets you choose)."),
    "dlg.base": ("Nombre:", "Name:"),
    "dlg.create": ("Crear", "Create"),
    "dlg.rename": ("Renombrar activa", "Rename active"),
    "dlg.open_title": ("CAMPAÑAS ABIERTAS ({n})", "OPEN CAMPAIGNS ({n})"),
    "dlg.saved_title": ("GUARDADAS", "SAVED"),
    "dlg.activate": ("Activar", "Activate"),
    "dlg.active": ("activa", "active"),
    "dlg.close_camp": ("Cerrar", "Close"),
    "dlg.close_camp_tip": ("Guarda y cierra esta campaña.", "Saves and closes this campaign."),
    "dlg.save_all": ("Guardar todas", "Save all"),
    "dlg.save_active": ("Guardar activa", "Save active"),
    "dlg.open": ("Abrir", "Open"),
    "dlg.name_exists": ("Ya hay una campaña abierta con ese nombre.", "A campaign with that name is already open."),
    "dlg.name_empty": ("Escribe un nombre para la campaña.", "Enter a name for the campaign."),
    "status.created": ("Campaña creada: {n}", "Campaign created: {n}"),
    "status.renamed": ("Campaña renombrada: {n}", "Campaign renamed: {n}"),
    "status.closed": ("Campaña cerrada: {n}", "Campaign closed: {n}"),
    "status.saved_all": ("{n} campaña(s) guardada(s).", "{n} campaign(s) saved."),
    # --- v5: base de datos OPR ---
    "opr.downloading_list": ("Descargando lista de facciones de Army Forge...", "Downloading faction list from Army Forge..."),
    "opr.list_ok": ("Lista descargada: {n} facciones.", "List downloaded: {n} factions."),
    "opr.list_fail": ("No se pudo descargar la lista ({err}).", "Could not download the list ({err})."),
    "opr.downloading_book": ("Descargando libro de ejército...", "Downloading army book..."),
    "opr.book_ok": ("Libro descargado: {n} unidades.", "Book downloaded: {n} units."),
    "opr.book_fail": ("No se pudo descargar el libro ({err}).", "Could not download the book ({err})."),
    "books.title": ("FACCIÓN OPR · {s}", "OPR FACTION · {s}"),
    "books.download": ("Descargar lista de Army Forge", "Download list from Army Forge"),
    "books.download_tip": ("Descarga las facciones oficiales del sistema (requiere internet) y las guarda en la caché local.",
                           "Downloads the system's official factions (needs internet) and stores them in the local cache."),
    "books.filter": ("Buscar:", "Search:"),
    "books.choose": ("Elegir", "Choose"),
    "books.clear": ("Quitar vínculo", "Remove link"),
    "books.empty": ("No hay facciones en caché para {s}. Descarga la lista o copia libros JSON en la carpeta de abajo.",
                    "No cached factions for {s}. Download the list or copy JSON books into the folder below."),
    "books.folder": ("Caché: {p}", "Cache: {p}"),
    "books.current": ("Actual: {n}", "Current: {n}"),
    "books.local_hint": ("Libros propios: copia el JSON de un libro como «{s}__nombre.json» en la carpeta de caché.",
                         "Own books: copy a book's JSON as \"{s}__name.json\" into the cache folder."),
    "books.close": ("Cerrar", "Close"),
    "books.none_sys": ("Elige un sistema OPR (no «Gen») para vincular una facción.",
                       "Pick an OPR system (not \"Gen\") to link a faction."),
    "cat.title": ("CATÁLOGO OPR · {n}", "OPR CATALOG · {n}"),
    "cat.search": ("Buscar unidad:", "Search unit:"),
    "cat.no_book": ("El libro no está en la caché local.", "The book is not in the local cache."),
    "cat.download": ("Descargar libro", "Download book"),
    "cat.stats": ("Calidad {q}+ · Defensa {d}+ · {s} modelo(s) · {c} pts base",
                  "Quality {q}+ · Defense {d}+ · {s} model(s) · {c} pts base"),
    "cat.rules": ("Reglas: {t}", "Rules: {t}"),
    "cat.weapons": ("Armas: {t}", "Weapons: {t}"),
    "cat.upgrades": ("MEJORAS Y OPCIONES", "UPGRADES AND OPTIONS"),
    "cat.no_upgrades": ("Esta unidad no tiene mejoras.", "This unit has no upgrades."),
    "cat.add": ("Añadir al ejército {n} (reserva)", "Add to army {n} (reserve)"),
    "cat.total": ("Coste total: {c} pts", "Total cost: {c} pts"),
    "cat.added": ("{u} añadida a {a} (en reserva).", "{u} added to {a} (in reserve)."),
    "cat.one": ("(elige una)", "(pick one)"),
    "cat.any": ("(cualquier número)", "(any number)"),
    "cat.replace": ("(reemplazo)", "(replacement)"),
    "cat.opt": ("{l}   ({c:+d} pts)", "{l}   ({c:+d} pts)"),
    "cat.units": ("{n} unidades", "{n} units"),
    "cat.note": ("Datos de Army Forge (One Page Rules), guardados en la caché local para uso personal.",
                 "Data from Army Forge (One Page Rules), kept in the local cache for personal use."),
})


def tr(key: str, **kw) -> str:
    v = T.get(key)
    if v is None:
        return key
    s = v[0] if LANG == "es" else v[1]
    return s.format(**kw) if kw else s


def set_lang(lang: str):
    global LANG
    LANG = lang if lang in LANGS else "es"


def bname(k: str) -> str:
    return tr(f"b.{k}")


def bdesc(k: str) -> str:
    return tr(f"b.{k}.d")


def bshort(k: str) -> str:
    return tr(f"b.{k}.s")


def rname(k: str) -> str:
    return tr(f"rule.{k}")


def rdesc(k: str) -> str:
    return tr(f"rule.{k}.d")


def rcode(k: str) -> str:
    return tr(f"rule.{k}.c")


def point_in_poly(x: float, y: float, poly) -> bool:
    inside = False
    n = len(poly)
    j = n - 1
    for i in range(n):
        xi, yi = poly[i]
        xj, yj = poly[j]
        if (yi > y) != (yj > y) and x < (xj - xi) * (y - yi) / ((yj - yi) or 1e-9) + xi:
            inside = not inside
        j = i
    return inside


def biome_name(i: int) -> str:
    return tr(f"biome.{i}")


def cost_str(k: str) -> str:
    b = BUILDINGS[k]
    parts = []
    if b.get("cost_cr"):
        parts.append(f"{b['cost_cr']} CR")
    if b.get("cost_rr"):
        parts.append(f"{b['cost_rr']} RR")
    return " + ".join(parts) if parts else "0"


# =============================================================================
#  UTILIDADES
# =============================================================================
def clamp(v, lo, hi):
    return max(lo, min(hi, v))


def darker(c, f=0.6):
    return tuple(int(x * f) for x in c[:3])


def lighter(c, t=0.35):
    return tuple(int(x + (255 - x) * t) for x in c[:3])


def quad_label(col: int, row: int) -> str:
    return f"{chr(65 + col)}{row + 1}"


def safe_filename(name: str) -> str:
    s = re.sub(r"[^\w\- \[\]]", "_", name.strip(), flags=re.UNICODE).strip()
    return s or "campaign"


def campaign_tag(code: str) -> str:
    return CAMPAIGN_TAGS.get(code, "Gen")


def compose_campaign_name(code: str, base: str) -> str:
    """Construye el nombre con el formato obligatorio «[Tipo] nombre»."""
    base = " ".join((base or "").split())[:40] or tr("dlg.default_name")
    return f"[{campaign_tag(code)}] {base}"


def valid_campaign_name(name: str) -> bool:
    return bool(_NAME_RE.match(name or ""))


def split_campaign_name(name: str) -> Tuple[str, str]:
    """Devuelve (código de tipo, nombre base); si no cumple el formato asume GEN."""
    m = _NAME_RE.match(name or "")
    if not m:
        return "GEN", " ".join((name or "").split()) or tr("dlg.default_name")
    code = next((c for c, t in CAMPAIGN_TAGS.items() if t == m.group(1)), "GEN")
    return code, m.group(2)


def _mk(cls, d: dict):
    """Construye un dataclass ignorando claves desconocidas (compatibilidad)."""
    names = {f.name for f in fields(cls)}
    return cls(**{k: v for k, v in d.items() if k in names})


def get_clipboard_text() -> str:
    """Lee texto del portapapeles probando varios métodos (pygame, tkinter, comandos del SO)."""
    try:
        scrap = pygame.scrap
        if not scrap.get_init():
            scrap.init()
        if hasattr(scrap, "get_text"):
            t = scrap.get_text()
            if t:
                return str(t)
        for kind in ("text/plain;charset=utf-8", getattr(pygame, "SCRAP_TEXT", "text/plain"), "text/plain"):
            data = scrap.get(kind)
            if data:
                return data.decode("utf-8", "ignore").replace("\x00", "")
    except Exception:
        pass
    if sys.platform != "darwin":
        try:
            import tkinter
            root = tkinter.Tk()
            root.withdraw()
            txt = root.clipboard_get()
            root.destroy()
            if txt:
                return txt
        except Exception:
            pass
    cmds = []
    if sys.platform == "darwin":
        cmds = [["pbpaste"]]
    elif sys.platform.startswith("win"):
        cmds = [["powershell", "-command", "Get-Clipboard"]]
    else:
        cmds = [["wl-paste", "-n"], ["xclip", "-selection", "clipboard", "-o"],
                ["xsel", "-b", "-o"]]
    for cmd in cmds:
        try:
            out = subprocess.run(cmd, capture_output=True, timeout=3)
            if out.returncode == 0 and out.stdout:
                return out.stdout.decode("utf-8", "ignore")
        except Exception:
            continue
    return ""


# =============================================================================
#  LISTAS DE EJÉRCITO: modelo + importación desde Army Forge
# =============================================================================
@dataclass
class ArmyUnit:
    name: str = "Unit"
    size: int = 1
    quality: int = 4
    defense: int = 4
    pts: int = 0
    rr_cost: int = 0
    rules: str = ""
    weapons: str = ""
    upgrades: str = ""          # mejoras (importadas de Army Forge)
    notes: str = ""             # notas libres del jugador
    status: str = "reserve"     # reserve (inicial) | active | fallen (dañada) | destroyed
    force: int = 0              # (heredado v4: las unidades ahora viven dentro de cada Force)
    xp: int = 0                 # experiencia acumulada
    spent: int = 0              # puntos de avance ya gastados
    advances: List[str] = field(default_factory=list)   # avances obtenidos
    unpaid: int = 0             # turnos seguidos sin pagar mantenimiento


def default_rr(pts: int, pts_per_rr: int) -> int:
    return max(1, int(round(pts / max(1, pts_per_rr)))) if pts > 0 else 0


def normalize_system(s: str) -> str:
    """Convierte «GF», «Age of Fantasy», «firefight»... en un código de SYSTEMS (o GEN)."""
    key = re.sub(r"[^a-z]", "", (s or "").lower())
    return _SYS_ALIASES.get(key, "GEN")


def sys_info(code: str) -> str:
    p = SYSTEMS.get(code, SYSTEMS["GEN"])
    parts = []
    if p["pts"]:
        parts.append(tr("sys.i_pts", n=p["pts"]))
    if p["pct"]:
        parts.append(tr("sys.i_pct", n=p["pct"]))
    if p["per"]:
        parts.append(tr("sys.i_per", n=p["per"]))
    w, h = BOARD_SIZES[p["board"]]
    parts.append(tr("sys.i_board", w=w, h=h))
    if p["terrain"]:
        parts.append(tr("sys.i_terrain", n=p["terrain"]))
    return f"{tr('sys.' + code)} — " + "; ".join(parts) + ". " + tr("sys.note")


def rank_of(xp: int) -> int:
    return max(i for i, t in enumerate(RANK_XP) if xp >= t)


def rank_name(i: int) -> str:
    return tr(f"rank.{clamp(i, 0, len(RANK_XP) - 1)}")


def ap_available(u: "ArmyUnit") -> int:
    return max(0, rank_of(u.xp) - u.spent)


def can_advance(u: "ArmyUnit", key: str) -> bool:
    if ap_available(u) <= 0:
        return False
    if key == "quality" and u.quality <= 2:
        return False
    if key == "defense" and u.defense <= 2:
        return False
    return u.advances.count(key) < ADV_MAX.get(key, 1)


def apply_advance(u: "ArmyUnit", key: str) -> bool:
    if not can_advance(u, key):
        return False
    if key == "quality":
        u.quality -= 1
    elif key == "defense":
        u.defense -= 1
    elif key in ADV_RULES and ADV_RULES[key].lower() not in u.rules.lower():
        u.rules = _append(u.rules, ADV_RULES[key])
    u.advances.append(key)
    u.spent += 1
    return True


def undo_advance(u: "ArmyUnit") -> bool:
    if not u.advances:
        return False
    key = u.advances.pop()
    u.spent = max(0, u.spent - 1)
    if key == "quality":
        u.quality = min(6, u.quality + 1)
    elif key == "defense":
        u.defense = min(6, u.defense + 1)
    elif key in ADV_RULES:
        parts = [p for p in _split_top(u.rules) if p.lower() != ADV_RULES[key].lower()]
        u.rules = ", ".join(parts)
    return True


def adv_summary(u: "ArmyUnit") -> str:
    seen = []
    for k in u.advances:
        n = u.advances.count(k)
        txt = tr("adv." + k) + (f" x{n}" if n > 1 else "")
        if txt not in seen:
            seen.append(txt)
    return ", ".join(seen)


def army_warnings(army, system: str) -> List[str]:
    """Advertencias orientativas de una lista (army = Force) según el sistema OPR."""
    p = SYSTEMS.get(system, SYSTEMS["GEN"])
    counted = [u for u in army.units if u.status in ("active", "fallen")]
    total = sum(u.pts for u in counted)
    lim = army.points_limit
    out = []
    if lim and total > lim:
        out.append(tr("army.w_limit", t=total, l=lim))
    if lim and p["pct"]:
        cap = lim * p["pct"] / 100.0
        for u in counted:
            if u.pts > cap:
                out.append(tr("army.w_pct", u=u.name, p=u.pts, pct=p["pct"], m=int(cap)))
    if lim and p["per"]:
        mx = max(1, lim // p["per"])
        if len(counted) > mx:
            out.append(tr("army.w_units", n=len(counted), m=mx, per=p["per"]))
    return out


def _split_top(s: str, sep: str = ",") -> List[str]:
    """Divide por separador ignorando los que están dentro de paréntesis."""
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth = max(0, depth - 1)
        if ch == sep and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return [x for x in out if x]


_RE_HEADER = re.compile(r"^\s*\+\+\s*(?P<name>.*?)\s*(?:\[(?P<info>[^\]]*)\])?\s*\+\+\s*$")
_RE_UNIT = re.compile(
    r"^\s*(?P<name>.+?)\s*\[(?P<size>\d+)\]\s*Q\s*(?P<q>\d)\s*\+?\s*D\s*(?P<d>\d)\s*\+?\s*"
    r"\|\s*(?P<pts>\d+)\s*pts?\s*(?:\|(?P<rest>.*))?$", re.IGNORECASE)
_RE_WEAPON = re.compile(r"^\d+x\s|\(.*\bA\d+", re.IGNORECASE)
_RE_UPG_LINE = re.compile(r"^(upgrades?|mejoras?|options?|opciones)\s*[:\-]\s*(.*)$", re.IGNORECASE)
_RE_JOINED = re.compile(r"^#?\s*joined\s+to\s*:?\s*(.*)$", re.IGNORECASE)


def _append(cur: str, item: str) -> str:
    item = item.strip()
    if not item:
        return cur
    return f"{cur}, {item}" if cur else item


def _split_items(s: str) -> List[str]:
    # separa "Strider 4x CCWs (A1)" en "Strider, 4x CCWs (A1)"
    s = re.sub(r"(?<=[\w\)])\s+(?=\d+x\s)", ", ", s)
    return _split_top(s)


def _add_continuation(u: "ArmyUnit", line: str):
    """Línea posterior a una unidad: armas -> armas; resto (mejoras, unidad unida) -> mejoras."""
    s = line.strip()
    m = _RE_JOINED.match(s)
    if m:
        u.upgrades = _append(u.upgrades, "Joined to: " + m.group(1).strip())
        return
    m = _RE_UPG_LINE.match(s)
    if m:
        for it in _split_top(m.group(2)):
            u.upgrades = _append(u.upgrades, it)
        return
    s = re.sub(r"^[\-\+\*•·]\s*", "", s)
    for it in _split_items(s):
        if _RE_WEAPON.search(it):
            u.weapons = _append(u.weapons, it)
        else:
            u.upgrades = _append(u.upgrades, it)


def parse_army_text(text: str) -> dict:
    """
    Parser del texto exportado por Army Forge, por ejemplo:
      ++ 123rd Valhallan [GF 795pts] ++
      516th Conscripted [10] Q6+ D5+ | 80pts | 1XP | Hero, Tough(3)
      10x CCWs (A1), 10x Rifles (24", A1)          <- armas (línea siguiente)
      Upgrades: Jetpack                             <- mejoras
      # Joined to: Eternals                         <- unidad unida (a mejoras)
    El campo «notas» queda vacío: es para las anotaciones del jugador.
    """
    res = {"name": "", "system": "", "units": [], "list_pts": 0}
    last = None
    for raw in text.splitlines():
        line = raw.strip()
        if not line:
            continue
        m = _RE_HEADER.match(line)
        if m:
            res["name"] = m.group("name").strip()
            info = (m.group("info") or "").strip()
            sm = re.match(r"(?:([A-Za-z][A-Za-z ]*?)\s*)?(\d+)\s*pts?", info, re.IGNORECASE)
            if sm:
                res["system"] = (sm.group(1) or "").strip()
                res["list_pts"] = int(sm.group(2))
            continue
        m = _RE_UNIT.match(line)
        if m:
            rest = (m.group("rest") or "").strip()
            body, xp = [], 0
            for part in rest.split("|"):
                part = part.strip()
                mx = re.fullmatch(r"(\d+)\s*XP", part, re.IGNORECASE)
                if mx:
                    xp = int(mx.group(1))
                elif part:
                    body.append(part)
            rules, weapons = [], []
            for item in _split_items(", ".join(body)):
                (weapons if _RE_WEAPON.search(item) else rules).append(item)
            last = ArmyUnit(name=m.group("name").strip(), size=int(m.group("size")),
                            quality=int(m.group("q")), defense=int(m.group("d")),
                            pts=int(m.group("pts")), rules=", ".join(rules),
                            weapons=", ".join(weapons), xp=xp)
            res["units"].append(last)
        elif last is not None and not line.startswith("++"):
            _add_continuation(last, line)
    return res


def _to_int(v, default=0) -> int:
    if isinstance(v, bool):
        return default
    if isinstance(v, (int, float)):
        return int(v)
    m = re.search(r"\d+", str(v))
    return int(m.group()) if m else default


def _fmt_rule(r) -> str:
    if isinstance(r, str):
        return r
    if isinstance(r, dict):
        name = r.get("label") or r.get("name") or r.get("key") or ""
        rating = r.get("rating")
        return f"{name}({rating})" if rating not in (None, "", 0) and name else str(name)
    return str(r)


def _fmt_weapon(w) -> str:
    if isinstance(w, str):
        return w
    if not isinstance(w, dict):
        return str(w)
    name = w.get("label") or w.get("name") or "?"
    cnt = _to_int(w.get("count", w.get("quantity", 1)), 1)
    inner = []
    rng = w.get("range")
    if rng not in (None, "", 0, "-"):
        inner.append(f"{rng}\"")
    att = w.get("attacks")
    if att not in (None, ""):
        inner.append(f"A{att}")
    sr = w.get("specialRules") or w.get("rules") or []
    if isinstance(sr, list):
        inner.extend(_fmt_rule(x) for x in sr)
    txt = f"{cnt}x {name}" if cnt > 1 else name
    return f"{txt} ({', '.join(inner)})" if inner else txt


def _num(v) -> Optional[float]:
    if isinstance(v, bool):
        return None
    if isinstance(v, (int, float)):
        return float(v)
    return None


def _entry_cost(e, uid) -> float:
    """Coste de una mejora seleccionada (tolera varias estructuras de Army Forge)."""
    if not isinstance(e, dict):
        return 0.0
    cnt = _num(e.get("count", e.get("quantity", e.get("qty")))) or 1.0

    def pick(d):
        if not isinstance(d, dict):
            return None
        c = _num(d.get("cost"))
        if c is not None:
            return c
        cs = d.get("costs")
        if isinstance(cs, list):
            for it in cs:
                if isinstance(it, dict) and uid is not None and uid in (it.get("unitId"), it.get("id")):
                    return _num(it.get("cost"))
            for it in cs:
                if isinstance(it, dict) and _num(it.get("cost")) is not None:
                    return _num(it.get("cost"))
        return None

    for d in (e.get("option"), e.get("selected"), e):
        v = pick(d)
        if v is not None:
            return v * cnt
    return 0.0


def _upgrade_label(e) -> str:
    if isinstance(e, dict):
        for d in (e.get("option"), e.get("selected"), e):
            if isinstance(d, dict):
                lab = d.get("label") or d.get("name")
                if lab:
                    return str(lab)
        return ""
    return str(e)


def parse_army_json(data) -> dict:
    """
    Parser tolerante para JSON de Army Forge. Busca la lista de unidades en cualquier nivel.
    El coste de cada unidad incluye las mejoras seleccionadas; si la lista trae su total
    de puntos, se usa para decidir si «cost» ya incluía las mejoras o solo era el coste base.
    """
    best, best_score = None, -1
    stack = [data]
    while stack:
        o = stack.pop()
        if isinstance(o, list):
            dicts = [x for x in o if isinstance(x, dict)]
            unitish = [x for x in dicts if ("name" in x or "customName" in x) and
                       any(k in x for k in ("quality", "defense", "cost", "points", "pts"))]
            if unitish and len(unitish) >= max(1, len(dicts) // 2):
                score = sum(1 for x in unitish if "quality" in x or "defense" in x) * 1000 + len(unitish)
                if score > best_score:
                    best, best_score = unitish, score
            stack.extend(o)
        elif isinstance(o, dict):
            stack.extend(o.values())
    res = {"name": "", "system": "", "units": [], "list_pts": 0}
    if isinstance(data, dict):
        res["name"] = str(data.get("name") or data.get("listName") or data.get("armyName") or "")
        res["system"] = str(data.get("gameSystem") or data.get("system") or "")[:12]
        for k in ("points", "totalPoints", "listPoints", "pointsTotal"):
            v = _num(data.get(k))
            if v:
                res["list_pts"] = int(v)
                break
    rows = []
    for u in best or []:
        uid = u.get("id") if u.get("id") is not None else u.get("selectionId")
        rules = u.get("specialRules") or u.get("rules") or u.get("abilities") or []
        weapons = u.get("loadout") or u.get("weapons") or u.get("equipment") or []
        ups = u.get("selectedUpgrades") or u.get("upgrades") or u.get("selectedOptions") or []
        if not isinstance(ups, list):
            ups = []
        base = _to_int(u.get("cost", u.get("points", u.get("pts", 0))))
        explicit = None
        for k in ("totalCost", "costTotal", "unitCost", "pointsTotal", "total"):
            v = _num(u.get(k))
            if v:
                explicit = int(v)
                break
        extra = int(round(sum(_entry_cost(e, uid) for e in ups)))
        rl = ", ".join(_fmt_rule(r) for r in rules) if isinstance(rules, list) else str(rules)
        wl = ", ".join(_fmt_weapon(w) for w in weapons) if isinstance(weapons, list) else str(weapons)
        names = [n for n in (_upgrade_label(x) for x in ups) if n]
        unit = ArmyUnit(
            name=str(u.get("customName") or u.get("name") or "Unit"),
            size=max(1, _to_int(u.get("size", u.get("models", 1)), 1)),
            quality=clamp(_to_int(u.get("quality", 4), 4), 2, 6),
            defense=clamp(_to_int(u.get("defense", 4), 4), 2, 6),
            rules=rl, weapons=wl, upgrades=", ".join(names)[:400],
            xp=max(0, _to_int(u.get("xp", 0))))
        rows.append((unit, base, extra, explicit))
    sum_base = sum((r[3] if r[3] else r[1]) for r in rows)
    sum_full = sum((r[3] if r[3] else r[1] + r[2]) for r in rows)
    use_full = sum_full != sum_base
    if res["list_pts"] and use_full:      # el total de la lista decide qué interpretación es la buena
        use_full = abs(sum_full - res["list_pts"]) <= abs(sum_base - res["list_pts"])
    for unit, base, extra, explicit in rows:
        unit.pts = explicit if explicit else (base + extra if use_full else base)
        res["units"].append(unit)
    return res


def parse_any(text: str) -> dict:
    """Detecta JSON o texto de Army Forge y devuelve {name, system, units}."""
    s = text.strip()
    if not s:
        raise ValueError("empty")
    res = None
    if s[0] in "{[":
        try:
            res = parse_army_json(json.loads(s))
        except json.JSONDecodeError:
            res = None
    if res is None or not res["units"]:
        res = parse_army_text(s)
    if not res["units"]:
        raise ValueError("0 units")
    return res


def extract_list_id(src: str) -> Optional[str]:
    src = src.strip()
    if "://" in src:
        q = urllib.parse.parse_qs(urllib.parse.urlparse(src).query)
        return (q.get("id") or [None])[0]
    return src if re.fullmatch(r"[\w\-]{5,40}", src) else None


class ArmyFetcher:
    """Descarga una lista compartida de Army Forge en un hilo (no bloquea la interfaz)."""

    def __init__(self):
        self.busy = False
        self.result: Optional[dict] = None
        self.error: Optional[str] = None

    def start(self, src: str):
        if self.busy:
            return
        self.busy, self.result, self.error = True, None, None
        threading.Thread(target=self._run, args=(src,), daemon=True).start()

    def _run(self, src: str):
        try:
            list_id = extract_list_id(src)
            if not list_id:
                raise ValueError("invalid link/ID")
            req = urllib.request.Request(
                ARMY_FORGE_API + urllib.parse.quote(list_id),
                headers={"User-Agent": "Mozilla/5.0 (OPR Campaign Manager)",
                         "Accept": "application/json"})
            with urllib.request.urlopen(req, timeout=15) as r:
                raw = r.read().decode("utf-8", "replace")
            res = parse_any(raw)
            res["source"] = src
            self.result = res
        except Exception as ex:  # noqa
            self.error = str(ex)[:120]
        finally:
            self.busy = False

    def take(self) -> Tuple[Optional[dict], Optional[str]]:
        if self.busy:
            return None, None
        r, e = self.result, self.error
        self.result = self.error = None
        return r, e


# =============================================================================
#  BASE DE DATOS OPR LOCAL (Army Forge): descarga, caché en disco y normalización
# =============================================================================
def _http_json(url: str, timeout: int = 20):
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (OPR Campaign Manager)",
                                               "Accept": "application/json"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.loads(r.read().decode("utf-8", "replace"))


def _list_urls(code: str) -> List[str]:
    slug, gid = SYSTEM_SLUGS[code], SYSTEM_IDS.get(code)
    urls = [f"{AF_BASE}/api/army-books?filters=official&gameSystemSlug={slug}&searchText=&page=1"
            f"&unitCount=1000&balanceValid=false&customRules=true&cacheBuster={int(time.time())}"]
    if gid:
        urls.append(f"{AF_BASE}/api/army-books?gameSystem={gid}")
    urls.append(f"{AF_BASE}/api/army-books?gameSystemSlug={slug}")
    return urls


def parse_book_list(data) -> List[dict]:
    """Normaliza la respuesta de la lista de libros: [{uid, name, gs, version}]."""
    items = data
    if isinstance(data, dict):
        items = next((data[k] for k in ("data", "armyBooks", "books", "items", "results")
                      if isinstance(data.get(k), list)), [])
    out = []
    for it in items if isinstance(items, list) else []:
        if isinstance(it, dict):
            uid, name = it.get("uid") or it.get("id"), it.get("name")
            if uid and name:
                out.append(dict(uid=str(uid), name=str(name), gs=it.get("gameSystem"),
                                version=str(it.get("versionString") or it.get("version") or "")))
    return sorted(out, key=lambda b: b["name"].lower())


def normalize_book(raw: dict, code: str = "GEN") -> dict:
    """
    Convierte el JSON de un libro de ejército de Army Forge en una estructura simple:
      {uid, name, version, system, units:[{id,name,size,cost,quality,defense,rules,weapons,upgrades}],
       packages:{uid:[{label,mode,select,options:[{label,cost,weapons,rules}]}]}, rules:{nombre:desc}}
    El parser es tolerante: si Army Forge cambia algún campo, lo que no reconoce se ignora.
    """
    rules_desc = {}
    for r in raw.get("specialRules") or []:
        if isinstance(r, dict) and r.get("name"):
            rules_desc[str(r["name"])] = str(r.get("description") or "")
    packages: Dict[str, list] = {}
    for p in raw.get("upgradePackages") or []:
        if not isinstance(p, dict):
            continue
        puid = str(p.get("uid") or p.get("id") or len(packages))
        secs = []
        for s in p.get("sections") or []:
            if not isinstance(s, dict):
                continue
            label = str(s.get("label") or s.get("name") or "")
            low = label.lower()
            opts = []
            for o in s.get("options") or []:
                if not isinstance(o, dict):
                    continue
                weapons, rules, others = [], [], []
                for g in o.get("gains") or []:
                    if isinstance(g, dict):
                        gt = str(g.get("type") or "").lower()
                        if "weapon" in gt or "attacks" in g:
                            weapons.append(_fmt_weapon(g))
                        elif "rule" in gt or g.get("rating") is not None:
                            rules.append(_fmt_rule(g))
                        else:
                            others.append(str(g.get("label") or g.get("name") or ""))
                    elif g:
                        others.append(str(g))
                lab = o.get("label") or next(iter(weapons + rules + [x for x in others if x]), "?")
                cost = _num(o.get("cost"))
                if cost is None and isinstance(o.get("costs"), list):
                    cost = next((_num(c.get("cost")) for c in o["costs"] if isinstance(c, dict)
                                 and _num(c.get("cost")) is not None), None)
                opts.append(dict(label=str(lab), cost=int(cost or 0), weapons=weapons,
                                 rules=rules + [x for x in others if x]))
            secs.append(dict(label=label, mode="replace" if low.startswith("replace") else "upgrade",
                             select=1 if (re.search(r"\bone\b", low) and "any" not in low) else 0,
                             options=opts))
        packages[puid] = secs
    units = []
    for i, u in enumerate(raw.get("units") or []):
        if not isinstance(u, dict):
            continue
        ups = []
        for x in u.get("upgrades") or []:
            ups.append(str(x.get("uid") or x.get("id")) if isinstance(x, dict) else str(x))
        rl = u.get("specialRules") or u.get("rules") or []
        wl = u.get("weapons") or u.get("equipment") or u.get("loadout") or []
        units.append(dict(
            id=str(u.get("id") or i), name=str(u.get("name") or "Unit"),
            size=max(1, _to_int(u.get("size", 1), 1)), cost=_to_int(u.get("cost", u.get("points", 0))),
            quality=clamp(_to_int(u.get("quality", 4), 4), 2, 6),
            defense=clamp(_to_int(u.get("defense", 4), 4), 2, 6),
            rules=[_fmt_rule(r) for r in rl] if isinstance(rl, list) else [str(rl)],
            weapons=[_fmt_weapon(w) for w in wl] if isinstance(wl, list) else [str(wl)],
            upgrades=[x for x in ups if x in packages]))
    return dict(uid=str(raw.get("uid") or raw.get("id") or ""), name=str(raw.get("name") or ""),
                version=str(raw.get("versionString") or raw.get("version") or ""),
                system=code, units=units, packages=packages, rules=rules_desc)


def catalog_sections(book: dict, unit: dict) -> List[tuple]:
    """Secciones de mejora aplicables a una unidad: [((paquete, índice), sección)]."""
    out = []
    for puid in unit.get("upgrades", []):
        for si, sec in enumerate(book["packages"].get(puid, [])):
            if sec["options"]:
                out.append(((puid, si), sec))
    return out


def catalog_cost(book: dict, unit: dict, selection: Dict[tuple, set]) -> int:
    total = unit["cost"]
    for key, sec in catalog_sections(book, unit):
        for oi in selection.get(key, ()):
            if oi < len(sec["options"]):
                total += sec["options"][oi]["cost"]
    return total


def catalog_to_unit(book: dict, unit: dict, selection: Dict[tuple, set], pts_per_rr: int) -> "ArmyUnit":
    """Crea un ArmyUnit (en reserva) a partir de una unidad del catálogo y sus mejoras elegidas."""
    rules, weapons, ups = list(unit["rules"]), list(unit["weapons"]), []
    for key, sec in catalog_sections(book, unit):
        for oi in sorted(selection.get(key, ())):
            if oi >= len(sec["options"]):
                continue
            opt = sec["options"][oi]
            if sec["mode"] == "replace":
                target = re.sub(r"^replace\s+(all|one|any|up to \d+)?\s*", "", sec["label"].lower()).rstrip(": ")
                target = target.split("(")[0].strip()
                if target:
                    weapons = [w for w in weapons if target not in w.lower()]
            weapons += opt["weapons"]
            rules += opt["rules"]
            ups.append(opt["label"])
    pts = catalog_cost(book, unit, selection)
    return ArmyUnit(name=unit["name"], size=unit["size"], quality=unit["quality"], defense=unit["defense"],
                    pts=pts, rr_cost=default_rr(pts, pts_per_rr), rules=", ".join(rules),
                    weapons=", ".join(weapons), upgrades=", ".join(ups), status="reserve")


class OprDB:
    """Caché local de facciones y libros de Army Forge (carpeta opr_db/) con descargas en segundo plano."""

    def __init__(self, folder: Optional[str] = None):
        self.dir = folder or OPR_DB_DIR
        self.lists: Dict[str, List[dict]] = {}
        self.books: Dict[str, dict] = {}
        self.busy = False
        self.msg = ""
        self.err = False

    # ---- disco -------------------------------------------------------------
    def _read(self, name: str):
        try:
            with open(os.path.join(self.dir, name), "r", encoding="utf-8") as fh:
                return json.load(fh)
        except Exception:
            return None

    def _write(self, name: str, data):
        os.makedirs(self.dir, exist_ok=True)
        with open(os.path.join(self.dir, name), "w", encoding="utf-8") as fh:
            json.dump(data, fh, ensure_ascii=False)

    def _local_metas(self, code: str) -> List[dict]:
        out = []
        try:
            for fn in sorted(os.listdir(self.dir)):
                if fn.startswith(code + "__") and fn.lower().endswith(".json"):
                    raw = self._read(fn)
                    if isinstance(raw, dict) and raw.get("units"):
                        out.append(dict(uid="file:" + fn, name=str(raw.get("name") or fn[len(code) + 2:-5]),
                                        gs=None, version=str(raw.get("versionString") or "local")))
        except OSError:
            pass
        return out

    # ---- consulta ------------------------------------------------------------
    def book_list(self, code: str) -> List[dict]:
        if code not in self.lists:
            data = self._read(f"list_{code}.json")
            metas = parse_book_list(data) if data is not None else []
            seen = {m["uid"] for m in metas}
            metas += [m for m in self._local_metas(code) if m["uid"] not in seen]
            self.lists[code] = metas
        return self.lists[code]

    def get_book(self, uid: str, code: str) -> Optional[dict]:
        if uid in self.books:
            return self.books[uid]
        raw = self._read(uid[5:]) if uid.startswith("file:") else self._read(f"book_{uid}.json")
        if isinstance(raw, dict) and raw.get("units") is not None:
            self.books[uid] = normalize_book(raw, code)
            return self.books[uid]
        return None

    # ---- descargas (hilos) ---------------------------------------------------
    def request_list(self, code: str):
        if self.busy or code not in SYSTEM_SLUGS:
            return
        self.busy, self.err, self.msg = True, False, tr("opr.downloading_list")
        threading.Thread(target=self._job_list, args=(code,), daemon=True).start()

    def _job_list(self, code: str):
        errors = []
        try:
            for url in _list_urls(code):
                try:
                    data = _http_json(url)
                    metas = parse_book_list(data)
                    if metas:
                        self._write(f"list_{code}.json", data)
                        self.lists.pop(code, None)
                        self.msg, self.err = tr("opr.list_ok", n=len(metas)), False
                        return
                    errors.append("empty")
                except urllib.error.HTTPError as ex:
                    errors.append(f"HTTP {ex.code}")
                except Exception as ex:  # noqa
                    errors.append(str(ex)[:50])
            self.msg, self.err = tr("opr.list_fail", err="; ".join(errors[-2:])), True
        finally:
            self.busy = False

    def request_book(self, meta_uid: str, code: str, gs=None):
        if self.busy or meta_uid.startswith("file:"):
            return
        self.busy, self.err, self.msg = True, False, tr("opr.downloading_book")
        threading.Thread(target=self._job_book, args=(meta_uid, code, gs), daemon=True).start()

    def _job_book(self, uid: str, code: str, gs):
        try:
            gid = gs if isinstance(gs, int) else SYSTEM_IDS.get(code, 2)
            raw = _http_json(f"{AF_BASE}/api/army-books/{urllib.parse.quote(uid)}?gameSystem={gid}", 30)
            if not isinstance(raw, dict) or not raw.get("units"):
                raise ValueError("no units in response")
            self._write(f"book_{uid}.json", raw)
            self.books.pop(uid, None)
            self.msg, self.err = tr("opr.book_ok", n=len(raw["units"])), False
        except urllib.error.HTTPError as ex:
            self.msg, self.err = tr("opr.book_fail", err=f"HTTP {ex.code}"), True
        except Exception as ex:  # noqa
            self.msg, self.err = tr("opr.book_fail", err=str(ex)[:60]), True
        finally:
            self.busy = False


# =============================================================================
#  MODELO DE DATOS: CAMPAÑA
# =============================================================================
@dataclass
class Force:
    """Ficha móvil de una facción con SU PROPIO ejército (lista de unidades independiente)."""
    name: str = ""
    col: int = 0
    row: int = 0
    moved: bool = False        # ya se movió este turno
    army_name: str = ""
    army_source: str = ""
    points_limit: int = 0      # 0 = sin límite
    units: List[ArmyUnit] = field(default_factory=list)

    def pts_total(self, status: Optional[str] = None) -> int:
        return sum(u.pts for u in self.units if status is None or u.status == status)

    def count(self, status: str) -> int:
        return sum(1 for u in self.units if u.status == status)


@dataclass
class BattleRecord:
    """Entrada del historial de combates de un territorio."""
    turn: int = 1
    date: str = ""
    att_fid: Optional[int] = None
    def_fid: Optional[int] = None
    att_name: str = ""
    def_name: str = ""
    winner: str = "draw"       # att | def | draw
    att_losses: int = 0        # unidades caídas o destruidas
    def_losses: int = 0
    att_destroyed: int = 0     # de ellas, destruidas (irrecuperables)
    def_destroyed: int = 0
    note: str = ""


@dataclass
class Clash:
    """Combate pendiente generado al atacar un territorio con fuerzas enemigas."""
    col: int
    row: int
    att_fid: int
    att_force: int
    def_fid: int
    def_force: int
    turn: int = 1


@dataclass
class Faction:
    fid: int
    name: str
    color_idx: int = 0
    cr: int = START_CR           # recursos de campaña (economía común de la facción)
    rr: int = START_RR           # recursos de reclutamiento
    army_name: str = ""          # (heredado v4; se migra a la primera fuerza)
    army_system: str = "GEN"     # código de SYSTEMS
    army_source: str = ""        # (heredado)
    points_limit: int = 0        # (heredado)
    units: List[ArmyUnit] = field(default_factory=list)      # (heredado: se migra a las fuerzas)
    forces: List[Force] = field(default_factory=list)
    capital: Optional[List[int]] = None     # [col, row] = base principal / casilla de salida
    opr_faction: Optional[dict] = None      # {uid, name, system, gs} de Army Forge

    @property
    def color(self):
        return FACTION_COLORS[self.color_idx % len(FACTION_COLORS)]

    def all_units(self) -> List[ArmyUnit]:
        return [u for fc in self.forces for u in fc.units]

    def pts_total(self, status: Optional[str] = None) -> int:
        return sum(u.pts for u in self.all_units() if status is None or u.status == status)

    def fallen(self) -> int:
        return sum(1 for u in self.all_units() if u.status == "fallen")


@dataclass
class Quadrant:
    col: int
    row: int
    name: str
    biome: int = 0
    owner: Optional[int] = None
    buildings: List[str] = field(default_factory=list)
    history: List[BattleRecord] = field(default_factory=list)


class Campaign:
    """Campaña completa: tipo/sistema, facciones (con sus ejércitos), mapa, rutas, turno y registro."""

    def __init__(self, system: str = "GEN", base_name: Optional[str] = None):
        self.system = system if system in CAMPAIGN_TYPES else "GEN"
        self.name = compose_campaign_name(self.system, base_name or tr("dlg.default_name"))
        self.factions: List[Faction] = []
        self.next_fid = 1
        self.quads: List[Quadrant] = []
        self.cols = self.rows = 5
        self.seed = 1
        self.turn = 1
        self.max_buildings = 0          # 0 = sin límite
        self.pts_per_rr = 25
        self.logistics = True
        self.routes: List[List[int]] = []       # [c1, r1, c2, r2, fid]
        self.clashes: List[Clash] = []
        self.log: List[str] = []
        self.add_faction()
        self.add_faction()
        self.generate(5)

    # ---- tipo de campaña ----------------------------------------------------
    def set_system(self, code: str):
        """Cambia el tipo; si no es «Gen» fija el sistema de todas las facciones."""
        if code not in CAMPAIGN_TYPES:
            return
        self.system = code
        _c, base = split_campaign_name(self.name)
        self.name = compose_campaign_name(code, base)
        if code != "GEN":
            for f in self.factions:
                f.army_system = code
                if f.opr_faction and f.opr_faction.get("system") != code:
                    f.opr_faction = None

    def rename(self, code: str, base: str):
        self.set_system(code)
        self.name = compose_campaign_name(code, base)

    # ---- facciones --------------------------------------------------------
    def add_faction(self) -> Optional[Faction]:
        if len(self.factions) >= 6:
            return None
        used = {f.color_idx for f in self.factions}
        cidx = next((i for i in range(len(FACTION_COLORS)) if i not in used), 0)
        names = DEFAULT_FACTION_NAMES.get(LANG, DEFAULT_FACTION_NAMES["es"])
        f = Faction(self.next_fid, names[(self.next_fid - 1) % len(names)], cidx,
                    army_system=self.system)
        self.next_fid += 1
        self.factions.append(f)
        return f

    def remove_faction(self, fid: int):
        self.factions = [f for f in self.factions if f.fid != fid]
        self.clashes = [c for c in self.clashes if fid not in (c.att_fid, c.def_fid)]
        for q in self.quads:
            if q.owner == fid:
                q.owner = None
        self.prune_routes()

    def faction(self, fid: Optional[int]) -> Optional[Faction]:
        if fid is None:
            return None
        return next((f for f in self.factions if f.fid == fid), None)

    # ---- mapa y conectividad ---------------------------------------------
    def quad(self, col: int, row: int) -> Quadrant:
        return self.quads[row * self.cols + col]

    def in_bounds(self, c: int, r: int) -> bool:
        return 0 <= c < self.cols and 0 <= r < self.rows

    def has_route(self, c1, r1, c2, r2) -> bool:
        return any(rt[:4] in ([c1, r1, c2, r2], [c2, r2, c1, r1]) for rt in self.routes)

    def neighbors(self, c: int, r: int, fid: Optional[int] = None) -> List[Quadrant]:
        """Adyacentes (4 dir.) y, si se indica fid, también extremos de rutas de esa facción."""
        out: List[Quadrant] = []
        for dc, dr in ((1, 0), (-1, 0), (0, 1), (0, -1)):
            if self.in_bounds(c + dc, r + dr):
                out.append(self.quad(c + dc, r + dr))
        for rt in self.routes:
            if fid is not None and rt[4] != fid:
                continue
            if (rt[0], rt[1]) == (c, r):
                other = (rt[2], rt[3])
            elif (rt[2], rt[3]) == (c, r):
                other = (rt[0], rt[1])
            else:
                continue
            if self.in_bounds(*other):
                n = self.quad(*other)
                if all(n is not o for o in out):
                    out.append(n)
        return out

    # ---- rutas dinámicas ----------------------------------------------------
    def route_error(self, f: Faction, a: Tuple[int, int], b: Tuple[int, int]) -> Optional[str]:
        if not (self.in_bounds(*a) and self.in_bounds(*b)):
            return "err.route_own"
        if self.quad(*a).owner != f.fid or self.quad(*b).owner != f.fid:
            return "err.route_own"
        if a == b or abs(a[0] - b[0]) + abs(a[1] - b[1]) == 1:
            return "err.route_adjacent"
        if self.has_route(*a, *b):
            return "err.route_exists"
        if f.cr < ROUTE_COST_CR:
            return "err.route_funds"
        return None

    def build_route(self, f: Faction, a: Tuple[int, int], b: Tuple[int, int]) -> Optional[str]:
        err = self.route_error(f, a, b)
        if err:
            return err
        f.cr -= ROUTE_COST_CR
        self.routes.append([a[0], a[1], b[0], b[1], f.fid])
        self.log.append(tr("log.route_built", t=self.turn, f=f.name, a=quad_label(*a),
                           b=quad_label(*b), c=ROUTE_COST_CR))
        self.log = self.log[-60:]
        return None

    def prune_routes(self) -> int:
        """Destruye las rutas cuyos dos extremos ya no pertenecen a la facción que las construyó."""
        keep, lost = [], 0
        for rt in self.routes:
            ok = (len(rt) >= 5 and self.in_bounds(rt[0], rt[1]) and self.in_bounds(rt[2], rt[3])
                  and self.quad(rt[0], rt[1]).owner == rt[4] and self.quad(rt[2], rt[3]).owner == rt[4])
            if ok:
                keep.append(rt)
            else:
                lost += 1
                if len(rt) >= 4 and self.in_bounds(rt[0], rt[1]) and self.in_bounds(rt[2], rt[3]):
                    self.log.append(tr("log.route_lost", t=self.turn, a=quad_label(rt[0], rt[1]),
                                       b=quad_label(rt[2], rt[3])))
        if lost:
            self.routes = keep
            self.log = self.log[-60:]
        return lost

    # ---- suministro -----------------------------------------------------------
    def capital_of(self, f: Faction) -> Optional[Quadrant]:
        if f.capital and self.in_bounds(*f.capital):
            q = self.quad(*f.capital)
            if q.owner == f.fid:
                return q
        owned = [q for q in self.quads if q.owner == f.fid]
        for q in owned:
            if "barracks" in q.buildings:
                return q
        return owned[0] if owned else None

    def supply_network(self, fid: int) -> set:
        f = self.faction(fid)
        cap = self.capital_of(f) if f else None
        if cap is None:
            return set()
        seen = {(cap.col, cap.row)}
        stack = [cap]
        while stack:
            q = stack.pop()
            for n in self.neighbors(q.col, q.row, fid):
                if n.owner == fid and (n.col, n.row) not in seen:
                    seen.add((n.col, n.row))
                    stack.append(n)
        return seen

    def supply_map(self) -> Dict[int, set]:
        return {f.fid: self.supply_network(f.fid) for f in self.factions}

    def is_supplied(self, q: Quadrant) -> bool:
        if q.owner is None:
            return False
        if not self.logistics:
            return True
        return (q.col, q.row) in self.supply_network(q.owner)

    # ---- generación ---------------------------------------------------------
    def generate(self, n: Optional[int] = None, seed: Optional[int] = None):
        if n:
            self.cols = self.rows = n
        self.seed = seed if seed is not None else random.randint(1, 999999)
        rng = random.Random(self.seed)
        part_a, part_b = NAME_PARTS.get(LANG, NAME_PARTS["es"])
        self.quads = []
        grid = [[None] * self.cols for _ in range(self.rows)]
        used = set()
        for r in range(self.rows):
            for c in range(self.cols):
                if r > 0 and rng.random() < 0.35:
                    biome = grid[r - 1][c].biome
                elif c > 0 and rng.random() < 0.35:
                    biome = grid[r][c - 1].biome
                else:
                    biome = rng.randrange(len(BIOMES))
                name = ""
                for _ in range(30):
                    a, b = rng.choice(part_a), rng.choice(part_b)
                    name = f"{a} {b}" if LANG == "es" else f"{b} {a}"
                    if name not in used:
                        break
                used.add(name)
                q = Quadrant(c, r, name, biome)      # el mapa nace sin edificios ni rutas
                grid[r][c] = q
                self.quads.append(q)
        self.routes = []
        spawns = [(0, 0), (self.cols - 1, self.rows - 1), (self.cols - 1, 0),
                  (0, self.rows - 1), (self.cols // 2, 0), (self.cols // 2, self.rows - 1)]
        for i, f in enumerate(self.factions):
            c, r = spawns[i % len(spawns)]
            q = self.quad(c, r)
            q.owner = f.fid
            q.buildings = ["barracks"]
            f.capital = [c, r]
            if f.forces:                             # los ejércitos existentes vuelven a la base
                for fc in f.forces:
                    fc.col, fc.row, fc.moved = c, r, False
            else:
                f.forces = [Force(tr("force.name", n=1), c, r)]
        self.clashes = []
        self.turn = 1
        self.log = [tr("log.newmap", n=self.cols, seed=self.seed)]

    # ---- construcción -----------------------------------------------------
    def build_error(self, q: Quadrant, key: str) -> Optional[str]:
        owner = self.faction(q.owner)
        if owner is None:
            return "err.free"
        if self.logistics and not self.is_supplied(q):
            return "err.cutoff"
        if self.max_buildings and len(q.buildings) >= self.max_buildings:
            return "err.full"
        b = BUILDINGS[key]
        if owner.cr < b["cost_cr"] or owner.rr < b["cost_rr"]:
            return "err.funds"
        return None

    def build(self, q: Quadrant, key: str) -> Optional[str]:
        err = self.build_error(q, key)
        if err:
            return err
        owner = self.faction(q.owner)
        b = BUILDINGS[key]
        owner.cr -= b["cost_cr"]
        owner.rr -= b["cost_rr"]
        q.buildings.append(key)
        self.log.append(tr("log.build", t=self.turn, f=owner.name, b=bname(key),
                           q=quad_label(q.col, q.row), cost=cost_str(key)))
        self.log = self.log[-60:]
        return None

    # ---- ejércitos (fuerzas) -------------------------------------------------
    def forces_at(self, col: int, row: int) -> List[tuple]:
        """[(facción, índice de ejército, fuerza)] presentes en un territorio."""
        return [(f, i, fc) for f in self.factions for i, fc in enumerate(f.forces)
                if fc.col == col and fc.row == row]

    def force_create_error(self, f: Faction) -> Optional[str]:
        if len(f.forces) >= MAX_FORCES:
            return "err.force_max"
        if not (f.capital and self.in_bounds(*f.capital) and self.quad(*f.capital).owner == f.fid):
            return "err.force_base"
        if f.cr < FORCE_COST_CR:
            return "err.force_funds"
        return None

    def create_force(self, f: Faction) -> Optional[str]:
        """Crea un ejército nuevo: cuesta CR y solo aparece en la base principal."""
        err = self.force_create_error(f)
        if err:
            return err
        f.cr -= FORCE_COST_CR
        fc = Force(tr("force.name", n=len(f.forces) + 1), f.capital[0], f.capital[1])
        f.forces.append(fc)
        self.log.append(tr("log.force_new", t=self.turn, f=f.name, n=fc.name, c=FORCE_COST_CR))
        self.log = self.log[-60:]
        return None

    def force_remove_error(self, f: Faction, fi: int) -> Optional[str]:
        if fi <= 0 or fi >= len(f.forces) or f.forces[fi].units:
            return "err.force_remove"
        return None

    def remove_force(self, f: Faction, fi: int) -> Optional[str]:
        err = self.force_remove_error(f, fi)
        if err:
            return err
        f.forces.pop(fi)
        keep = []
        for c in self.clashes:
            if (c.att_fid == f.fid and c.att_force == fi) or (c.def_fid == f.fid and c.def_force == fi):
                continue
            if c.att_fid == f.fid and c.att_force > fi:
                c.att_force -= 1
            if c.def_fid == f.fid and c.def_force > fi:
                c.def_force -= 1
            keep.append(c)
        self.clashes = keep
        return None

    # ---- movimiento ---------------------------------------------------------
    def move_error(self, f: Faction, fi: int, dest: Quadrant) -> Optional[str]:
        if fi >= len(f.forces):
            return "err.no_force"
        fc = f.forces[fi]
        if fc.moved:
            return "err.moved"
        if not any(n is dest for n in self.neighbors(fc.col, fc.row, f.fid)):
            return "err.move_far"
        if dest.owner != f.fid and self.logistics:
            origin = self.quad(fc.col, fc.row)
            if origin.owner != f.fid or not self.is_supplied(origin):
                return "err.move_supply"
        return None

    def move_force(self, f: Faction, fi: int, dest: Quadrant) -> str:
        """Mueve un ejército. Devuelve 'moved', 'captured', 'clash' o una clave 'err.*'."""
        err = self.move_error(f, fi, dest)
        if err:
            return err
        fc = f.forces[fi]
        qn = quad_label(dest.col, dest.row)
        enemies = [(g, j) for g, j, _gf in self.forces_at(dest.col, dest.row) if g.fid != f.fid]
        fc.moved = True
        if enemies:
            g, j = enemies[0]
            if not any((c.col, c.row, c.att_fid, c.att_force) == (dest.col, dest.row, f.fid, fi)
                       for c in self.clashes):
                self.clashes.append(Clash(dest.col, dest.row, f.fid, fi, g.fid, j, self.turn))
            self.log.append(tr("log.clash", t=self.turn, a=f.name, d=g.name, q=qn))
            self.log = self.log[-60:]
            return "clash"
        fc.col, fc.row = dest.col, dest.row
        if dest.owner != f.fid:
            dest.owner = f.fid
            self.log.append(tr("log.capture", t=self.turn, f=f.name, n=fc.name, q=qn))
            self.prune_routes()
            res = "captured"
        else:
            self.log.append(tr("log.move", t=self.turn, f=f.name, n=fc.name, q=qn))
            res = "moved"
        self.log = self.log[-60:]
        return res

    def retreat(self, f: Faction, fi: int, from_q: Quadrant):
        if fi >= len(f.forces):
            return
        opts = [n for n in self.neighbors(from_q.col, from_q.row, f.fid)
                if n.owner == f.fid and not any(g.fid != f.fid for g, _i, _c in self.forces_at(n.col, n.row))]
        if not opts:
            cap = self.capital_of(f)
            if cap and (cap.col, cap.row) != (from_q.col, from_q.row):
                opts = [cap]
        if opts:
            f.forces[fi].col, f.forces[fi].row = opts[0].col, opts[0].row

    def participants(self, q: Quadrant, f: Faction, fi: Optional[int] = None) -> List[ArmyUnit]:
        """Unidades ACTIVAS que combaten: las del ejército indicado, las de los ejércitos de f en q,
        o (registro manual sin ejércitos presentes) todas las activas de la facción."""
        if fi is not None and fi < len(f.forces):
            return [u for u in f.forces[fi].units if u.status == "active"]
        idx = {i for g, i, _c in self.forces_at(q.col, q.row) if g is f}
        units = [u for i in sorted(idx) for u in f.forces[i].units if u.status == "active"]
        return units or [u for u in f.all_units() if u.status == "active"]

    # ---- reclutamiento y estados de unidad -------------------------------------
    def recruit_error(self, f: Faction, fi: int, u: ArmyUnit) -> Optional[str]:
        """Pasar de reserva a activa: ejército en territorio propio con Cuartel/Fortaleza y RR suficientes."""
        if fi >= len(f.forces):
            return "err.no_force"
        fc = f.forces[fi]
        q = self.quad(fc.col, fc.row)
        if q.owner != f.fid or not any(b in q.buildings for b in RECRUIT_BUILDINGS):
            return "err.recruit_loc"
        if f.rr < u.rr_cost:
            return "err.recruit_rr"
        return None

    def status_error(self, f: Faction, fi: int, u: ArmyUnit, new: str) -> Optional[str]:
        old = u.status
        if new == old:
            return None
        if old == "destroyed":
            return "err.status_destroyed"
        if old == "fallen":
            return "err.status_fallen" if new in ("active", "reserve") else None
        if old == "reserve":
            if new == "active":
                return self.recruit_error(f, fi, u)
            return None if new == "destroyed" else "err.status_no"
        return None                       # active -> reserve / fallen / destroyed

    def change_status(self, f: Faction, fi: int, u: ArmyUnit, new: str) -> Optional[str]:
        """Cambia el estado aplicando las reglas: reclutar cuesta RR; volver a reserva devuelve la mitad."""
        err = self.status_error(f, fi, u, new)
        if err:
            return err
        old = u.status
        if old == "reserve" and new == "active":
            f.rr -= u.rr_cost
        elif old == "active" and new == "reserve":
            f.rr += u.rr_cost // 2
        u.status = new
        u.unpaid = 0
        return None

    @staticmethod
    def unit_upkeep(u: ArmyUnit) -> int:
        return max(1, int(math.ceil(u.pts / UPKEEP_PTS_PER_CR))) if u.pts > 0 else 0

    def upkeep(self, f: Faction) -> int:
        return sum(self.unit_upkeep(u) for u in f.all_units() if u.status == "active")

    # ---- resultado de batalla / historial / XP -----------------------------
    def local_bonus(self, q: Quadrant) -> dict:
        """Bonos de Torre vigía (iniciativa) y Fortaleza (defensa): solo para batallas en este territorio."""
        if q.owner is None:
            return dict(ini=0, df=0)
        b = self.quad_bonus(q)
        return dict(ini=b["ini"], df=b["df"])

    def record_battle(self, q: Quadrant, att_fid, def_fid, winner: str, att_rows, def_rows,
                      note: str = "", clash: Optional[Clash] = None) -> List[str]:
        """
        att_rows/def_rows: listas de (unidad, estado, xp) con estado 'ok' | 'fallen' | 'destroyed'.
        Aplica bajas y XP, guarda la entrada en q.history y, si venía de un choque,
        resuelve el movimiento (captura y retirada del derrotado).
        """
        att, dfn = self.faction(att_fid), self.faction(def_fid)
        msgs: List[str] = []

        def apply(rows) -> Tuple[int, int]:
            lost = destroyed = 0
            for u, state, xp in rows:
                if state in ("fallen", "destroyed"):
                    u.status = state
                    lost += 1
                    destroyed += state == "destroyed"
                before = rank_of(u.xp)
                u.xp += xp
                if rank_of(u.xp) > before:
                    msgs.append(tr("log.rankup", u=u.name, r=rank_name(rank_of(u.xp))))
            return lost, destroyed

        la, da = apply(att_rows)
        ld, dd = apply(def_rows)
        rec = BattleRecord(self.turn, time.strftime("%Y-%m-%d"), att_fid, def_fid,
                           att.name if att else "—", dfn.name if dfn else tr("camp.neutral"),
                           winner, la, ld, da, dd, note.strip())
        q.history.append(rec)
        q.history = q.history[-60:]
        if clash is not None:
            if clash in self.clashes:
                self.clashes.remove(clash)
            if winner == "att" and att is not None and clash.att_force < len(att.forces):
                fc = att.forces[clash.att_force]
                fc.col, fc.row = q.col, q.row
                q.owner = att.fid
                if dfn is not None:
                    self.retreat(dfn, clash.def_force, q)
                self.prune_routes()
        wtxt = {"att": rec.att_name, "def": rec.def_name}.get(winner, tr("camp.draw"))
        self.log.append(tr("log.battle", t=self.turn, q=quad_label(q.col, q.row), a=rec.att_name,
                           d=rec.def_name, w=wtxt, la=la, ld=ld))
        self.log.extend(f"T{self.turn} · {m}" for m in msgs)
        self.log = self.log[-60:]
        return msgs

    # ---- economía y turnos ------------------------------------------------
    @staticmethod
    def quad_bonus(q: Quadrant) -> dict:
        d = {k: 0 for k in BONUS_KEYS}
        for b in q.buildings:
            for k in BONUS_KEYS:
                d[k] += BUILDINGS.get(b, {}).get(k, 0)
        return d

    def income(self, fid: int) -> dict:
        """
        Ingresos por turno. Solo producen los territorios abastecidos (con la logística activa).
        CR: max(1, abastecidos // 2) + Talleres/Mercados. RR: 1 por territorio + Cuarteles/Mercados.
        Hospital (recuperación), Torre (iniciativa) y Fortaleza (defensa) NO suman aquí: son locales.
        """
        d = {k: 0 for k in BONUS_KEYS}
        d.update(quads=0, builds=0, cut=0, hospitals=0)
        net = self.supply_network(fid) if self.logistics else None
        counted = 0
        for q in self.quads:
            if q.owner != fid:
                continue
            d["quads"] += 1
            d["builds"] += len(q.buildings)
            d["hospitals"] += q.buildings.count("hospital")
            if net is not None and (q.col, q.row) not in net:
                d["cut"] += 1
                continue
            counted += 1
            d["rr"] += BASE_RR
            bonus = self.quad_bonus(q)
            d["cr"] += bonus["cr"]
            d["rr"] += bonus["rr"]
        d["cr"] += max(1, counted // 2) if counted else 0
        return d

    def end_turn(self):
        # 1) Hospitales: solo recuperan caídas de los ejércitos del dueño presentes en el territorio
        for q in self.quads:
            owner = self.faction(q.owner)
            cap = q.buildings.count("hospital") * BUILDINGS["hospital"]["rec"]
            if owner is None or cap <= 0:
                continue
            healed = 0
            for g, _i, gf in self.forces_at(q.col, q.row):
                if g is not owner:
                    continue
                for u in gf.units:
                    if healed < cap and u.status == "fallen":
                        u.status = "active"
                        u.unpaid = 0
                        healed += 1
            if healed:
                self.log.append(tr("log.hospital", t=self.turn, q=quad_label(q.col, q.row), n=healed))
        # 2) Ingresos y mantenimiento de ejércitos
        for f in self.factions:
            inc = self.income(f.fid)
            f.cr += inc["cr"]
            f.rr += inc["rr"]
            self.log.append(tr("log.turn", t=self.turn, f=f.name, cr=inc["cr"], rr=inc["rr"]))
            paid, late, back = 0, 0, 0
            for fc in f.forces:
                for u in fc.units:
                    if u.status != "active":
                        continue
                    cost = self.unit_upkeep(u)
                    if cost <= f.cr:
                        f.cr -= cost
                        paid += cost
                        u.unpaid = 0
                    else:
                        u.unpaid += 1
                        if u.unpaid >= 2:            # segundo impago seguido: vuelve a reserva
                            u.status, u.unpaid = "reserve", 0
                            back += 1
                        else:                        # primer impago: penalización de moral
                            late += 1
                fc.moved = False
            if paid:
                self.log.append(tr("log.upkeep", t=self.turn, f=f.name, c=paid))
            if late:
                self.log.append(tr("log.unpaid", t=self.turn, f=f.name, n=late))
            if back:
                self.log.append(tr("log.reverted", t=self.turn, f=f.name, n=back))
        self.prune_routes()
        self.turn += 1
        self.log = self.log[-60:]

    # ---- persistencia -----------------------------------------------------
    def to_dict(self) -> dict:
        return dict(name=self.name, system=self.system, cols=self.cols, rows=self.rows,
                    seed=self.seed, turn=self.turn, next_fid=self.next_fid, log=self.log[-60:],
                    max_buildings=self.max_buildings, pts_per_rr=self.pts_per_rr,
                    logistics=self.logistics, routes=self.routes,
                    clashes=[asdict(c) for c in self.clashes],
                    factions=[asdict(f) for f in self.factions],
                    quads=[asdict(q) for q in self.quads])

    def ensure_forces(self):
        """Toda facción con territorio dispone al menos de un ejército (en su capital)."""
        for f in self.factions:
            if not f.forces:
                cap = self.capital_of(f)
                if cap:
                    f.forces = [Force(tr("force.name", n=1), cap.col, cap.row)]

    def ensure_state(self):
        """Completa/migra datos de partidas guardadas con versiones anteriores."""
        self.ensure_forces()
        for f in self.factions:
            f.army_system = normalize_system(f.army_system) if f.army_system else "GEN"
            if self.system != "GEN":
                f.army_system = self.system
            if f.units:                                  # v4: lista global -> ejércitos por fuerza
                if not f.forces:
                    f.forces = [Force(tr("force.name", n=1), 0, 0)]
                for u in f.units:
                    idx = u.force if 0 <= u.force < len(f.forces) else 0
                    f.forces[idx].units.append(u)
                fc0 = f.forces[0]
                fc0.army_name = fc0.army_name or f.army_name
                fc0.army_source = fc0.army_source or f.army_source
                fc0.points_limit = fc0.points_limit or f.points_limit
                f.units, f.army_name, f.army_source, f.points_limit = [], "", "", 0
            for fc in f.forces:
                fc.col = clamp(fc.col, 0, self.cols - 1)
                fc.row = clamp(fc.row, 0, self.rows - 1)
                for u in fc.units:
                    if u.status not in STATUSES:
                        u.status = "reserve"
        # rutas v4 (4 valores): se conservan solo si unen dos territorios de la misma facción
        fixed = []
        for rt in self.routes:
            if len(rt) == 4 and self.in_bounds(rt[0], rt[1]) and self.in_bounds(rt[2], rt[3]):
                o1, o2 = self.quad(rt[0], rt[1]).owner, self.quad(rt[2], rt[3]).owner
                if o1 is not None and o1 == o2:
                    fixed.append(rt + [o1])
            elif len(rt) >= 5:
                fixed.append(rt[:5])
        self.routes = fixed
        self.prune_routes()

    @classmethod
    def from_dict(cls, d: dict) -> "Campaign":
        c = cls.__new__(cls)
        raw_name = str(d.get("name") or tr("dlg.default_name"))
        code = d.get("system") if d.get("system") in CAMPAIGN_TYPES else split_campaign_name(raw_name)[0]
        c.system = code
        c.name = raw_name if valid_campaign_name(raw_name) else compose_campaign_name(
            code, split_campaign_name(raw_name)[1])
        c.cols, c.rows = int(d["cols"]), int(d["rows"])
        c.seed, c.turn = int(d.get("seed", 1)), int(d.get("turn", 1))
        c.next_fid = int(d.get("next_fid", 1))
        c.max_buildings = int(d.get("max_buildings", 0))
        c.pts_per_rr = int(d.get("pts_per_rr", 25))
        c.logistics = bool(d.get("logistics", False))      # partidas antiguas: sin logística
        c.routes = [[int(x) for x in rt] for rt in d.get("routes", [])]
        c.clashes = [_mk(Clash, x) for x in d.get("clashes", [])]
        c.log = list(d.get("log", []))
        c.factions = []
        for fd in d["factions"]:
            fd = dict(fd)
            if "rp" in fd and "rr" not in fd:
                fd["rr"] = fd["rp"]
            if "sup" in fd and "cr" not in fd:
                fd["cr"] = fd["sup"]
            fd["units"] = [_mk(ArmyUnit, u) for u in fd.get("units", [])]
            forces = []
            for x in fd.get("forces", []):
                x = dict(x)
                x["units"] = [_mk(ArmyUnit, u) for u in x.get("units", [])]
                forces.append(_mk(Force, x))
            fd["forces"] = forces
            c.factions.append(_mk(Faction, fd))
        c.quads = []
        for qd in d["quads"]:
            qd = dict(qd)
            qd["history"] = [_mk(BattleRecord, h) for h in qd.get("history", [])]
            q = _mk(Quadrant, qd)
            q.biome = clamp(int(q.biome), 0, len(BIOMES) - 1)
            q.buildings = [b for b in q.buildings if b in BUILDINGS]
            c.quads.append(q)
        if len(c.quads) != c.cols * c.rows:
            raise ValueError("inconsistent campaign map")
        c.ensure_state()
        return c


# =============================================================================
#  MODELO DE DATOS: BATALLA
# =============================================================================
@dataclass
class TerrainType:
    key: str
    name: str
    color: tuple
    shape: str          # "ellipse" | "rect"
    w: float
    h: float
    var: float
    density: float
    style: str
    effect: str = ""
    custom: bool = False
    i18n: str = ""      # clave de traducción para los tipos por defecto
    renamed: bool = False
    rules: List[str] = field(default_factory=list)   # reglas especiales por defecto del tipo

    def raw_name(self) -> str:
        if self.i18n and not self.renamed:
            return tr(self.i18n)
        return self.name

    def label(self) -> str:
        return self.raw_name() or "?"

    def fx(self) -> str:
        return tr(self.i18n + ".fx") if (self.i18n and not self.custom) else self.effect


@dataclass
class TerrainPiece:
    type_key: str
    x: float
    y: float
    w: float
    h: float
    seed: int = 0
    rules: List[str] = field(default_factory=list)   # reglas especiales de esta pieza


def default_terrain_types() -> List[TerrainType]:
    def t(key, color, shape, w, h, var, dens, style, rules):
        return TerrainType(key, "", color, shape, w, h, var, dens, style, "", False,
                           f"terrain.{key}", False, list(rules))
    return [
        t("hill", (146, 120, 84), "ellipse", 20, 14, 0.25, 1.0, "contour", []),
        t("forest", (40, 100, 56), "ellipse", 18, 16, 0.30, 1.5, "trees", ["cover", "difficult"]),
        t("ruins", (134, 130, 124), "rect", 14, 10, 0.30, 1.0, "ruins", ["cover"]),
        t("building", (156, 96, 80), "rect", 12, 10, 0.20, 0.8, "building", ["sight"]),
        t("obstacle", (92, 94, 104), "rect", 10, 3, 0.35, 1.5, "wall", ["cover"]),
        t("marsh", (74, 82, 46), "ellipse", 16, 12, 0.30, 0.6, "marsh", ["difficult", "dangerous"]),
        t("crates", (184, 130, 54), "rect", 6, 5, 0.30, 1.0, "crates", ["cover"]),
    ]


class BattleState:
    def __init__(self):
        self.size_idx = 1
        self.types: List[TerrainType] = default_terrain_types()
        self.counts: Dict[str, int] = {}
        self.pieces: List[TerrainPiece] = []
        self.seed = random.randint(1, 99999)
        self.show_zones = True
        self.manual = False
        self.sel_type = self.types[0].key
        self.sel_piece: Optional[int] = None
        self.last_msg = tr("bt.ready")
        self.context = ""
        self.custom_counter = 1
        self.deploy = "frontline"          # estilo de despliegue OPR
        self.depth: Optional[float] = None  # profundidad de zona en cm (None = automática)
        self.flip = False                  # intercambia qué jugador ocupa cada zona
        self.condition = ""                # condición del campo de batalla (clave de regla)
        self.auto_counts()

    @property
    def W(self) -> int:
        return BOARD_SIZES[self.size_idx][0]

    @property
    def H(self) -> int:
        return BOARD_SIZES[self.size_idx][1]

    # ---- despliegue -------------------------------------------------------
    def auto_depth(self) -> float:
        axis = self.W if self.deploy == "side" else self.H
        return min(30.0, axis * 0.25)           # 12'' ≈ 30 cm, limitado en tableros pequeños

    def eff_depth(self) -> float:
        return float(self.depth) if self.depth else self.auto_depth()

    def zone_depth(self) -> float:
        return self.eff_depth()

    def edge_band(self) -> float:
        """Franja de entrada de refuerzos (3'' ≈ 7,5 cm) en «Asalto de flanco»."""
        return 7.5 if self.deploy == "flank" else 0.0

    def zones(self) -> List[tuple]:
        """Zonas de despliegue como (jugador 'A'/'B', polígono en cm, rol 'a'/'b')."""
        W, H, D = float(self.W), float(self.H), self.eff_depth()

        def rect(x, y, w, h):
            return [(x, y), (x + w, y), (x + w, y + h), (x, y + h)]

        k = self.deploy
        if k == "side":
            z = [("a", rect(0, 0, D, H)), ("b", rect(W - D, 0, D, H))]
        elif k == "ambush":
            cw, ch, b = W * 0.34, H * 0.5, D * 0.5
            z = [("a", rect((W - cw) / 2, (H - ch) / 2, cw, ch)),
                 ("b", rect(0, 0, W, b)), ("b", rect(0, H - b, W, b)),
                 ("b", rect(0, b, b, H - 2 * b)), ("b", rect(W - b, b, b, H - 2 * b))]
        elif k == "spearhead":
            L = min(W, H) * 0.6
            z = [("a", [(0, 0), (L, 0), (0, L)]), ("b", [(W, H), (W - L, H), (W, H - L)])]
        elif k == "cornered":
            z = [("a", rect(0, 0, W * 0.3, H * 0.45)),
                 ("b", rect(0, H - D, W, D)), ("b", rect(W - D, 0, D, H - D))]
        else:                                    # frontline / flank
            z = [("a", rect(0, 0, W, D)), ("b", rect(0, H - D, W, D))]
        out = []
        for role, poly in z:
            owner = role if not self.flip else ("b" if role == "a" else "a")
            out.append((owner.upper(), poly, role))
        return out

    def in_zone(self, x: float, y: float) -> bool:
        return any(point_in_poly(x, y, poly) for _o, poly, _r in self.zones())

    def type_by_key(self, key: str) -> Optional[TerrainType]:
        return next((t for t in self.types if t.key == key), None)

    def auto_counts(self, mult: Optional[dict] = None):
        for t in self.types:
            m = (mult or {}).get(t.key, 1.0)
            self.counts[t.key] = int(round(t.density * self.W * self.H / 3600.0 * m))

    def set_size(self, idx: int):
        old = self.W * self.H
        self.size_idx = idx
        ratio = (self.W * self.H) / old
        for k in list(self.counts):
            self.counts[k] = int(round(self.counts[k] * ratio))
        self.pieces = []
        self.sel_piece = None
        self.last_msg = tr("bt.size_msg", w=self.W, h=self.H)

    def add_custom_type(self) -> Optional[TerrainType]:
        if len(self.types) >= MAX_TERRAIN_TYPES:
            return None
        n = self.custom_counter
        key = f"custom{n}"
        self.custom_counter += 1
        col = tuple(random.Random(n * 31 + 7).randint(70, 210) for _ in range(3))
        t = TerrainType(key, tr("terrain.custom", n=n), col, "rect", 12, 8, 0.25, 0.5, "plain",
                        tr("terrain.custom.fx"), True)
        self.types.append(t)
        self.counts[key] = 0
        self.sel_type = key
        return t

    def remove_type(self, key: str):
        if len(self.types) <= 1:
            return
        self.types = [t for t in self.types if t.key != key]
        self.counts.pop(key, None)
        self.pieces = [p for p in self.pieces if p.type_key != key]
        self.sel_piece = None
        if self.sel_type == key:
            self.sel_type = self.types[0].key

    def bounds(self, p: TerrainPiece) -> Tuple[float, float, float, float]:
        t = self.type_by_key(p.type_key)
        shrink = 0.88 if (t and t.shape == "ellipse") else 1.0
        hw, hh = p.w / 2 * shrink, p.h / 2 * shrink
        return p.x - hw, p.y - hh, p.x + hw, p.y + hh

    def overlaps(self, a: TerrainPiece, b: TerrainPiece, gap: float = 0.0) -> bool:
        A, B = self.bounds(a), self.bounds(b)
        return not (A[2] + gap <= B[0] or B[2] + gap <= A[0] or
                    A[3] + gap <= B[1] or B[3] + gap <= A[1])

    def clamp_piece(self, p: TerrainPiece):
        p.w, p.h = min(p.w, self.W), min(p.h, self.H)
        p.x = clamp(p.x, p.w / 2, self.W - p.w / 2)
        p.y = clamp(p.y, p.h / 2, self.H - p.h / 2)

    def rotate(self, idx: int):
        p = self.pieces[idx]
        p.w, p.h = p.h, p.w
        self.clamp_piece(p)

    def hit(self, bx: float, by: float) -> Optional[int]:
        for i in range(len(self.pieces) - 1, -1, -1):
            p = self.pieces[i]
            t = self.type_by_key(p.type_key)
            dx, dy = (bx - p.x) / (p.w / 2), (by - p.y) / (p.h / 2)
            if t and t.shape == "ellipse":
                if dx * dx + dy * dy <= 1.0:
                    return i
            elif abs(dx) <= 1 and abs(dy) <= 1:
                return i
        return None

    def generate(self, keep: bool = False):
        rng = random.Random(self.seed + (len(self.pieces) * 7919 if keep else 0))
        if not keep:
            self.pieces = []
            self.sel_piece = None
        existing: Dict[str, int] = {}
        for p in self.pieces:
            existing[p.type_key] = existing.get(p.type_key, 0) + 1
        wanted = placed = 0
        gap = 3.0
        for t in sorted(self.types, key=lambda tt: -(tt.w * tt.h)):
            need = self.counts.get(t.key, 0) - existing.get(t.key, 0)
            for _ in range(max(0, need)):
                wanted += 1
                for _attempt in range(250):
                    w = max(2.0, round(t.w * (1 + rng.uniform(-t.var, t.var)), 1))
                    h = max(2.0, round(t.h * (1 + rng.uniform(-t.var, t.var)), 1))
                    if rng.random() < 0.5:
                        w, h = h, w
                    if w > self.W or h > self.H:
                        continue
                    x = round(rng.uniform(w / 2, self.W - w / 2) * 2) / 2
                    y = round(rng.uniform(h / 2, self.H - h / 2) * 2) / 2
                    if self.in_zone(x, y) and rng.random() < 0.65:
                        continue
                    cand = TerrainPiece(t.key, x, y, w, h, rng.randint(0, 10 ** 6), list(t.rules))
                    if not any(self.overlaps(cand, q, gap) for q in self.pieces):
                        self.pieces.append(cand)
                        placed += 1
                        break
        miss = wanted - placed
        self.last_msg = tr("bt.placed", p=placed, w=wanted) + (tr("bt.placed_miss", m=miss) if miss else "")

    def apply_biome(self, biome_idx: int):
        self.auto_counts(BIOMES[biome_idx]["mult"])

    def to_dict(self) -> dict:
        return dict(size_idx=self.size_idx, seed=self.seed, show_zones=self.show_zones,
                    counts=self.counts, context=self.context,
                    custom_counter=self.custom_counter, sel_type=self.sel_type,
                    deploy=self.deploy, depth=self.depth, flip=self.flip,
                    condition=self.condition,
                    types=[asdict(t) for t in self.types],
                    pieces=[asdict(p) for p in self.pieces])

    @classmethod
    def from_dict(cls, d: dict) -> "BattleState":
        b = cls()
        b.types = []
        for td in d["types"]:
            td = dict(td)
            td["color"] = tuple(td["color"])
            b.types.append(_mk(TerrainType, td))
        if not b.types:
            b.types = default_terrain_types()
        b.size_idx = clamp(int(d.get("size_idx", 1)), 0, len(BOARD_SIZES) - 1)
        b.seed = int(d.get("seed", 1))
        b.show_zones = bool(d.get("show_zones", True))
        b.context = d.get("context", "")
        b.custom_counter = int(d.get("custom_counter", 1))
        b.deploy = d.get("deploy") if d.get("deploy") in DEPLOY_TYPES else "frontline"
        b.depth = float(d["depth"]) if d.get("depth") else None
        b.flip = bool(d.get("flip", False))
        b.condition = d.get("condition") if d.get("condition") in RULE_CATS else ""
        b.counts = {k: int(v) for k, v in d.get("counts", {}).items()}
        for t in b.types:
            b.counts.setdefault(t.key, 0)
        keys = {t.key for t in b.types}
        b.pieces = [_mk(TerrainPiece, p) for p in d.get("pieces", []) if p.get("type_key") in keys]
        b.sel_type = d.get("sel_type") if d.get("sel_type") in keys else b.types[0].key
        b.sel_piece = None
        b.last_msg = ""
        return b


# =============================================================================
#  RENDER DE TABLERO (pantalla y exportación)
# =============================================================================
def draw_terrain_piece(surf, p: TerrainPiece, t: Optional[TerrainType], ox, oy, sc, fonts,
                       selected=False, bad=False, label=True):
    if t is None:
        t = TerrainType("?", "?", (120, 120, 120), "rect", 5, 5, 0, 0, "plain")
    w, h = max(4, int(p.w * sc)), max(4, int(p.h * sc))
    rect = pygame.Rect(0, 0, w, h)
    rect.center = (int(ox + p.x * sc), int(oy + p.y * sc))
    base = t.color
    dark = darker(base, 0.55)
    light = lighter(base, 0.35)
    rng = random.Random(p.seed)
    ell = t.shape == "ellipse"

    if ell:
        pygame.draw.ellipse(surf, base, rect)
    else:
        pygame.draw.rect(surf, base, rect, border_radius=2)

    st = t.style
    if st == "trees":
        n = clamp(int(p.w * p.h / 10), 5, 45)
        rad = max(3, int(1.7 * sc))
        for _ in range(n):
            a = rng.uniform(0, 2 * math.pi)
            d = math.sqrt(rng.random()) * 0.80
            tx = rect.centerx + math.cos(a) * d * w / 2
            ty = rect.centery + math.sin(a) * d * h / 2
            pygame.draw.circle(surf, darker(base, 0.65), (int(tx), int(ty)), rad)
            pygame.draw.circle(surf, lighter(base, 0.22),
                               (int(tx - rad * 0.25), int(ty - rad * 0.25)), max(2, int(rad * 0.62)))
    elif st == "contour":
        for k in (0.74, 0.48, 0.22):
            r2 = pygame.Rect(0, 0, max(3, int(w * k)), max(3, int(h * k)))
            r2.center = rect.center
            pygame.draw.ellipse(surf, lighter(base, 0.25 + (0.74 - k) * 0.5), r2, 2)
    elif st == "ruins":
        th = max(2, int(sc * 1.0))
        walls = [pygame.Rect(rect.x, rect.y, w, th), pygame.Rect(rect.x, rect.bottom - th, w, th),
                 pygame.Rect(rect.x, rect.y, th, h), pygame.Rect(rect.right - th, rect.y, th, h)]
        for wr in walls:
            if rng.random() > 0.25:
                pygame.draw.rect(surf, dark, wr)
        for _ in range(8):
            rw, rh = rng.randint(2, max(3, int(sc * 1.4))), rng.randint(2, max(3, int(sc * 1.4)))
            rx = rng.randint(rect.x + th, max(rect.x + th, rect.right - th - rw))
            ry = rng.randint(rect.y + th, max(rect.y + th, rect.bottom - th - rh))
            pygame.draw.rect(surf, rng.choice((dark, light)), (rx, ry, rw, rh))
    elif st == "building":
        inner = rect.inflate(-int(w * 0.25), -int(h * 0.25))
        pygame.draw.rect(surf, darker(base, 0.78), inner)
        for a, b in ((rect.topleft, inner.topleft), (rect.topright, inner.topright),
                     (rect.bottomleft, inner.bottomleft), (rect.bottomright, inner.bottomright)):
            pygame.draw.line(surf, dark, a, b, 1)
        pygame.draw.line(surf, dark, (inner.left, inner.centery), (inner.right, inner.centery), 1)
    elif st == "marsh":
        for _ in range(14):
            a = rng.uniform(0, 2 * math.pi)
            d = math.sqrt(rng.random()) * 0.72
            mx = rect.centerx + math.cos(a) * d * w / 2
            my = rect.centery + math.sin(a) * d * h / 2
            er = pygame.Rect(0, 0, max(4, int(sc * 2.6)), max(3, int(sc * 1.1)))
            er.center = (int(mx), int(my))
            pygame.draw.ellipse(surf, lighter(base, 0.30), er, 1)
    elif st == "wall":
        inner = rect.inflate(-4, -4)
        if inner.w > 0 and inner.h > 0:
            pygame.draw.rect(surf, darker(base, 0.8), inner)
        step = max(5, int(sc * 2))
        for x in range(rect.x + step, rect.right - 2, step):
            pygame.draw.line(surf, dark, (x, rect.y + 2), (x, rect.bottom - 3), 1)
    elif st == "crates":
        pygame.draw.line(surf, dark, rect.topleft, rect.bottomright, 2)
        pygame.draw.line(surf, dark, rect.topright, rect.bottomleft, 2)
        pygame.draw.rect(surf, light, rect.inflate(-4, -4), 1)

    if ell:
        pygame.draw.ellipse(surf, dark, rect, 2)
    else:
        pygame.draw.rect(surf, dark, rect, 2, border_radius=2)

    if label and fonts and w > 52 and h > 28:
        txt = t.label().split("/")[0].strip()
        s = fonts["tiny"].render(txt, True, (250, 250, 250))
        sh = fonts["tiny"].render(txt, True, (0, 0, 0))
        r = s.get_rect(center=rect.center)
        surf.blit(sh, r.move(1, 1))
        surf.blit(s, r)

    if getattr(p, "rules", None) and fonts and w > 34:       # insignias de reglas especiales
        bx, by = rect.x + 3, rect.bottom - 14
        for rk in p.rules:
            if rk not in RULE_CATS:
                continue
            ts = fonts["tiny"].render(rcode(rk), True, (255, 255, 255))
            bw = ts.get_width() + 6
            if bx + bw > rect.right - 2:
                break
            pygame.draw.rect(surf, RULE_COLORS[RULE_CATS[rk]], (bx, by, bw, 12), border_radius=3)
            surf.blit(ts, (bx + 3, by))
            bx += bw + 2

    if bad:
        pygame.draw.rect(surf, C_BAD, rect.inflate(6, 6), 2, border_radius=3)
    if selected:
        pygame.draw.rect(surf, C_ACCENT, rect.inflate(8, 8), 2, border_radius=3)


def draw_board(surf, b: BattleState, ox, oy, sc, fonts, sel=None, flag_overlap=True):
    W, H = b.W, b.H
    board = pygame.Rect(int(ox), int(oy), int(W * sc), int(H * sc))
    pygame.draw.rect(surf, BOARD_COL, board)
    for x in range(10, W, 10):
        pygame.draw.line(surf, BOARD_GRID, (ox + x * sc, oy), (ox + x * sc, board.bottom))
    for y in range(10, H, 10):
        pygame.draw.line(surf, BOARD_GRID, (ox, oy + y * sc), (board.right, oy + y * sc))

    if b.show_zones:
        ov = pygame.Surface(board.size, pygame.SRCALPHA)
        cols = {"A": (210, 70, 70), "B": (70, 110, 220)}
        labels = {}
        for owner, poly, role in b.zones():
            pts = [(int(x * sc), int(y * sc)) for x, y in poly]
            pygame.draw.polygon(ov, (*cols[owner], 62), pts)
            pygame.draw.polygon(ov, (*cols[owner], 175), pts, 2)
            xs, ys = [p[0] for p in poly], [p[1] for p in poly]
            area = (max(xs) - min(xs)) * (max(ys) - min(ys))
            if role not in labels or area > labels[role][0]:
                labels[role] = (area, owner, sum(xs) / len(xs) * sc, sum(ys) / len(ys) * sc)
        band = b.edge_band()
        if band:
            bw = max(2, int(band * sc))
            green = (80, 200, 120, 48)
            pygame.draw.rect(ov, green, (0, 0, board.w, bw))
            pygame.draw.rect(ov, green, (0, board.h - bw, board.w, bw))
            pygame.draw.rect(ov, green, (0, bw, bw, board.h - 2 * bw))
            pygame.draw.rect(ov, green, (board.w - bw, bw, bw, board.h - 2 * bw))
            pygame.draw.rect(ov, (80, 200, 120, 160), (bw, bw, board.w - 2 * bw, board.h - 2 * bw), 1)
        surf.blit(ov, board.topleft)
        for role, (_a, owner, cx, cy) in labels.items():
            txt = tr(f"deploy.{b.deploy}.r{role}")
            s = fonts["tiny"].render(txt, True, lighter(cols[owner], 0.65))
            surf.blit(s, s.get_rect(center=(int(board.x + cx), int(board.y + cy))))
        if band:
            s = fonts["tiny"].render(tr("dep.reserve_label"), True, (170, 235, 190))
            surf.blit(s, s.get_rect(midbottom=(board.centerx, board.bottom - int(band * sc) - 3)))

    bad = set()
    if flag_overlap:
        for i in range(len(b.pieces)):
            for j in range(i + 1, len(b.pieces)):
                if b.overlaps(b.pieces[i], b.pieces[j], 0.0):
                    bad.add(i)
                    bad.add(j)
    for i, p in enumerate(b.pieces):
        draw_terrain_piece(surf, p, b.type_by_key(p.type_key), ox, oy, sc, fonts,
                           selected=(i == sel), bad=(i in bad))
    pygame.draw.rect(surf, (20, 22, 26), board, 3)

    for x in range(0, W + 1, 10):
        s = fonts["tiny"].render(str(x), True, C_DIM)
        surf.blit(s, s.get_rect(midbottom=(int(ox + x * sc), int(oy - 3))))
    for y in range(0, H + 1, 10):
        s = fonts["tiny"].render(str(y), True, C_DIM)
        surf.blit(s, s.get_rect(midright=(int(ox - 5), int(oy + y * sc))))


def export_battle(b: BattleState, fonts) -> Tuple[str, str]:
    os.makedirs(EXPORT_DIR, exist_ok=True)
    stamp = time.strftime("%Y%m%d_%H%M%S")
    sc, margin = 8, 56
    used = [t for t in b.types if any(p.type_key == t.key for p in b.pieces)]
    legend_h = 40 + 24 * max(1, (len(used) + 2) // 3)
    surf = pygame.Surface((b.W * sc + margin * 2, b.H * sc + margin * 2 + legend_h))
    surf.fill(C_BG)
    draw_board(surf, b, margin, margin, sc, fonts, sel=None, flag_overlap=False)
    title = tr("bt.exp_title", w=b.W, h=b.H, n=len(b.pieces), s=b.seed)
    title += f" · {tr('deploy.' + b.deploy)}"
    if b.condition:
        title += f" · {rname(b.condition)}"
    if b.context:
        title += f" · {b.context}"
    surf.blit(fonts["m"].render(title, True, C_TEXT), (margin, 12))
    ly = margin * 2 + b.H * sc - margin + 12
    for i, t in enumerate(used):
        n = sum(1 for p in b.pieces if p.type_key == t.key)
        cx, cy = margin + (i % 3) * 300, ly + (i // 3) * 24
        pygame.draw.rect(surf, t.color, (cx, cy, 16, 16))
        pygame.draw.rect(surf, darker(t.color, 0.5), (cx, cy, 16, 16), 1)
        surf.blit(fonts["s"].render(f"{t.label()} x{n}", True, C_TEXT), (cx + 24, cy - 1))
    png = os.path.join(EXPORT_DIR, f"opr_battle_{stamp}.png")
    js = os.path.join(EXPORT_DIR, f"opr_battle_{stamp}.json")
    pygame.image.save(surf, png)
    with open(js, "w", encoding="utf-8") as fh:
        json.dump(b.to_dict(), fh, ensure_ascii=False, indent=2)
    return png, js


# =============================================================================
#  UI: widgets en modo inmediato
# =============================================================================
class UI:
    def __init__(self, screen, fonts):
        self.screen = screen
        self.f = fonts
        self.mouse = (0, 0)
        self.click = None
        self.raw_click = None
        self.rclick = None
        self.wheel = 0
        self.keys: List[pygame.event.Event] = []
        self.focus: Optional[str] = None
        self.tip: Optional[str] = None
        self.input_enabled = True      # False mientras hay un diálogo modal abierto
        self.mouse_fn = pygame.mouse.get_pos   # la App lo sustituye (coordenadas lógicas)
        self._cache: Dict[tuple, pygame.Surface] = {}

    def begin(self, events):
        self.mouse = self.mouse_fn()
        self.click = self.raw_click = self.rclick = None
        self.wheel = 0
        self.keys = []
        self.tip = None
        wheel_type = getattr(pygame, "MOUSEWHEEL", None)
        for e in events:
            if e.type == pygame.MOUSEBUTTONDOWN:
                if e.button == 1:
                    self.click = self.raw_click = e.pos
                elif e.button == 3:
                    self.rclick = e.pos
            elif e.type == pygame.KEYDOWN:
                self.keys.append(e)
            elif wheel_type is not None and e.type == wheel_type:
                self.wheel += e.y

    # ---- texto ------------------------------------------------------------
    def render(self, s, font, color):
        key = (s, font, color)
        surf = self._cache.get(key)
        if surf is None:
            if len(self._cache) > 1500:
                self._cache.clear()
            surf = self.f[font].render(s, True, color)
            self._cache[key] = surf
        return surf

    def text(self, s, pos, font="s", color=C_TEXT, anchor="topleft"):
        surf = self.render(str(s), font, color)
        r = surf.get_rect(**{anchor: pos})
        self.screen.blit(surf, r)
        return r

    def fit(self, s, font, maxw):
        f = self.f[font]
        if f.size(s)[0] <= maxw:
            return s
        while s and f.size(s + "..")[0] > maxw:
            s = s[:-1]
        return s + ".."

    def wrap(self, s, font, maxw) -> List[str]:
        lines, cur = [], ""
        for w in s.split():
            test = (cur + " " + w).strip()
            if self.f[font].size(test)[0] <= maxw or not cur:
                cur = test
            else:
                lines.append(cur)
                cur = w
        if cur:
            lines.append(cur)
        return lines

    def panel(self, rect, title=None):
        r = pygame.Rect(rect)
        pygame.draw.rect(self.screen, C_PANEL, r, border_radius=8)
        pygame.draw.rect(self.screen, C_LINE, r, 1, border_radius=8)
        if title:
            self.text(title, (r.x + 12, r.y + 8), "xs", C_ACCENT)

    # ---- interacción ------------------------------------------------------
    def clicked(self, rect) -> bool:
        """Clic izquierdo dentro de rect (lo consume)."""
        if not self.input_enabled or self.click is None:
            return False
        if pygame.Rect(rect).collidepoint(self.click):
            self.click = None
            return True
        return False

    def take_click(self, rect):
        """Devuelve la posición del clic izquierdo si cae en rect (y lo consume), o None."""
        if not self.input_enabled or self.click is None:
            return None
        p = self.click
        if pygame.Rect(rect).collidepoint(p):
            self.click = None
            return p
        return None

    def over(self, rect) -> bool:
        return self.input_enabled and pygame.Rect(rect).collidepoint(self.mouse)

    def button(self, rect, label, enabled=True, active=False, color=None, font="s",
               tip=None, align="center", swatch=None):
        r = pygame.Rect(rect)
        over = self.input_enabled and r.collidepoint(self.mouse)
        hover = enabled and over
        if not enabled:
            col = C_BTN_OFF
        elif color is not None:
            col = lighter(color, 0.18) if hover else color
        elif active:
            col = C_BTN_ON
        else:
            col = C_BTN_H if hover else C_BTN
        pygame.draw.rect(self.screen, col, r, border_radius=5)
        pygame.draw.rect(self.screen, C_ACCENT if (active and enabled) else C_LINE, r,
                         2 if active else 1, border_radius=5)
        tcol = C_TEXT if enabled else (104, 109, 122)
        if color is not None and enabled:
            lum = 0.3 * color[0] + 0.59 * color[1] + 0.11 * color[2]
            tcol = (20, 20, 24) if lum > 150 else (250, 250, 250)
        left = r.x + 8
        if swatch is not None:
            pygame.draw.rect(self.screen, swatch, (r.x + 6, r.y + 5, 12, max(6, r.h - 10)))
            pygame.draw.rect(self.screen, (15, 15, 18), (r.x + 6, r.y + 5, 12, max(6, r.h - 10)), 1)
            left = r.x + 24
        avail = r.w - (left - r.x) - 6 if align == "left" else r.w - 10
        fnt = font
        if fnt == "s" and self.f[fnt].size(label)[0] > avail:
            fnt = "xs"
        label = self.fit(label, fnt, avail)
        if align == "left":
            self.text(label, (left, r.centery), fnt, tcol, "midleft")
        else:
            self.text(label, r.center, fnt, tcol, "center")
        if over and tip:
            self.tip = tip
        clicked = enabled and self.input_enabled and self.click is not None and r.collidepoint(self.click)
        if clicked:
            self.click = None
        return clicked

    def stepper(self, rect, value, lo, hi, step=1, fmt="{}", enabled=True):
        r = pygame.Rect(rect)
        bw = min(24, r.h)
        mult = 5 if (pygame.key.get_mods() & pygame.KMOD_SHIFT) else 1
        if self.button((r.x, r.y, bw, r.h), "-", enabled):
            value = max(lo, value - step * mult)
        if self.button((r.right - bw, r.y, bw, r.h), "+", enabled):
            value = min(hi, value + step * mult)
        mid = pygame.Rect(r.x + bw + 2, r.y, r.w - 2 * bw - 4, r.h)
        pygame.draw.rect(self.screen, C_PANEL2, mid, border_radius=4)
        self.text(fmt.format(value), mid.center, "s", C_TEXT, "center")
        return value

    def text_field(self, uid, rect, text, maxlen=22):
        r = pygame.Rect(rect)
        focused = self.focus == uid
        if self.input_enabled:
            if self.raw_click:
                if r.collidepoint(self.raw_click):
                    self.focus = uid
                    focused = True
                    self.click = None
                elif focused:
                    self.focus = None
                    focused = False
            if focused:
                for e in self.keys:
                    ctrl = e.mod & (pygame.KMOD_CTRL | pygame.KMOD_META)
                    if e.key == pygame.K_BACKSPACE:
                        text = "" if ctrl else text[:-1]
                    elif e.key == pygame.K_v and ctrl:
                        clip = " ".join(get_clipboard_text().split())
                        text = (text + clip)[:maxlen]
                    elif e.key in (pygame.K_RETURN, pygame.K_KP_ENTER, pygame.K_ESCAPE):
                        self.focus = None
                        focused = False
                        break
                    elif not ctrl and e.unicode and e.unicode.isprintable() and len(text) < maxlen:
                        text += e.unicode
        pygame.draw.rect(self.screen, (24, 27, 34), r, border_radius=4)
        pygame.draw.rect(self.screen, C_ACCENT if focused else C_LINE, r, 2 if focused else 1,
                         border_radius=4)
        avail = r.w - 14
        if focused:                      # muestra el final del texto mientras se edita
            shown = text
            f = self.f["s"]
            while shown and f.size(shown)[0] > avail:
                shown = shown[1:]
        else:
            shown = self.fit(text, "s", avail)
        rr = self.text(shown, (r.x + 7, r.centery), "s", C_TEXT, "midleft")
        if focused and (pygame.time.get_ticks() // 450) % 2 == 0:
            pygame.draw.line(self.screen, C_TEXT, (rr.right + 2, r.y + 5), (rr.right + 2, r.bottom - 5))
        return text

    def draw_tooltip(self):
        if not self.tip:
            return
        lines = self.wrap(self.tip, "xs", 300)
        w = max(self.f["xs"].size(l)[0] for l in lines) + 16
        h = len(lines) * 16 + 10
        x = clamp(self.mouse[0] + 14, 4, WIN_W - w - 4)
        y = clamp(self.mouse[1] + 18, 4, WIN_H - h - 4)
        pygame.draw.rect(self.screen, (14, 16, 20), (x, y, w, h), border_radius=5)
        pygame.draw.rect(self.screen, C_ACCENT, (x, y, w, h), 1, border_radius=5)
        for i, l in enumerate(lines):
            self.text(l, (x + 8, y + 5 + i * 16), "xs", C_TEXT)


def make_fonts() -> Dict[str, pygame.font.Font]:
    names = "segoeui,dejavusans,arial,helvetica,liberationsans,freesans"

    def f(size, bold=False):
        try:
            return pygame.font.SysFont(names, size, bold=bold)
        except Exception:
            return pygame.font.Font(None, size + 4)

    return dict(tiny=f(11), xs=f(12), s=f(14), m=f(16), l=f(20, True), xl=f(26, True))


# =============================================================================
#  VISTAS
# =============================================================================
class View:
    def __init__(self, app: "App"):
        self.app = app

    def handle_event(self, e, ui: UI):
        pass

    def draw(self, ui: UI):
        pass


# -----------------------------------------------------------------------------
#  Vista 1: Mapa de campaña
# -----------------------------------------------------------------------------
class CampaignView(View):
    MAP_RECT = pygame.Rect(20, 58, 840, 634)

    def __init__(self, app):
        super().__init__(app)
        self.sel: Optional[Tuple[int, int]] = None
        self.sel_force: Optional[Tuple[int, int]] = None     # (fid, índice de fuerza)
        self.dtab = "terr"                                   # terr | forces | hist
        self.route_mode: Optional[Tuple[int, int]] = None    # origen de la ruta que se está creando
        self.hist_scroll = 0

    def geometry(self):
        camp = self.app.campaign
        cs = min(self.MAP_RECT.w // camp.cols, self.MAP_RECT.h // camp.rows)
        ox = self.MAP_RECT.x + (self.MAP_RECT.w - cs * camp.cols) // 2
        oy = self.MAP_RECT.y + (self.MAP_RECT.h - cs * camp.rows) // 2
        return cs, ox, oy

    def selected_force(self):
        if not self.sel_force:
            return None
        f = self.app.campaign.faction(self.sel_force[0])
        if f is None or self.sel_force[1] >= len(f.forces):
            return None
        return f, self.sel_force[1], f.forces[self.sel_force[1]]

    @staticmethod
    def dashed(surf, a, b, color, dash=10, gap=7, width=3):
        dx, dy = b[0] - a[0], b[1] - a[1]
        dist = math.hypot(dx, dy)
        if dist < 1:
            return
        ux, uy = dx / dist, dy / dist
        pos = 0.0
        while pos < dist:
            end = min(dist, pos + dash)
            pygame.draw.line(surf, color, (int(a[0] + ux * pos), int(a[1] + uy * pos)),
                             (int(a[0] + ux * end), int(a[1] + uy * end)), width)
            pos += dash + gap

    # ------------------------------------------------------------------
    def draw(self, ui: UI):
        camp = self.app.campaign
        scr = ui.screen
        camp.ensure_forces()
        lost = camp.prune_routes()
        if lost:
            self.app.set_status(tr("status.route_lost", n=lost), error=True)
        cs, ox, oy = self.geometry()
        if self.sel and (self.sel[0] >= camp.cols or self.sel[1] >= camp.rows):
            self.sel = None
        sf = self.selected_force()
        if sf is None:
            self.sel_force = None
        supply = camp.supply_map() if camp.logistics else None

        dests: Dict[Tuple[int, int], str] = {}        # destinos válidos de la fuerza seleccionada
        if sf:
            f, _fi, fc = sf
            for n in camp.neighbors(fc.col, fc.row, f.fid):
                hostile = n.owner not in (None, f.fid) or \
                    any(g.fid != f.fid for g, _i, _c in camp.forces_at(n.col, n.row))
                dests[(n.col, n.row)] = "attack" if hostile else "go"

        # ---------------- pasada A: fondos y bordes ----------------
        rects: Dict[Tuple[int, int], pygame.Rect] = {}
        for q in camp.quads:
            r = pygame.Rect(ox + q.col * cs, oy + q.row * cs, cs, cs)
            rects[(q.col, q.row)] = r
            inner = r.inflate(-4, -4)
            pygame.draw.rect(scr, BIOMES[q.biome]["color"], inner, border_radius=6)
            owner = camp.faction(q.owner)
            if owner:
                ov = pygame.Surface(inner.size, pygame.SRCALPHA)
                pygame.draw.rect(ov, (*owner.color, 100), ov.get_rect(), border_radius=6)
                scr.blit(ov, inner.topleft)
                pygame.draw.rect(scr, owner.color, inner, 4, border_radius=6)
            else:
                pygame.draw.rect(scr, (96, 104, 120), inner, 2, border_radius=6)
            if self.sel == (q.col, q.row):
                pygame.draw.rect(scr, (255, 255, 255), r, 3, border_radius=8)
            mode = dests.get((q.col, q.row))
            if mode:
                pygame.draw.rect(scr, C_BAD if mode == "attack" else C_GOOD, r, 3, border_radius=8)
            if self.route_mode == (q.col, q.row):
                pygame.draw.rect(scr, (90, 205, 235), r, 3, border_radius=8)

        self.draw_links(ui, camp, rects, supply)

        # ---------------- pasada B: textos, iconos, fichas y clics ----------------
        max_tok = 3 if cs < 120 else 4
        for q in camp.quads:
            r = rects[(q.col, q.row)]
            inner = r.inflate(-4, -4)
            owner = camp.faction(q.owner)
            ui.text(quad_label(q.col, q.row), (inner.x + 7, inner.y + 5), "m", (250, 250, 250))
            ui.text(ui.fit(q.name, "xs", inner.w - 12), (inner.x + 7, inner.y + 25), "xs", (240, 240, 240))
            if cs >= 112:
                ui.text(biome_name(q.biome), (inner.x + 7, inner.y + 40), "xs", (215, 220, 215))
            tag = tr("camp.free") if not owner else owner.name
            ui.text(ui.fit(tag, "xs", inner.w - 70), (inner.x + 7, inner.bottom - 50), "xs",
                    (255, 255, 255) if owner else (200, 205, 215))
            # marcas: capital (rombo dorado), aislado (!), choque pendiente (X)
            mx, my = inner.right - 12, inner.bottom - 44
            if owner and camp.capital_of(owner) is q:
                pygame.draw.polygon(scr, (240, 200, 70), [(mx, my - 6), (mx + 6, my), (mx, my + 6), (mx - 6, my)])
                pygame.draw.polygon(scr, (20, 20, 24), [(mx, my - 6), (mx + 6, my), (mx, my + 6), (mx - 6, my)], 1)
                mx -= 18
            if owner and supply is not None and (q.col, q.row) not in supply.get(owner.fid, set()):
                pygame.draw.circle(scr, C_BAD, (mx, my), 7)
                ui.text("!", (mx, my), "xs", (255, 255, 255), "center")
                mx -= 18
            if any((c.col, c.row) == (q.col, q.row) for c in camp.clashes):
                pygame.draw.line(scr, C_BAD, (mx - 5, my - 5), (mx + 5, my + 5), 3)
                pygame.draw.line(scr, C_BAD, (mx - 5, my + 5), (mx + 5, my - 5), 3)
            # edificios (solo los construidos)
            per_row = max(1, (inner.w - 14) // 26)
            shown = q.buildings if len(q.buildings) <= per_row else q.buildings[:per_row - 1]
            for i, bk in enumerate(shown):
                sr = pygame.Rect(inner.x + 7 + i * 26, inner.bottom - 28, 22, 22)
                pygame.draw.rect(scr, BUILDINGS[bk]["color"], sr, border_radius=4)
                pygame.draw.rect(scr, (15, 15, 18), sr, 1, border_radius=4)
                ui.text(bshort(bk), sr.center, "s", (15, 15, 18), "center")
            if len(shown) < len(q.buildings):
                ui.text(f"+{len(q.buildings) - len(shown)}", (inner.x + 7 + len(shown) * 26, inner.bottom - 26),
                        "s", (255, 255, 255))
            # fichas de fuerzas presentes
            tokens = []
            present = camp.forces_at(q.col, q.row)
            for k, (g, gi, gf) in enumerate(present[:max_tok]):
                cx, cy = inner.right - 14 - k * 22, inner.y + 15
                pygame.draw.circle(scr, g.color, (cx, cy), 10)
                sel_tok = self.sel_force == (g.fid, gi)
                ring = (255, 255, 255) if sel_tok else ((70, 70, 76) if gf.moved else (18, 18, 22))
                pygame.draw.circle(scr, ring, (cx, cy), 10, 3 if sel_tok else 2)
                lum = 0.3 * g.color[0] + 0.59 * g.color[1] + 0.11 * g.color[2]
                ui.text(str(gi + 1), (cx, cy), "xs", (20, 20, 24) if lum > 150 else (255, 255, 255), "center")
                if gf.moved:
                    pygame.draw.circle(scr, (30, 30, 34), (cx + 8, cy + 8), 3)
                tokens.append((pygame.Rect(cx - 10, cy - 10, 20, 20), g.fid, gi))
            if len(present) > max_tok:
                ui.text(f"+{len(present) - max_tok}", (inner.right - 14 - max_tok * 22 + 8, inner.y + 15),
                        "xs", (255, 255, 255), "center")
            p = ui.take_click(r)
            if p is not None:
                self.on_cell_click(camp, q, dests, tokens, p, sf)

        # ---------------- panel derecho ----------------
        px, pw = 880, 390
        ui.panel((px, 58, pw, 164), tr("camp.title"))
        ui.text(tr("camp.grid"), (px + 12, 84), "s", C_DIM)
        for i, n in enumerate((4, 5, 6)):
            if ui.button((px + 96 + i * 80, 80, 72, 26), f"{n} x {n}", active=(camp.cols == n),
                         tip=tr("camp.grid_tip")):
                camp.generate(n)
                self.sel = self.sel_force = self.route_mode = None
        if ui.button((px + 12, 114, 210, 28), tr("camp.generate"), color=(150, 100, 30),
                     tip=tr("camp.generate_tip")):
            camp.generate(camp.cols)
            self.sel = self.sel_force = self.route_mode = None
        ui.text(tr("camp.seed", n=camp.seed), (px + 236, 120), "s", C_DIM)
        ui.text(tr("camp.maxb"), (px + 12, 156), "xs", C_DIM)
        for i, (lim, lab, w) in enumerate(((2, "2", 40), (3, "3", 40), (4, "4", 40),
                                           (0, tr("camp.unlimited"), 96))):
            bx = px + 168 + [0, 44, 88, 132][i]
            if ui.button((bx, 150, w, 26), lab, active=(camp.max_buildings == lim), font="xs",
                         tip=tr("camp.maxb_tip")):
                camp.max_buildings = lim
        if ui.button((px + 12, 184, 170, 28), tr("camp.logistics", s=tr("on") if camp.logistics else tr("off")),
                     active=camp.logistics, tip=tr("camp.logistics_tip"), font="xs"):
            camp.logistics = not camp.logistics
        if ui.button((px + 190, 184, 188, 28), tr("camp.end_turn"), color=(150, 100, 30)):
            camp.end_turn()
            self.sel_force = None
            self.app.set_status(tr("status.turn_done", n=camp.turn - 1))

        self.draw_details(ui, px, 230, pw, 462)

    # ------------------------------------------------------------------
    def draw_links(self, ui, camp, rects, supply):
        """Conectores entre territorios propios abastecidos y rutas (línea discontinua con el color de su dueño)."""
        scr = ui.screen
        for q in camp.quads:
            if q.owner is None:
                continue
            f = camp.faction(q.owner)
            for dc, dr in ((1, 0), (0, 1)):
                c2, r2 = q.col + dc, q.row + dr
                if not camp.in_bounds(c2, r2):
                    continue
                n = camp.quad(c2, r2)
                if n.owner != q.owner:
                    continue
                if supply is not None:
                    net = supply.get(q.owner, set())
                    if (q.col, q.row) not in net or (c2, r2) not in net:
                        continue
                a, b = rects[(q.col, q.row)], rects[(c2, r2)]
                pr = pygame.Rect(a.right - 12, a.centery - 3, 24, 6) if dc else \
                    pygame.Rect(a.centerx - 3, a.bottom - 12, 6, 24)
                pygame.draw.rect(scr, f.color, pr, border_radius=3)
                pygame.draw.rect(scr, (15, 15, 18), pr, 1, border_radius=3)
        for rt in camp.routes:
            c1, r1, c2, r2 = rt[:4]
            if (c1, r1) not in rects or (c2, r2) not in rects:
                continue
            owner = camp.faction(rt[4]) if len(rt) > 4 else None
            col = lighter(owner.color, 0.25) if owner else (90, 205, 235)
            a, b = rects[(c1, r1)].center, rects[(c2, r2)].center
            self.dashed(scr, a, b, col)
            for pnt in (a, b):
                pygame.draw.circle(scr, (20, 24, 34), pnt, 7)
                pygame.draw.circle(scr, col, pnt, 7, 2)

    def on_cell_click(self, camp, q, dests, tokens, p, sf):
        key = (q.col, q.row)
        if self.route_mode and self.route_mode != key:
            origin = camp.quad(*self.route_mode)
            f = camp.faction(origin.owner)
            err = camp.build_route(f, self.route_mode, key) if f else "err.route_own"
            if err:
                self.app.set_status(tr(err, c=ROUTE_COST_CR), error=True)
            else:
                self.app.set_status(tr("status.route_built", c=ROUTE_COST_CR))
            self.route_mode = None
            return
        if self.route_mode == key:
            self.route_mode = None
            return
        if sf and key in dests:
            self.do_move(camp, q, sf)
            return
        for rect, fid, idx in tokens:
            if rect.collidepoint(p):
                self.sel_force, self.sel, self.dtab = (fid, idx), key, "forces"
                return
        self.sel, self.sel_force = key, None

    def do_move(self, camp, dest, sf):
        f, fi, fc = sf
        name = fc.name
        res = camp.move_force(f, fi, dest)
        if res.startswith("err."):
            self.app.set_status(tr(res), error=True)
            return
        self.app.set_status(tr("status." + res, f=f.name, n=name, q=quad_label(dest.col, dest.row)),
                            error=(res == "clash"))
        self.sel, self.sel_force = (dest.col, dest.row), None
        if res == "clash":
            self.dtab = "forces"

    # ------------------------------------------------------------------
    def draw_details(self, ui, px, py, pw, ph):
        camp = self.app.campaign
        ui.panel((px, py, pw, ph), tr("camp.details"))
        if not self.sel:
            ui.text(tr("camp.hint1"), (px + 16, py + 36), "s", C_DIM)
            ui.text(tr("camp.hint2"), (px + 16, py + 56), "s", C_DIM)
            ui.text(tr("camp.legend"), (px + 16, py + 92), "xs", C_ACCENT)
            for i, k in enumerate(BUILDINGS):
                yy = py + 112 + i * 40
                pygame.draw.rect(ui.screen, BUILDINGS[k]["color"], (px + 16, yy, 24, 24), border_radius=4)
                ui.text(bshort(k), (px + 28, yy + 12), "s", (15, 15, 18), "center")
                ui.text(f"{bname(k)}  ({cost_str(k)})", (px + 50, yy - 2), "s", C_TEXT)
                ui.text(ui.fit(bdesc(k), "xs", pw - 66), (px + 50, yy + 14), "xs", C_DIM)
            return

        q = camp.quad(*self.sel)
        owner = camp.faction(q.owner)
        x = px + 14
        y = py + 24
        ui.text(f"{quad_label(q.col, q.row)} · {q.name}", (x, y), "l", C_TEXT)
        y += 28
        pygame.draw.rect(ui.screen, BIOMES[q.biome]["color"], (x, y + 2, 14, 14), border_radius=3)
        ui.text(tr("camp.biome", b=biome_name(q.biome)), (x + 22, y), "s", C_DIM)
        y += 20
        if owner:
            pygame.draw.rect(ui.screen, owner.color, (x, y + 2, 14, 14), border_radius=3)
            ui.text(tr("camp.occupied", f=owner.name), (x + 22, y), "s", C_TEXT)
            if camp.logistics and not camp.is_supplied(q):
                ui.text(tr("camp.cutoff"), (px + pw - 14, y + 2), "xs", C_BAD, "topright")
        else:
            pygame.draw.rect(ui.screen, (96, 104, 120), (x, y + 2, 14, 14), 2, border_radius=3)
            ui.text(tr("camp.free"), (x + 22, y), "s", C_GOOD)
        y += 24
        tw = (pw - 28 - 8) // 3
        for i, (key, lab) in enumerate((("terr", "camp.tab_terr"), ("forces", "camp.tab_forces"),
                                        ("hist", "camp.tab_hist"))):
            label = tr(lab) + (f" ({len(q.history)})" if key == "hist" and q.history else "")
            if ui.button((x + i * (tw + 4), y, tw, 26), label, active=(self.dtab == key), font="xs"):
                self.dtab = key
        y += 34
        bottom = py + ph - 10
        if self.dtab == "terr":
            self.tab_terr(ui, camp, q, owner, x, y, pw)
        elif self.dtab == "forces":
            self.tab_forces(ui, camp, q, owner, x, y, pw, bottom)
        else:
            self.tab_hist(ui, camp, q, x, y, pw, bottom)

    # ---- pestaña: territorio (propietario y construcciones) -------------
    def tab_terr(self, ui, camp, q, owner, x, y, pw):
        ui.text(tr("camp.assign"), (x, y), "xs", C_ACCENT)
        y += 17
        bw = (pw - 28 - 8) // 3
        for i, f in enumerate(camp.factions):
            rr = (x + (i % 3) * (bw + 4), y + (i // 3) * 30, bw, 26)
            if ui.button(rr, f.name, color=f.color, active=(q.owner == f.fid), font="xs"):
                q.owner = f.fid
        y += max(1, (len(camp.factions) + 2) // 3) * 30
        if ui.button((x, y, 170, 26), tr("camp.release"), enabled=q.owner is not None):
            q.owner = None
        if owner:
            ui.text(f"{owner.cr} CR · {owner.rr} RR", (x + 190, y + 6), "s", C_GOOD)
        y += 34

        lim = f"/{camp.max_buildings}" if camp.max_buildings else ""
        ui.text(tr("camp.buildings", n=len(q.buildings), lim=lim), (x, y), "xs", C_ACCENT)
        y += 17
        cw = (pw - 28 - 4) // 2
        remove_idx = None
        vis = q.buildings[:4]
        if not vis:
            ui.text(tr("camp.none_built"), (x, y + 3), "s", (120, 126, 140))
            y += 28
        for i, k in enumerate(vis):
            rr = (x + (i % 2) * (cw + 4), y + (i // 2) * 28, cw, 24)
            if ui.button(rr, f"{bname(k)}   x", font="xs", swatch=BUILDINGS[k]["color"],
                         align="left", tip=tr("camp.demolish_tip")):
                remove_idx = i
        if vis:
            y += ((len(vis) + 1) // 2) * 28
        if len(q.buildings) > 4:
            ui.text(tr("camp.more", n=len(q.buildings) - 4), (x, y), "xs", C_DIM)
            y += 16
        if remove_idx is not None:
            q.buildings.pop(remove_idx)
        y += 4

        ui.text(tr("camp.build"), (x, y), "xs", C_ACCENT)
        if owner is None:
            ui.text(tr("camp.need_owner"), (x + pw - 28, y), "xs", C_WARN, "topright")
        y += 17
        for i, k in enumerate(BUILDINGS):
            rr = (x + (i % 2) * (cw + 4), y + (i // 2) * 30, cw, 26)
            err = camp.build_error(q, k)
            tip = bdesc(k)
            if err:
                tip += "  —  " + tr(err, cost=cost_str(k))
            if ui.button(rr, f"{bname(k)} ({cost_str(k)})", enabled=err is None, font="xs",
                         swatch=BUILDINGS[k]["color"], align="left", tip=tip):
                e2 = camp.build(q, k)
                if e2:
                    self.app.set_status(tr(e2, cost=cost_str(k)), error=True)
                else:
                    self.app.set_status(tr("status.built", b=bname(k), q=quad_label(q.col, q.row),
                                           cost=cost_str(k)))
        y += 3 * 30 + 4
        bonus = camp.quad_bonus(q)
        parts = [f"+{v} {tr('bonus.' + k)}" for k, v in bonus.items() if v]
        ui.text(tr("camp.bonus"), (x, y), "xs", C_ACCENT)
        ui.text(", ".join(parts) if parts else tr("camp.none"), (x + 150, y), "xs", C_TEXT)

    # ---- pestaña: fuerzas, rutas y batalla --------------------------------
    def tab_forces(self, ui, camp, q, owner, x, y, pw, bottom):
        if owner is not None:
            if not camp.logistics:
                ui.text(tr("camp.logi_off"), (x, y), "xs", C_DIM)
            elif camp.is_supplied(q):
                ui.text(tr("camp.supplied"), (x, y), "xs", C_GOOD)
            else:
                ui.text(tr("camp.cutoff"), (x, y), "xs", C_BAD)
        y += 18
        ui.text(tr("camp.forces"), (x, y), "xs", C_ACCENT)
        y += 17
        present = camp.forces_at(q.col, q.row)
        if not present:
            ui.text(tr("camp.no_forces"), (x, y + 2), "s", (120, 126, 140))
            y += 26
        for g, gi, gf in present[:5]:
            units = [u for u in gf.units if u.status == "active"]
            row = pygame.Rect(x, y, pw - 28, 26)
            pygame.draw.rect(ui.screen, C_PANEL2, row, border_radius=4)
            pygame.draw.circle(ui.screen, g.color, (row.x + 13, row.centery), 9)
            lum = 0.3 * g.color[0] + 0.59 * g.color[1] + 0.11 * g.color[2]
            ui.text(str(gi + 1), (row.x + 13, row.centery), "xs", (20, 20, 24) if lum > 150 else (255, 255, 255), "center")
            line = tr("camp.force_line", f=g.name, n=gf.army_name or gf.name, u=len(units),
                      p=sum(u.pts for u in units))
            ui.text(ui.fit(line, "xs", row.w - 120), (row.x + 30, row.centery), "xs", C_TEXT, "midleft")
            if ui.button((row.right - 80, row.y + 2, 76, 22), tr("camp.moved") if gf.moved else tr("camp.move"),
                         enabled=not gf.moved, font="xs", active=(self.sel_force == (g.fid, gi)),
                         tip=tr("camp.move_tip")):
                self.sel_force = (g.fid, gi)
            y += 28
        y += 2
        for c in [c for c in camp.clashes if (c.col, c.row) == (q.col, q.row)][:1]:
            a, d = camp.faction(c.att_fid), camp.faction(c.def_fid)
            ui.text(ui.fit(tr("camp.clash", a=a.name if a else "?", d=d.name if d else "?"), "xs", pw - 28),
                    (x, y), "xs", C_BAD)
            y += 18

        ui.text(tr("camp.routes"), (x, y), "xs", C_ACCENT)
        y += 17
        mine = [rt for rt in camp.routes if (rt[0], rt[1]) == (q.col, q.row) or (rt[2], rt[3]) == (q.col, q.row)]
        if not mine:
            ui.text(tr("camp.no_routes"), (x, y + 2), "s", (120, 126, 140))
            y += 24
        for rt in mine[:3]:
            other = camp.quad(rt[2], rt[3]) if (rt[0], rt[1]) == (q.col, q.row) else camp.quad(rt[0], rt[1])
            ui.text(ui.fit(f"-> {quad_label(other.col, other.row)} · {other.name}", "xs", pw - 80), (x, y + 5),
                    "xs", (120, 215, 240))
            if ui.button((x + pw - 28 - 28, y, 28, 24), "x", font="xs", tip=tr("camp.route_del_tip")):
                camp.routes = [r2 for r2 in camp.routes if r2 is not rt]
            y += 26
        active = self.route_mode == (q.col, q.row)
        if ui.button((x, y, pw - 28, 26), tr("camp.route_pick") if active else tr("camp.add_route", c=ROUTE_COST_CR),
                     enabled=owner is not None, active=active, font="xs", tip=tr("camp.add_route_tip")):
            self.route_mode = None if active else (q.col, q.row)

        by = bottom - 30
        half = (pw - 28 - 4) // 2
        if ui.button((x, by, half, 30), tr("camp.prepare_short"), color=(150, 100, 30), font="xs",
                     tip=tr("camp.prepare_tip")):
            self.app.start_battle_for(q)
        if ui.button((x + half + 4, by, half, 30), tr("camp.record"), color=(60, 120, 76), font="xs",
                     enabled=len(camp.factions) > 0, tip=tr("camp.record_tip")):
            self.app.open_result(q)

    # ---- pestaña: historial -----------------------------------------------
    def tab_hist(self, ui, camp, q, x, y, pw, bottom):
        ui.text(tr("camp.hist_title", n=len(q.history)), (x, y), "xs", C_ACCENT)
        y += 18
        if not q.history:
            ui.text(tr("camp.hist_empty"), (x, y + 2), "s", C_DIM)
            return
        recs = list(reversed(q.history))
        vis = max(1, (bottom - y) // 40)
        if ui.over((x, y, pw - 28, bottom - y)) and ui.wheel:
            self.hist_scroll -= ui.wheel
        self.hist_scroll = clamp(self.hist_scroll, 0, max(0, len(recs) - vis))
        for i in range(self.hist_scroll, min(len(recs), self.hist_scroll + vis)):
            rec = recs[i]
            row = pygame.Rect(x, y + (i - self.hist_scroll) * 40, pw - 28, 36)
            pygame.draw.rect(ui.screen, C_PANEL2, row, border_radius=4)
            wf = camp.faction(rec.att_fid if rec.winner == "att" else rec.def_fid if rec.winner == "def" else None)
            pygame.draw.rect(ui.screen, wf.color if wf else (110, 116, 130), (row.x, row.y, 5, row.h),
                             border_radius=2)
            wtxt = (tr("camp.won", f=rec.att_name) if rec.winner == "att" else
                    tr("camp.won", f=rec.def_name) if rec.winner == "def" else tr("camp.draw"))
            ui.text(tr("camp.hist_l1", t=rec.turn, d=rec.date), (row.x + 12, row.y + 3), "xs", C_DIM)
            l2 = tr("camp.hist_l2", a=rec.att_name, b=rec.def_name, w=wtxt, la=rec.att_losses, ld=rec.def_losses)
            if rec.att_destroyed or rec.def_destroyed:
                l2 += tr("camp.destroyed_note", a=rec.att_destroyed, d=rec.def_destroyed)
            ui.text(ui.fit(l2, "xs", row.w - 20), (row.x + 12, row.y + 19), "xs", C_TEXT)
            if rec.note and ui.over(row):
                ui.tip = rec.note


# -----------------------------------------------------------------------------
#  Vista 2: Generador de batalla
# -----------------------------------------------------------------------------
class BattleView(View):
    AREA = pygame.Rect(332, 56, 938, 538)

    def __init__(self, app):
        super().__init__(app)
        self.drag: Optional[Tuple[int, float, float]] = None
        self.ltab = "terrain"           # pestaña del panel izquierdo: terrain | deploy | rules
        self.rule_target = "type"       # a qué se aplican los interruptores de reglas

    def layout(self):
        b = self.app.battle
        ml, mt, mr, mb = 30, 42, 10, 8
        avail_w = self.AREA.w - ml - mr
        avail_h = self.AREA.h - mt - mb
        sc = min(avail_w / b.W, avail_h / b.H)
        ox = self.AREA.x + ml + (avail_w - b.W * sc) / 2
        oy = self.AREA.y + mt + (avail_h - b.H * sc) / 2
        return sc, ox, oy

    def handle_event(self, e, ui: UI):
        b = self.app.battle
        sc, ox, oy = self.layout()
        board = pygame.Rect(int(ox), int(oy), int(b.W * sc), int(b.H * sc))

        if e.type == pygame.MOUSEBUTTONDOWN and board.collidepoint(e.pos):
            bx, by = (e.pos[0] - ox) / sc, (e.pos[1] - oy) / sc
            if e.button == 1:
                idx = b.hit(bx, by)
                if idx is not None:
                    b.sel_piece = idx
                    p = b.pieces[idx]
                    self.drag = (idx, bx - p.x, by - p.y)
                elif b.manual:
                    t = b.type_by_key(b.sel_type)
                    if t:
                        p = TerrainPiece(t.key, round(bx * 2) / 2, round(by * 2) / 2,
                                         t.w, t.h, random.randint(0, 10 ** 6), list(t.rules))
                        b.clamp_piece(p)
                        b.pieces.append(p)
                        b.sel_piece = len(b.pieces) - 1
                        b.last_msg = tr("bt.added", n=t.label())
                else:
                    b.sel_piece = None
            elif e.button == 3:
                idx = b.hit(bx, by)
                if idx is not None:
                    b.pieces.pop(idx)
                    b.sel_piece = None
        elif e.type == pygame.MOUSEMOTION and self.drag:
            idx, dx, dy = self.drag
            if idx < len(b.pieces):
                p = b.pieces[idx]
                p.x = (e.pos[0] - ox) / sc - dx
                p.y = (e.pos[1] - oy) / sc - dy
                b.clamp_piece(p)
        elif e.type == pygame.MOUSEBUTTONUP and e.button == 1:
            if self.drag and self.drag[0] < len(b.pieces):
                p = b.pieces[self.drag[0]]
                p.x, p.y = round(p.x * 2) / 2, round(p.y * 2) / 2
            self.drag = None
        elif e.type == pygame.KEYDOWN and ui.focus is None:
            if e.key == pygame.K_r and b.sel_piece is not None:
                b.rotate(b.sel_piece)
            elif e.key in (pygame.K_DELETE, pygame.K_BACKSPACE) and b.sel_piece is not None:
                b.pieces.pop(b.sel_piece)
                b.sel_piece = None
            elif e.key == pygame.K_g:
                b.generate(False)

    # ------------------------------------------------------------------
    def draw(self, ui: UI):
        b = self.app.battle
        scr = ui.screen
        ui.panel((8, 54, 316, 640))
        for i, (key, lab) in enumerate((("terrain", "bt.tab_terrain"), ("deploy", "bt.tab_deploy"),
                                        ("rules", "bt.tab_rules"))):
            if ui.button((14 + i * 102, 60, 98, 26), tr(lab), active=(self.ltab == key), font="xs"):
                self.ltab = key
        if self.ltab == "terrain":
            self.draw_terrain_tab(ui, b)
        elif self.ltab == "deploy":
            self.draw_deploy_tab(ui, b)
        else:
            self.draw_rules_tab(ui, b)

        # ======== cabecera y tablero ========
        sc, ox, oy = self.layout()
        title = tr("bt.title", w=b.W, h=b.H, fw=f"{b.W / 30:.0f}", fh=f"{b.H / 30:.0f}")
        title += f"  ·  {tr('deploy.' + b.deploy)}"
        if b.condition:
            title += f"  ·  {rname(b.condition)}"
        if b.context:
            title += f"  ·  {b.context}"
        ui.text(ui.fit(title, "m", 600), (self.AREA.x + 4, self.AREA.y + 2), "m", C_TEXT)
        ui.text(tr("bt.help"), (self.AREA.right - 4, self.AREA.y + 5), "xs", C_DIM, "topright")
        draw_board(scr, b, ox, oy, sc, self.app.fonts, sel=b.sel_piece)
        self.draw_strip(ui, b)

    # ------------------------------ pestaña: terreno ------------------------------
    def draw_terrain_tab(self, ui: UI, b: BattleState):
        ui.text(tr("bt.size"), (18, 94), "xs", C_ACCENT)
        for i, (w, h) in enumerate(BOARD_SIZES):
            r = (16 + (i % 2) * 152, 110 + (i // 2) * 30, 148, 26)
            if ui.button(r, f"{w} x {h} cm", active=(i == b.size_idx), tip=tr("bt.size_tip")) \
                    and i != b.size_idx:
                b.set_size(i)
        ui.text(tr("bt.seed", n=b.seed), (18, 176), "s", C_DIM)
        if ui.button((200, 170, 116, 26), tr("bt.random"), font="xs"):
            b.seed = random.randint(1, 99999)

        ui.text(tr("bt.pool"), (18, 206), "xs", C_ACCENT)
        ui.text(tr("bt.pool_hint"), (118, 207), "tiny", C_DIM)
        y = 224
        for t in b.types:
            if ui.button((14, y, 170, 22), t.label(), active=(t.key == b.sel_type), align="left",
                         swatch=t.color, font="xs", tip=t.fx()):
                b.sel_type = t.key
            b.counts[t.key] = ui.stepper((190, y, 126, 22), b.counts.get(t.key, 0), 0, 60)
            y += 24
        y += 6

        def row(y0, left, right):
            res = []
            for i, (label, kw) in enumerate((left, right)):
                res.append(ui.button((16 + i * 152, y0, 148, 28), label, **kw))
            return res

        a, c = row(y, (tr("bt.auto"), dict(tip=tr("bt.auto_tip"))),
                   (tr("bt.clear_pool"), dict(tip=tr("bt.clear_pool_tip"))))
        if a:
            b.auto_counts()
        if c:
            for k in b.counts:
                b.counts[k] = 0
        y += 32
        a, c = row(y, (tr("bt.gen"), dict(color=(150, 100, 30), tip=tr("bt.gen_tip"))),
                   (tr("bt.fill"), dict(tip=tr("bt.fill_tip"))))
        if a:
            b.generate(False)
        if c:
            b.generate(True)
        y += 32
        a, c = row(y, (tr("bt.clear"), dict(tip=tr("bt.clear_tip"))),
                   (tr("bt.manual", s=tr("on") if b.manual else tr("off")),
                    dict(active=b.manual, tip=tr("bt.manual_tip"))))
        if a:
            b.pieces = []
            b.sel_piece = None
            b.last_msg = tr("bt.cleared")
        if c:
            b.manual = not b.manual
        y += 32
        if ui.button((16, y, 300, 28), tr("bt.export"), tip=tr("bt.export_tip")):
            try:
                png, _js = export_battle(b, self.app.fonts)
                b.last_msg = tr("bt.exported", f=os.path.basename(png))
                self.app.set_status(tr("status.exported", path=EXPORT_DIR))
            except Exception as ex:  # noqa
                self.app.set_status(tr("status.export_err", err=ex), error=True)
        y += 36
        ui.text(tr("bt.onboard", n=len(b.pieces), m=sum(b.counts.values())), (18, y), "s", C_TEXT)
        for i, line in enumerate(ui.wrap(b.last_msg, "xs", 290)[:3]):
            ui.text(line, (18, y + 22 + i * 15), "xs", C_DIM)

    # ------------------------------ pestaña: despliegue ------------------------------
    def draw_deploy_tab(self, ui: UI, b: BattleState):
        ui.text(tr("dep.title"), (18, 94), "xs", C_ACCENT)
        for i, k in enumerate(DEPLOY_TYPES):
            r = (16 + (i % 2) * 152, 112 + (i // 2) * 32, 148, 28)
            if ui.button(r, tr(f"deploy.{k}"), active=(b.deploy == k), font="xs", tip=tr(f"deploy.{k}.d")):
                b.deploy = k
        if ui.button((16, 212, 148, 28), tr("dep.random"), tip=tr("dep.random_tip"), font="xs"):
            roll = random.randint(1, 6)
            b.deploy = DEPLOY_TYPES[roll - 1]
            b.last_msg = tr("dep.rolled", n=roll, name=tr("deploy." + b.deploy))
        if ui.button((168, 212, 148, 28), tr("dep.swap"), tip=tr("dep.swap_tip"), font="xs",
                     active=b.flip):
            b.flip = not b.flip
        ui.text(tr("dep.depth"), (18, 254), "s", C_DIM)
        cur = int(round(b.eff_depth()))
        new = ui.stepper((110, 248, 130, 26), cur, 5, 60, 1, "{} cm")
        if new != cur:
            b.depth = float(new)
        if ui.button((248, 248, 68, 26), tr("dep.auto"), active=b.depth is None, font="xs"):
            b.depth = None
        if ui.button((16, 284, 300, 28), tr("dep.zones", s=tr("on") if b.show_zones else tr("off")),
                     active=b.show_zones):
            b.show_zones = not b.show_zones

        y = 326
        for line in ui.wrap(tr(f"deploy.{b.deploy}.d"), "s", 292):
            ui.text(line, (18, y), "s", C_TEXT)
            y += 19
        y += 10
        pygame.draw.rect(ui.screen, (210, 70, 70), (18, y + 2, 14, 12), border_radius=2)
        pygame.draw.rect(ui.screen, (70, 110, 220), (170, y + 2, 14, 12), border_radius=2)
        owner_a = "A" if not b.flip else "B"
        roles = {"A": tr(f"deploy.{b.deploy}.ra"), "B": tr(f"deploy.{b.deploy}.rb")}
        red_role = roles["A"] if owner_a == "A" else roles["B"]
        blue_role = roles["B"] if owner_a == "A" else roles["A"]
        ui.text(ui.fit(red_role, "xs", 130), (38, y + 1), "xs", C_TEXT)
        ui.text(ui.fit(blue_role, "xs", 130), (190, y + 1), "xs", C_TEXT)
        y += 30
        for line in ui.wrap(tr("dep.note"), "xs", 292):
            ui.text(line, (18, y), "xs", C_DIM)
            y += 15
        if b.last_msg:
            y += 8
            for line in ui.wrap(b.last_msg, "xs", 292)[:2]:
                ui.text(line, (18, y), "xs", C_GOOD)
                y += 15

    # ------------------------------ pestaña: reglas ------------------------------
    def roll_condition(self, b: BattleState):
        d = random.randint(1, 6)
        if d <= 2:
            b.condition = ""
            b.last_msg = tr("rl.rolled_none", d=d)
            return
        kind, pool = (("rl.kind_geo", GEO_RULES) if d <= 4 else ("rl.kind_myst", MYST_RULES))
        b.condition = random.choice(pool)
        b.last_msg = tr("rl.rolled", d=d, k=tr(kind), c=rname(b.condition))

    def draw_rules_tab(self, ui: UI, b: BattleState):
        ui.text(tr("rl.title"), (18, 94), "xs", C_ACCENT)
        if ui.button((16, 110, 148, 28), tr("rl.none"), active=(b.condition == ""), font="xs"):
            b.condition = ""
        if ui.button((168, 110, 148, 28), tr("rl.roll"), tip=tr("rl.roll_tip"), font="xs"):
            self.roll_condition(b)
        ui.text(tr("rl.geo"), (18, 146), "xs", C_DIM)
        for i, k in enumerate(GEO_RULES):
            if ui.button((16 + (i % 2) * 152, 162 + (i // 2) * 28, 148, 24), rname(k), font="xs",
                         active=(b.condition == k), swatch=RULE_COLORS["geo"], align="left", tip=rdesc(k)):
                b.condition = k
        ui.text(tr("rl.myst"), (18, 224), "xs", C_DIM)
        for i, k in enumerate(MYST_RULES):
            if ui.button((16 + (i % 2) * 152, 240 + (i // 2) * 28, 148, 24), rname(k), font="xs",
                         active=(b.condition == k), swatch=RULE_COLORS["myst"], align="left", tip=rdesc(k)):
                b.condition = k
        y = 328
        if b.condition:
            for line in ui.wrap(rdesc(b.condition), "xs", 292)[:5]:
                ui.text(line, (18, y), "xs", C_TEXT)
                y += 14
        else:
            ui.text(ui.fit(tr("rl.no_cond"), "xs", 292), (18, y), "xs", C_DIM)
        pygame.draw.line(ui.screen, C_LINE, (16, 404), (316, 404))
        ui.text(tr("rl.terrain_title"), (18, 410), "xs", C_ACCENT)
        ui.text(tr("rl.note"), (316, 410), "tiny", C_DIM, "topright")

        t = b.type_by_key(b.sel_type)
        piece = b.pieces[b.sel_piece] if (b.sel_piece is not None and b.sel_piece < len(b.pieces)) else None
        if piece is None and self.rule_target == "piece":
            self.rule_target = "type"
        if ui.button((16, 426, 148, 26), tr("rl.target_type", n=t.label() if t else "?"),
                     active=(self.rule_target == "type"), font="xs", tip=tr("rl.target_tip")):
            self.rule_target = "type"
        if ui.button((168, 426, 148, 26), tr("rl.target_piece", i=(b.sel_piece or 0) + 1),
                     enabled=piece is not None, active=(self.rule_target == "piece"), font="xs",
                     tip=tr("rl.target_tip")):
            self.rule_target = "piece"
        lst = piece.rules if (self.rule_target == "piece" and piece is not None) else (t.rules if t else [])
        for i, k in enumerate(RULE_ORDER):
            r = (16 + (i % 2) * 152, 458 + (i // 2) * 24, 148, 22)
            if ui.button(r, rname(k), active=(k in lst), font="xs", align="left",
                         swatch=RULE_COLORS[RULE_CATS[k]], tip=rdesc(k)):
                if k in lst:
                    lst.remove(k)
                else:
                    lst.append(k)
        if t and ui.button((16, 656, 300, 26), tr("rl.apply"), font="xs", tip=tr("rl.apply_tip")):
            n = 0
            for p in b.pieces:
                if p.type_key == t.key:
                    p.rules = list(t.rules)
                    n += 1
            b.last_msg = tr("rl.applied", n=n)

    # ------------------------------ franja inferior ------------------------------
    def draw_strip(self, ui: UI, b: BattleState):
        ui.panel((332, 600, 938, 94), tr("bt.editor"))
        t = b.type_by_key(b.sel_type)
        if t:
            x0, y0 = 342, 622
            cur = t.raw_name()
            new = ui.text_field(f"tname_{t.key}", (x0, y0, 170, 26), cur, 20)
            if new != cur:
                t.name, t.renamed = new, True
            ui.text(tr("bt.w"), (x0 + 184, y0 + 5), "xs", C_DIM)
            t.w = ui.stepper((x0 + 228, y0, 100, 26), int(t.w), 2, 60, 1, "{} cm")
            ui.text(tr("bt.h"), (x0 + 344, y0 + 5), "xs", C_DIM)
            t.h = ui.stepper((x0 + 376, y0, 100, 26), int(t.h), 2, 60, 1, "{} cm")
            shape = tr("bt.ellipse") if t.shape == "ellipse" else tr("bt.rect")
            if ui.button((x0 + 492, y0, 120, 26), tr("bt.shape", s=shape), tip=tr("bt.shape_tip")):
                t.shape = "rect" if t.shape == "ellipse" else "ellipse"
            if ui.button((x0 + 624, y0, 130, 26), tr("bt.del_type"), enabled=len(b.types) > 1,
                         tip=tr("bt.del_type_tip")):
                b.remove_type(t.key)
        y1 = 658
        if ui.button((342, y1, 120, 26), tr("bt.new_type"), enabled=len(b.types) < MAX_TERRAIN_TYPES,
                     tip=tr("bt.new_type_tip")):
            b.add_custom_type()
        if b.sel_piece is not None and b.sel_piece < len(b.pieces):
            p = b.pieces[b.sel_piece]
            pt = b.type_by_key(p.type_key)
            txt = tr("bt.piece", i=b.sel_piece + 1, n=pt.label() if pt else "?", w=p.w, h=p.h,
                     x=p.x, y=p.y)
            if p.rules:
                txt += "  [" + ", ".join(rname(k) for k in p.rules if k in RULE_CATS) + "]"
            ui.text(ui.fit(txt, "s", 540), (476, y1 + 5), "s", C_TEXT)
            if ui.button((1020, y1, 110, 26), tr("bt.rotate")):
                b.rotate(b.sel_piece)
            if ui.button((1140, y1, 120, 26), tr("bt.delete"), color=(120, 50, 50)):
                b.pieces.pop(b.sel_piece)
                b.sel_piece = None
        else:
            ui.text(tr("bt.select_hint"), (476, y1 + 5), "s", C_DIM)


# -----------------------------------------------------------------------------
#  Vista 3: Facciones, recursos y listas de ejército
# -----------------------------------------------------------------------------
class FactionView(View):
    STATUS_COL = {"active": C_GOOD, "reserve": C_WARN, "fallen": C_BAD, "destroyed": (112, 112, 124)}
    ROW_H = 26
    VISIBLE = 16

    def __init__(self, app):
        super().__init__(app)
        self.army_fid: Optional[int] = None      # facción cuya lista se edita
        self.army_fi = 0                         # ejército (fuerza) que se edita
        self.sel_unit: Optional[int] = None
        self.scroll = 0
        self.import_src = ""
        self.import_replace = True
        self.ed_tab = "unit"                     # unit | xp
        self.fetcher = ArmyFetcher()
        self.msg = ""
        self.msg_err = False

    # =====================================================================
    def draw(self, ui: UI):
        if self.army_fid is not None:
            fac = self.app.campaign.faction(self.army_fid)
            if fac is None or not fac.forces:
                self.army_fid = None
            else:
                self.draw_army(ui)
                return
        self.draw_table(ui)

    # ------------------------- tabla de facciones ------------------------
    def draw_table(self, ui: UI):
        camp = self.app.campaign
        ui.panel((20, 58, 1240, 410), tr("fac.title"))
        heads = [("fac.h_name", 70), ("fac.h_terr", 266), ("fac.h_bld", 310), ("fac.h_cr", 346),
                 ("fac.h_rr", 466), ("fac.h_units", 592), ("fac.h_fallen", 722),
                 ("fac.h_income", 772), ("fac.h_armies", 925)]
        for key, x in heads:
            ui.text(tr(key), (x, 80), "xs", C_DIM)

        remove = None
        for i, f in enumerate(camp.factions):
            y = 102 + i * 54
            pygame.draw.rect(ui.screen, C_PANEL2, (30, y - 4, 1220, 48), border_radius=6)
            if ui.button((38, y + 2, 28, 28), "", color=f.color, tip=tr("fac.color_tip")):
                f.color_idx = (f.color_idx + 1) % len(FACTION_COLORS)
            f.name = ui.text_field(f"fname_{f.fid}", (72, y, 180, 28), f.name, 22)
            opr = (f.opr_faction or {}).get("name") or tr("fac.no_opr")
            ui.text(ui.fit(tr("fac.opr_line", s=f.army_system, f=opr), "xs", 180), (74, y + 30), "xs", C_DIM)
            inc = camp.income(f.fid)
            ui.text(str(inc["quads"]), (270, y + 9), "m", C_TEXT)
            ui.text(str(inc["builds"]), (314, y + 9), "m", C_TEXT)
            f.cr = ui.stepper((346, y + 4, 112, 28), f.cr, 0, 9999)
            f.rr = ui.stepper((466, y + 4, 112, 28), f.rr, 0, 9999)
            units = f.all_units()
            ui.text(tr("fac.units_val", n=len(units), pts=f.pts_total()), (592, y + 2), "xs", C_TEXT)
            ui.text(f"{f.pts_total('active')} pts", (592, y + 20), "xs", C_DIM)
            ui.text(str(f.fallen()), (736, y + 9), "m", C_BAD if f.fallen() else C_TEXT)
            ui.text(tr("fac.income1", cr=inc["cr"], rr=inc["rr"]), (772, y + 2), "xs", C_GOOD)
            up = camp.upkeep(f)
            ui.text(tr("fac.income2", up=up), (772, y + 20), "xs", C_BAD if up > f.cr + inc["cr"] else C_DIM)
            ui.text(tr("fac.armies_n", n=len(f.forces), m=MAX_FORCES), (925, y + 11), "s", C_TEXT)
            err = camp.force_create_error(f)
            tip = tr("fac.new_army_tip") + (("  —  " + tr(err, c=FORCE_COST_CR)) if err else "")
            if ui.button((960, y + 4, 64, 28), tr("fac.new_army", c=FORCE_COST_CR), enabled=err is None,
                         font="xs", tip=tip):
                camp.create_force(f)
                self.app.set_status(tr("status.force_created", n=f.forces[-1].name, c=FORCE_COST_CR))
            if ui.button((1030, y + 4, 100, 28), tr("fac.army"), color=(150, 100, 30), enabled=bool(f.forces),
                         tip=tr("fac.army_tip")):
                self.army_fid, self.army_fi, self.sel_unit, self.scroll, self.msg = f.fid, 0, None, 0, ""
            if ui.button((1140, y + 4, 100, 28), tr("fac.delete"), enabled=len(camp.factions) > 1,
                         color=(110, 48, 48), font="xs"):
                remove = f.fid
        if remove is not None:
            camp.remove_faction(remove)

        by = 102 + max(1, len(camp.factions)) * 54 + 6
        if ui.button((30, by, 170, 32), tr("fac.add"), enabled=len(camp.factions) < 6,
                     tip=tr("fac.add_tip")):
            camp.add_faction()
        ui.text(tr("fac.turn", n=camp.turn), (216, by + 6), "l", C_ACCENT)
        ui.text(tr("fac.ptsrr"), (390, by + 9), "s", C_DIM)
        camp.pts_per_rr = ui.stepper((490, by + 2, 118, 28), camp.pts_per_rr, 5, 200, 5)
        if ui.over((490, by + 2, 118, 28)):
            ui.tip = tr("fac.ptsrr_tip")
        if ui.button((920, by, 320, 32), tr("fac.end_turn"), color=(150, 100, 30),
                     tip=tr("fac.end_turn_tip")):
            camp.end_turn()
            self.app.set_status(tr("status.turn_done", n=camp.turn - 1))

        ui.panel((20, 478, 1240, 214), tr("fac.log"))
        for i, line in enumerate(reversed(camp.log[-9:])):
            ui.text(ui.fit(line, "s", 1210), (34, 502 + i * 20), "s", C_TEXT if i == 0 else C_DIM)

    # ------------------------- lista de ejército -------------------------
    def set_msg(self, text, err=False):
        self.msg, self.msg_err = text, err

    def apply_import(self, fac: Faction, fi: int, res: dict):
        """Las unidades importadas entran SIEMPRE en reserva en el ejército seleccionado."""
        camp = self.app.campaign
        fc = fac.forces[fi]
        units = res["units"]
        for u in units:
            u.status = "reserve"
            u.rr_cost = default_rr(u.pts, camp.pts_per_rr)
        if self.import_replace:
            fc.units = units
            self.sel_unit = 0 if units else None
        else:
            self.sel_unit = len(fc.units)
            fc.units.extend(units)
        if res.get("name") and (self.import_replace or not fc.army_name):
            fc.army_name = res["name"][:60]
        warn = ""
        if res.get("system"):
            code = normalize_system(res["system"])
            if code != "GEN":
                if camp.system == "GEN" and fac.army_system == "GEN":
                    fac.army_system = code
                elif fac.army_system not in ("GEN", code):
                    warn = tr("army.sys_mismatch", a=code, b=fac.army_system)
        if not fc.points_limit:
            fc.points_limit = int(res.get("list_pts") or SYSTEMS[fac.army_system]["pts"])
        if res.get("source"):
            fc.army_source = res["source"]
        self.scroll = 0
        total = sum(u.pts for u in units)
        msg = tr("army.imported", n=len(units), pts=total) + warn
        if res.get("list_pts") and res["list_pts"] != total:
            msg += tr("army.list_pts_warn", n=res["list_pts"])
        self.set_msg(msg)

    def import_text(self, fac: Faction, fi: int, text: str, source: str = ""):
        try:
            res = parse_any(text)
            res["source"] = source
            self.apply_import(fac, fi, res)
        except Exception as ex:  # noqa
            self.set_msg(tr("army.err_parse", err=ex), True)

    def start_import(self, fac: Faction, fi: int):
        src_text = self.import_src.strip()
        if not src_text:
            self.set_msg(tr("army.err_src"), True)
            return
        path = os.path.expanduser(src_text.strip('"'))
        if os.path.isfile(path):
            try:
                with open(path, "r", encoding="utf-8-sig", errors="replace") as fh:
                    self.import_text(fac, fi, fh.read(), path)
            except OSError as ex:
                self.set_msg(tr("army.err_parse", err=ex), True)
        else:
            self.set_msg(tr("army.fetching"))
            self.fetcher.start(src_text)

    def change_unit_status(self, fac: Faction, fi: int, u: ArmyUnit, st: str):
        camp = self.app.campaign
        old = u.status
        err = camp.change_status(fac, fi, u, st)
        if err:
            self.set_msg(tr(err), True)
        elif old == "reserve" and st == "active":
            self.set_msg(tr("army.recruited", u=u.name, c=u.rr_cost))
        elif old == "active" and st == "reserve":
            self.set_msg(tr("army.refunded", u=u.name, n=u.rr_cost // 2))

    def draw_army(self, ui: UI):
        camp = self.app.campaign
        fac = camp.faction(self.army_fid)
        self.army_fi = clamp(self.army_fi, 0, len(fac.forces) - 1)
        fi = self.army_fi
        fc = fac.forces[fi]

        res, err = self.fetcher.take()               # resultado de la descarga en segundo plano
        if res:
            self.apply_import(fac, fi, res)
        elif err:
            self.set_msg(tr("army.err_net", err=err), True)

        units = fc.units
        n = len(units)
        self.sel_unit = None if n == 0 else (None if self.sel_unit is None else clamp(self.sel_unit, 0, n - 1))

        # =============== panel izquierdo: ejércitos y lista ===============
        L = pygame.Rect(20, 58, 640, 636)
        ui.panel(L, tr("army.title", f=fac.name))
        pygame.draw.rect(ui.screen, fac.color, (L.right - 34, L.y + 8, 20, 14), border_radius=3)
        for i, g in enumerate(fac.forces):
            tip = f"{g.name} · {quad_label(g.col, g.row)} · {len(g.units)} / {g.pts_total()} pts"
            if ui.button((32 + i * 124, 78, 120, 24), f"{i + 1}. {g.army_name or g.name}",
                         active=(i == fi), font="xs", tip=tip):
                self.army_fi, self.sel_unit, self.scroll = i, None, 0
                return
        if len(fac.forces) < MAX_FORCES:
            err = camp.force_create_error(fac)
            if ui.button((32 + len(fac.forces) * 124, 78, 92, 24), tr("army.new_army_btn", c=FORCE_COST_CR),
                         enabled=err is None, font="xs",
                         tip=tr("fac.new_army_tip") + (("  —  " + tr(err, c=FORCE_COST_CR)) if err else "")):
                camp.create_force(fac)
                self.army_fi, self.sel_unit, self.scroll = len(fac.forces) - 1, None, 0
                self.set_msg(tr("status.force_created", n=fac.forces[-1].name, c=FORCE_COST_CR))
                return

        for lab, x in ((tr("army.list_name"), 32), (tr("army.system"), 238), (tr("army.opr_faction"), 330),
                       (tr("army.limit"), 526)):
            ui.text(lab, (x, 108), "xs", C_DIM)
        fc.army_name = ui.text_field(f"aname_{fac.fid}_{fi}", (32, 122, 198, 28), fc.army_name, 60)
        code = fac.army_system if fac.army_system in SYSTEMS else "GEN"
        locked = camp.system != "GEN"
        if ui.button((238, 122, 84, 28), code, enabled=not locked,
                     tip=(tr("army.sys_locked") + "  " if locked else "") + sys_info(code) + "  [" + tr("army.system_tip") + "]"):
            nxt = SYS_ORDER[(SYS_ORDER.index(code) + 1) % len(SYS_ORDER)]
            if fc.points_limit in (0, SYSTEMS[code]["pts"]):
                fc.points_limit = SYSTEMS[nxt]["pts"]
            fac.army_system = nxt
            if fac.opr_faction and fac.opr_faction.get("system") != nxt:
                fac.opr_faction = None
        oname = (fac.opr_faction or {}).get("name") or tr("army.opr_none")
        if ui.button((330, 122, 188, 28), oname, enabled=code != "GEN", tip=tr("army.opr_tip"), font="xs"):
            self.app.open_books(fac.fid)
        fc.points_limit = ui.stepper((526, 122, 124, 28), fc.points_limit, 0, 99999, 50, "{} pts")
        if ui.over((526, 122, 124, 28)):
            ui.tip = tr("army.limit_tip")
        ui.text(tr("army.totals", n=n, pts=fc.pts_total(), a=fc.pts_total("active"), f=fc.count("fallen")),
                (32, 156), "xs", C_TEXT)
        warns = army_warnings(fc, code)
        if warns:
            txt = warns[0] + (tr("army.warn_more", n=len(warns) - 1) if len(warns) > 1 else "")
            ui.text(ui.fit(txt, "xs", 612), (32, 169), "xs", C_WARN)
            if ui.over((32, 167, 620, 14)):
                ui.tip = "  |  ".join(warns)
        cols = [(tr("army.h_unit"), 54), (tr("army.h_mod"), 384), (tr("army.h_q"), 428),
                (tr("army.h_d"), 462), (tr("army.h_pts"), 500), (tr("army.h_rr"), 556),
                (tr("army.col_xp"), 596)]
        for lab, x in cols:
            ui.text(lab, (x, 184), "xs", C_DIM)

        if ui.over(L) and ui.wheel:
            self.scroll -= ui.wheel * 2
        self.scroll = clamp(self.scroll, 0, max(0, n - self.VISIBLE))
        if n == 0:
            ui.text(tr("army.no_units"), (32, 214), "s", C_DIM)
        for idx in range(self.scroll, min(n, self.scroll + self.VISIBLE)):
            u = units[idx]
            y = 200 + (idx - self.scroll) * self.ROW_H
            row = pygame.Rect(30, y, 620, self.ROW_H - 2)
            if idx == self.sel_unit:
                pygame.draw.rect(ui.screen, (74, 62, 36), row, border_radius=4)
                pygame.draw.rect(ui.screen, C_ACCENT, row, 1, border_radius=4)
            elif ui.over(row):
                pygame.draw.rect(ui.screen, C_PANEL2, row, border_radius=4)
            dim = u.status == "destroyed"
            tcol = (120, 122, 132) if dim else C_TEXT
            pygame.draw.rect(ui.screen, self.STATUS_COL[u.status], (36, y + 5, 10, 14), border_radius=2)
            ui.text(ui.fit(u.name, "s", 300), (54, y + 4), "s", tcol)
            for txt, x in ((f"{u.size}", 388), (f"{u.quality}+", 430), (f"{u.defense}+", 464),
                           (f"{u.pts}", 502), (f"{u.rr_cost}", 558)):
                ui.text(txt, (x, y + 4), "s", tcol)
            ap = ap_available(u)
            ui.text(f"{u.xp}" + (" *" if ap else ""), (598, y + 4), "s", C_GOOD if ap and not dim else tcol)
            if u.unpaid:
                ui.text("!", (636, y + 4), "s", C_BAD)
                if ui.over(row):
                    ui.tip = tr("army.unpaid")
            if ui.clicked(row):
                self.sel_unit = idx
        if n:
            hi = min(n, self.scroll + self.VISIBLE)
            ui.text(tr("army.scroll", a=self.scroll + 1, b=hi, n=n), (32, 658), "xs", C_DIM)
        if ui.button((130, 652, 40, 28), "^", enabled=self.scroll > 0):
            self.scroll -= 1
        if ui.button((176, 652, 40, 28), "v", enabled=self.scroll < max(0, n - self.VISIBLE)):
            self.scroll += 1
        rem_err = camp.force_remove_error(fac, fi)
        if ui.button((226, 652, 170, 28), tr("army.del_army"), enabled=rem_err is None, font="xs",
                     tip=tr(rem_err) if rem_err else ""):
            camp.remove_force(fac, fi)
            self.army_fi, self.sel_unit, self.scroll = 0, None, 0
            return
        if ui.button((460, 652, 190, 28), tr("army.back"), font="xs"):
            self.army_fid = None
            ui.focus = None
            return

        # =============== panel derecho: importación, catálogo y editor ===============
        R = pygame.Rect(670, 58, 590, 636)
        ui.panel(R, tr("army.import_title"))
        self.import_src = ui.text_field("army_src", (682, 84, 410, 28), self.import_src, 300)
        if ui.button((1100, 84, 150, 28), tr("army.import"), color=(150, 100, 30),
                     enabled=not self.fetcher.busy, tip=tr("army.import_tip")):
            self.start_import(fac, fi)
        ui.text(ui.fit(tr("army.src_hint"), "xs", 566), (682, 116), "xs", C_DIM)
        if ui.button((682, 134, 190, 28), tr("army.clip"), tip=tr("army.clip_tip"), font="xs"):
            txt = get_clipboard_text()
            if txt.strip():
                self.import_text(fac, fi, txt, "clipboard")
            else:
                self.set_msg(tr("army.err_clip"), True)
        if ui.button((878, 134, 180, 28), tr("army.mode_replace") if self.import_replace
                     else tr("army.mode_append"), tip=tr("army.mode_tip"), font="xs"):
            self.import_replace = not self.import_replace
        if ui.button((1064, 134, 186, 28), tr("army.catalog"), color=(60, 110, 150), font="xs",
                     tip=tr("army.catalog_tip")):
            if fac.opr_faction:
                self.app.open_catalog(fac.fid, fi)
            else:
                self.set_msg(tr("army.catalog_need"), True)
        if self.msg:
            for i, line in enumerate(ui.wrap(self.msg, "xs", 566)[:2]):
                ui.text(line, (682, 168 + i * 15), "xs", C_BAD if self.msg_err else C_GOOD)
        else:
            ui.text(tr("army.reserve_note"), (682, 168), "xs", C_DIM)

        for i, (key, lab) in enumerate((("unit", "army.tab_unit"), ("xp", "army.tab_xp"))):
            if ui.button((682 + i * 158, 196, 152, 22), tr(lab), active=(self.ed_tab == key), font="xs"):
                self.ed_tab = key
        pygame.draw.line(ui.screen, C_LINE, (682, 220), (1250, 220))
        if self.sel_unit is None:
            ui.text(tr("army.select_hint"), (682, 234), "s", C_DIM)
            if ui.button((682, 590, 140, 28), tr("army.new")):
                self.new_unit(fc)
            ui.text(tr("army.resources", cr=fac.cr, rr=fac.rr), (960, 596), "s", C_GOOD)
            return

        u = units[self.sel_unit]
        uid = f"{fac.fid}_{fi}_{self.sel_unit}"
        if self.ed_tab == "unit":
            self.draw_unit_tab(ui, fac, fi, u, uid, camp)
        else:
            self.draw_xp_tab(ui, u)
        self.draw_unit_buttons(ui, fac, fi, fc, u)

    # ---- editor: datos de la unidad ---------------------------------------
    def draw_unit_tab(self, ui, fac, fi, u, uid, camp):
        lx, fx = 682, 770
        ui.text(tr("army.lbl_name"), (lx, 238), "xs", C_DIM)
        u.name = ui.text_field(f"u_name_{uid}", (fx, 232, 480, 28), u.name, 60)
        ui.text(tr("army.lbl_models"), (lx, 272), "xs", C_DIM)
        u.size = ui.stepper((fx, 266, 96, 28), u.size, 1, 99)
        ui.text(tr("army.lbl_q"), (882, 272), "xs", C_DIM)
        u.quality = ui.stepper((940, 266, 96, 28), u.quality, 2, 6, 1, "{}+")
        ui.text(tr("army.lbl_d"), (1050, 272), "xs", C_DIM)
        u.defense = ui.stepper((1110, 266, 96, 28), u.defense, 2, 6, 1, "{}+")
        ui.text(tr("army.lbl_pts"), (lx, 306), "xs", C_DIM)
        old_pts = u.pts
        u.pts = ui.stepper((fx, 300, 116, 28), u.pts, 0, 9999, 5)
        if u.pts != old_pts and u.rr_cost == default_rr(old_pts, camp.pts_per_rr):
            u.rr_cost = default_rr(u.pts, camp.pts_per_rr)
        ui.text(tr("army.lbl_rr"), (912, 306), "xs", C_DIM)
        u.rr_cost = ui.stepper((980, 300, 116, 28), u.rr_cost, 0, 999)
        ui.text(tr("army.lbl_status"), (lx, 340), "xs", C_DIM)
        for i, st in enumerate(STATUSES):
            err = camp.status_error(fac, fi, u, st)
            tip = ""
            if st == "active" and u.status == "reserve":
                tip = tr("tip.recruit", c=u.rr_cost)
            elif st == "reserve" and u.status == "active":
                tip = tr("tip.refund", n=u.rr_cost // 2)
            elif st == "destroyed":
                tip = tr("tip.destroy")
            if err:
                tip = tr(err)
            if ui.button((fx + i * 80, 334, 76, 28), tr("st." + st), enabled=err is None, font="xs",
                         active=(u.status == st), tip=tip,
                         color=darker(self.STATUS_COL[st], 0.7) if u.status == st else None):
                self.change_unit_status(fac, fi, u, st)
        if u.status == "active":
            ui.text(tr("army.upkeep", n=camp.unit_upkeep(u)), (1096, 341), "xs", C_DIM)
        ui.text(tr("army.lbl_rules"), (lx, 374), "xs", C_DIM)
        u.rules = ui.text_field(f"u_rules_{uid}", (fx, 368, 480, 28), u.rules, 400)
        ui.text(tr("army.lbl_weapons"), (lx, 408), "xs", C_DIM)
        u.weapons = ui.text_field(f"u_weap_{uid}", (fx, 402, 480, 28), u.weapons, 600)
        ui.text(tr("army.lbl_upgrades"), (lx, 442), "xs", C_DIM)
        u.upgrades = ui.text_field(f"u_upg_{uid}", (fx, 436, 480, 28), u.upgrades, 600)
        ui.text(tr("army.lbl_notes"), (lx, 476), "xs", C_DIM)
        u.notes = ui.text_field(f"u_notes_{uid}", (fx, 470, 480, 28), u.notes, 300)
        yy = 506
        for label, txt, mx in (("army.prev_rules", u.rules, 1), ("army.prev_weapons", u.weapons, 2),
                               ("army.prev_upgrades", u.upgrades, 1), ("army.prev_adv", adv_summary(u), 1)):
            if txt:
                for line in ui.wrap(tr(label, t=txt), "xs", 566)[:mx]:
                    ui.text(line, (682, yy), "xs", C_DIM)
                    yy += 15

    # ---- editor: XP, rangos y avances ---------------------------------------
    def draw_xp_tab(self, ui, u):
        x = 682
        rk = rank_of(u.xp)
        ui.text(ui.fit(u.name, "m", 560), (x, 234), "m", C_TEXT)
        ui.text(tr("army.rank", r=rank_name(rk), x=u.xp), (x, 258), "m", C_ACCENT)
        ui.text(tr("army.lbl_xp"), (x, 296), "xs", C_DIM)
        u.xp = ui.stepper((770, 290, 130, 28), u.xp, 0, 99)
        nxt = next((t for t in RANK_XP if t > u.xp), None)
        ui.text(tr("army.next_rank", x=nxt) if nxt is not None else tr("army.max_rank"), (916, 297), "xs", C_DIM)
        ap = ap_available(u)
        ui.text(tr("army.ap", n=ap), (x, 330), "m", C_GOOD if ap else C_DIM)
        ui.text(tr("army.adv_title"), (x, 360), "xs", C_ACCENT)
        for i, k in enumerate(ADVANCES):
            r = (x + (i % 2) * 288, 378 + (i // 2) * 34, 280, 30)
            if ui.button(r, tr("adv." + k), enabled=can_advance(u, k), font="xs", tip=tr("adv." + k + ".d")):
                if apply_advance(u, k):
                    self.set_msg(tr("army.adv_applied", u=u.name, a=tr("adv." + k)))
        ui.text(tr("army.adv_done", t=adv_summary(u) or tr("army.adv_none")), (x, 520), "xs", C_TEXT)
        if ui.button((x, 542, 240, 26), tr("army.adv_undo"), enabled=bool(u.advances), font="xs"):
            undo_advance(u)

    # ---- botones comunes del editor ------------------------------------------
    def draw_unit_buttons(self, ui, fac, fi, fc, u):
        camp = self.app.campaign
        if ui.button((682, 590, 140, 28), tr("army.new")):
            self.new_unit(fc)
        if ui.button((828, 590, 110, 28), tr("army.dup")):
            fc.units.insert(self.sel_unit + 1, ArmyUnit(**asdict(u)))
            self.sel_unit += 1
        if ui.button((944, 590, 100, 28), tr("army.del"), color=(120, 50, 50)):
            fc.units.pop(self.sel_unit)
            self.sel_unit = min(self.sel_unit, len(fc.units) - 1) if fc.units else None
            return
        if ui.button((1050, 590, 90, 28), tr("army.up"), enabled=self.sel_unit > 0, font="xs"):
            i = self.sel_unit
            fc.units[i - 1], fc.units[i] = fc.units[i], fc.units[i - 1]
            self.sel_unit -= 1
        if ui.button((1146, 590, 104, 28), tr("army.down"), enabled=self.sel_unit < len(fc.units) - 1,
                     font="xs"):
            i = self.sel_unit
            fc.units[i + 1], fc.units[i] = fc.units[i], fc.units[i + 1]
            self.sel_unit += 1
        err = camp.recruit_error(fac, fi, u) if u.status == "reserve" else "err.status_no"
        can_rec = u.status == "reserve" and err is None
        tip = tr("army.recruit_tip") + (("  —  " + tr(err)) if (err and u.status == "reserve") else "")
        if ui.button((682, 628, 270, 30), tr("army.recruit", c=u.rr_cost), enabled=can_rec,
                     color=(60, 120, 76) if can_rec else None, tip=tip):
            self.change_unit_status(fac, fi, u, "active")
        ui.text(tr("army.resources", cr=fac.cr, rr=fac.rr), (970, 635), "s", C_GOOD)

    def new_unit(self, fc: Force):
        u = ArmyUnit(name=tr("army.new_unit"), status="reserve")
        pos = (self.sel_unit + 1) if self.sel_unit is not None else len(fc.units)
        fc.units.insert(pos, u)
        self.sel_unit = pos
        self.scroll = clamp(self.scroll, max(0, pos - self.VISIBLE + 1), pos)


# =============================================================================
#  APLICACIÓN
# =============================================================================
class App:
    TAB_KEYS = [("tab.campaign", "campaign"), ("tab.battle", "battle"), ("tab.factions", "factions")]

    def __init__(self):
        pygame.init()
        self.settings = self.load_settings()
        set_lang(self.settings.get("lang", "es"))
        pygame.display.set_caption("OPR Campaign & Battle Manager")
        info = pygame.display.Info()
        scale = min(1.0, max(0.4, (info.current_w - 80) / WIN_W), max(0.4, (info.current_h - 140) / WIN_H))
        self.windowed_size = (int(WIN_W * scale), int(WIN_H * scale))
        self.fullscreen = False
        self.window = None
        self.view = (0, 0, 1.0)
        self.set_display(bool(self.settings.get("fullscreen", False)))
        self.canvas = pygame.Surface((WIN_W, WIN_H)).convert()
        self.screen = self.canvas
        self.clock = pygame.time.Clock()
        self.fonts = make_fonts()
        self.ui = UI(self.screen, self.fonts)
        self.ui.mouse_fn = lambda: self.to_logical(pygame.mouse.get_pos())
        self.opr = OprDB()
        self.views = {"campaign": CampaignView(self), "battle": BattleView(self),
                      "factions": FactionView(self)}
        self.tab = "campaign"
        self.status = ""
        self.status_err = False
        self.status_until = 0
        self.running = True
        # campañas abiertas a la vez
        self.slots: List[dict] = []
        self.active = 0
        self.campaign: Campaign = None
        self.battle: BattleState = None
        # diálogos
        self.dialog: Optional[str] = None          # files | result | books | catalog
        self.dlg_files: List[Tuple[str, float]] = []
        self.dlg_type = "GEN"
        self.dlg_base = ""
        self.dlg_msg = ""
        self.dlg_scroll_open = 0
        self.dlg_scroll_saved = 0
        self.res: Optional[dict] = None
        self.pick: Optional[dict] = None
        self.cat: Optional[dict] = None
        self.restore_campaigns()

    # ---- ajustes ----------------------------------------------------------
    @staticmethod
    def load_settings() -> dict:
        try:
            with open(SETTINGS_FILE, "r", encoding="utf-8") as fh:
                return json.load(fh)
        except Exception:
            return {}

    def save_settings(self):
        files = [s["file"] for s in self.slots if s.get("file")]
        act = self.slots[self.active]["file"] if self.slots and self.active < len(self.slots) else None
        self.settings.update(lang=LANG, fullscreen=self.fullscreen, open_campaigns=files,
                             active_campaign=act)
        try:
            with open(SETTINGS_FILE, "w", encoding="utf-8") as fh:
                json.dump(self.settings, fh, ensure_ascii=False, indent=2)
        except OSError:
            pass

    # ---- pantalla ---------------------------------------------------------
    # Todo se dibuja en una superficie lógica fija de 1280x720 (self.canvas) que se
    # escala a la ventana o a la pantalla completa manteniendo la proporción
    # (bandas negras). El ratón se convierte a coordenadas lógicas.
    def set_display(self, fullscreen: bool):
        try:
            if fullscreen:
                if self.window is not None and not self.fullscreen:
                    self.windowed_size = self.window.get_size()
                self.window = pygame.display.set_mode((0, 0), pygame.FULLSCREEN)
            else:
                self.window = pygame.display.set_mode(self.windowed_size, pygame.RESIZABLE)
            self.fullscreen = fullscreen
        except pygame.error:
            self.window = pygame.display.set_mode(self.windowed_size)
            self.fullscreen = False
        pygame.key.set_repeat(350, 35)

    def toggle_fullscreen(self):
        self.set_display(not self.fullscreen)
        self.save_settings()

    def present(self):
        win = pygame.display.get_surface()
        ww, wh = win.get_size()
        if (ww, wh) == (WIN_W, WIN_H):
            win.blit(self.canvas, (0, 0))
            self.view = (0, 0, 1.0)
        else:
            s = min(ww / WIN_W, wh / WIN_H)
            nw, nh = max(1, int(WIN_W * s)), max(1, int(WIN_H * s))
            ox, oy = (ww - nw) // 2, (wh - nh) // 2
            win.fill((0, 0, 0))
            win.blit(pygame.transform.smoothscale(self.canvas, (nw, nh)), (ox, oy))
            self.view = (ox, oy, s)
        pygame.display.flip()

    def to_logical(self, pos) -> Tuple[int, int]:
        ox, oy, s = self.view
        return int((pos[0] - ox) / s), int((pos[1] - oy) / s)

    def convert_events(self, events) -> list:
        out = []
        for e in events:
            if e.type in (pygame.MOUSEBUTTONDOWN, pygame.MOUSEBUTTONUP, pygame.MOUSEMOTION):
                d = dict(getattr(e, "dict", None) or e.__dict__)
                d["pos"] = self.to_logical(e.pos)
                e = pygame.event.Event(e.type, d)
            out.append(e)
        return out

    def change_lang(self, lang: str):
        if lang != LANG:
            set_lang(lang)
            self.ui._cache.clear()
            self.save_settings()

    # ---- estado / mensajes -----------------------------------------------
    def set_status(self, msg, error=False, ms=4500):
        self.status, self.status_err = msg, error
        self.status_until = pygame.time.get_ticks() + ms

    def switch_tab(self, key):
        if key != self.tab:
            self.tab = key
            self.ui.focus = None
            self.views["battle"].drag = None

    # ---- varias campañas abiertas ----------------------------------------------
    def add_slot(self, camp: Campaign, battle: BattleState, fname: Optional[str]) -> int:
        self.slots.append({"campaign": camp, "battle": battle, "file": fname})
        return len(self.slots) - 1

    def activate(self, idx: int):
        idx = clamp(idx, 0, len(self.slots) - 1)
        self.active = idx
        self.campaign = self.slots[idx]["campaign"]
        self.battle = self.slots[idx]["battle"]
        cv = self.views["campaign"]
        cv.sel = cv.sel_force = cv.route_mode = None
        self.views["battle"].drag = None
        fv = self.views["factions"]
        fv.army_fid, fv.sel_unit, fv.army_fi = None, None, 0
        self.ui.focus = None
        self.save_settings()

    def restore_campaigns(self):
        names = self.settings.get("open_campaigns")
        if names is None and self.settings.get("last_campaign"):
            names = [self.settings["last_campaign"]]
        for fn in names or []:
            path = os.path.join(CAMPAIGN_DIR, fn)
            if os.path.isfile(path):
                self.load_file(path, silent=True, activate=False)
        if not self.slots:
            self.add_slot(Campaign("GEN"), BattleState(), None)
        act = self.settings.get("active_campaign")
        idx = next((i for i, s in enumerate(self.slots) if act and s["file"] == act), 0)
        self.activate(idx)

    def save_slot(self, idx: int) -> bool:
        slot = self.slots[idx]
        fname = safe_filename(slot["campaign"].name) + ".json"
        try:
            os.makedirs(CAMPAIGN_DIR, exist_ok=True)
            with open(os.path.join(CAMPAIGN_DIR, fname), "w", encoding="utf-8") as fh:
                json.dump(dict(version=5, lang=LANG, campaign=slot["campaign"].to_dict(),
                               battle=slot["battle"].to_dict()), fh, ensure_ascii=False, indent=2)
            slot["file"] = fname
            return True
        except Exception as ex:  # noqa
            self.set_status(tr("status.save_err", err=ex), error=True)
            return False

    def save_campaign(self):
        if self.save_slot(self.active):
            self.save_settings()
            self.set_status(tr("status.saved", path=os.path.join("campaign", self.slots[self.active]["file"])))
            self.refresh_files()

    def save_all(self):
        n = sum(1 for i in range(len(self.slots)) if self.save_slot(i))
        self.save_settings()
        self.set_status(tr("status.saved_all", n=n))
        self.refresh_files()

    def load_file(self, path: str, silent: bool = False, activate: bool = True) -> bool:
        fname = os.path.basename(path)
        for i, s in enumerate(self.slots):
            if s["file"] == fname:
                if activate:
                    self.activate(i)
                return True
        try:
            with open(path, "r", encoding="utf-8") as fh:
                data = json.load(fh)
            camp = Campaign.from_dict(data["campaign"])
            battle = BattleState.from_dict(data["battle"]) if "battle" in data else BattleState()
            idx = self.add_slot(camp, battle, fname)
            if activate:
                self.activate(idx)
            if not silent:
                self.set_status(tr("status.loaded", name=camp.name))
            return True
        except Exception as ex:  # noqa
            self.set_status(tr("status.load_err", err=ex), error=True)
            return False

    def close_slot(self, idx: int):
        name = self.slots[idx]["campaign"].name
        self.save_slot(idx)
        was_active = self.active
        self.slots.pop(idx)
        if not self.slots:
            self.add_slot(Campaign("GEN"), BattleState(), None)
            new_active = 0
        elif idx < was_active:
            new_active = was_active - 1
        else:
            new_active = min(was_active, len(self.slots) - 1)
        self.activate(new_active)
        self.refresh_files()
        self.set_status(tr("status.closed", n=name))

    def refresh_files(self):
        files = []
        try:
            for fn in os.listdir(CAMPAIGN_DIR):
                if fn.lower().endswith(".json"):
                    files.append((fn, os.path.getmtime(os.path.join(CAMPAIGN_DIR, fn))))
        except OSError:
            pass
        self.dlg_files = sorted(files, key=lambda x: -x[1])

    def open_files(self):
        self.dialog = "files"
        self.ui.focus = None
        self.dlg_type, self.dlg_base = split_campaign_name(self.campaign.name)
        self.dlg_msg = ""
        self.dlg_scroll_open = self.dlg_scroll_saved = 0
        self.refresh_files()

    # ---- integración campaña -> batalla -----------------------------------
    def start_battle_for(self, q: Quadrant):
        """Prepara el generador de batalla según el bioma, el sistema OPR y los bonos locales del territorio."""
        b = self.battle
        camp = self.campaign
        owner = camp.faction(q.owner)
        prof = SYSTEMS.get(owner.army_system if owner else "GEN", SYSTEMS["GEN"])
        if owner and owner.army_system != "GEN" and b.size_idx != prof["board"]:
            b.set_size(prof["board"])
        b.apply_biome(q.biome)
        total = sum(b.counts.values())
        if prof["terrain"] and 0 < total < prof["terrain"]:
            k = prof["terrain"] / total
            for key in b.counts:
                b.counts[key] = int(math.ceil(b.counts[key] * k))
        b.seed = random.randint(1, 99999)
        b.context = (f"{quad_label(q.col, q.row)} {q.name} ({biome_name(q.biome)})"
                     + (tr("bt.ctx_defends", f=owner.name) if owner else tr("bt.ctx_free")))
        lb = camp.local_bonus(q)           # Torre vigía / Fortaleza: solo en este territorio
        if owner and (lb["ini"] or lb["df"]):
            b.context += tr("bt.local_bonus", ini=lb["ini"], df=lb["df"], f=owner.name)
        b.generate(False)
        self.switch_tab("battle")
        self.set_status(tr("status.battle_ready"))

    # ---- resultado de batalla (diálogo modal) -------------------------------
    def open_result(self, q: Quadrant):
        camp = self.campaign
        clash = next((c for c in camp.clashes if (c.col, c.row) == (q.col, q.row)), None)
        facs = camp.factions
        if clash:
            att, dfn = clash.att_fid, clash.def_fid
        else:
            present = [g.fid for g, _i, _c in camp.forces_at(q.col, q.row)]
            att = present[0] if present else (facs[0].fid if facs else None)
            others = [f.fid for f in facs if f.fid != att]
            dfn = q.owner if (q.owner is not None and q.owner != att) else (others[0] if others else None)
        self.res = dict(col=q.col, row=q.row, att=att, dfn=dfn, winner="att", note="",
                        scroll=0, clash=clash, rows={"att": [], "def": []})
        self.res_rebuild()
        self.dialog = "result"
        self.ui.focus = None

    def res_rebuild(self):
        camp, r = self.campaign, self.res
        q = camp.quad(r["col"], r["row"])
        clash = r["clash"]
        for side, key in (("att", "att"), ("def", "dfn")):
            f = camp.faction(r[key])
            fi = None
            if clash and f is not None:
                if side == "att" and clash.att_fid == f.fid:
                    fi = clash.att_force
                elif side == "def" and clash.def_fid == f.fid:
                    fi = clash.def_force
            r["rows"][side] = [dict(unit=u, state="ok", xp=1, auto=True)
                               for u in (camp.participants(q, f, fi) if f else [])]
        r["scroll"] = 0

    def draw_result_dialog(self, ui: UI):
        camp, r = self.campaign, self.res
        if r is None:
            self.dialog = None
            return
        q = camp.quad(r["col"], r["row"])
        dim = pygame.Surface((WIN_W, WIN_H), pygame.SRCALPHA)
        dim.fill((0, 0, 0, 170))
        self.screen.blit(dim, (0, 0))
        box = pygame.Rect(110, 56, 1060, 612)
        ui.panel(box, tr("res.title", q=f"{quad_label(q.col, q.row)} · {q.name}"))
        pygame.draw.rect(self.screen, C_ACCENT, box, 2, border_radius=8)
        facs = camp.factions
        ids = [f.fid for f in facs]
        fa, fd = camp.faction(r["att"]), camp.faction(r["dfn"])

        if ui.button((box.x + 14, box.y + 34, 250, 28), tr("res.att", f=fa.name if fa else "—"),
                     color=fa.color if fa else None, tip=tr("res.cycle_tip")) and ids:
            r["att"] = ids[(ids.index(r["att"]) + 1) % len(ids)] if r["att"] in ids else ids[0]
            if r["dfn"] == r["att"]:
                r["dfn"] = None
            self.res_rebuild()
        if ui.button((box.x + 272, box.y + 34, 250, 28), tr("res.def", f=fd.name if fd else tr("camp.neutral")),
                     color=fd.color if fd else None, tip=tr("res.cycle_tip")):
            opts = [None] + [i for i in ids if i != r["att"]]
            cur = opts.index(r["dfn"]) if r["dfn"] in opts else 0
            r["dfn"] = opts[(cur + 1) % len(opts)]
            self.res_rebuild()
        for i, (w, lab) in enumerate((("att", "res.win_att"), ("draw", "res.win_draw"), ("def", "res.win_def"))):
            if ui.button((box.x + 560 + i * 162, box.y + 34, 156, 28), tr(lab), active=(r["winner"] == w), font="xs"):
                r["winner"] = w
        ui.text(tr("res.xp_hint"), (box.x + 14, box.y + 68), "xs", C_DIM)

        state_col = {"ok": None, "fallen": (170, 110, 40), "destroyed": (130, 50, 50)}
        state_lab = {"ok": "res.ok", "fallen": "res.fallen", "destroyed": "res.destroyed"}
        order = ["ok", "fallen", "destroyed"]
        vis = 14
        longest = max(len(r["rows"]["att"]), len(r["rows"]["def"]))
        if ui.over(box) and ui.wheel:
            r["scroll"] -= ui.wheel
        r["scroll"] = clamp(r["scroll"], 0, max(0, longest - vis))
        for side, x0, head in (("att", box.x + 14, "res.att_units"), ("def", box.x + 546, "res.def_units")):
            ui.text(tr(head), (x0, box.y + 90), "xs", C_ACCENT)
            ui.text(tr("army.lbl_status"), (x0 + 268, box.y + 90), "xs", C_DIM)
            ui.text(tr("army.lbl_xp"), (x0 + 372, box.y + 90), "xs", C_DIM)
            rows = r["rows"][side]
            if not rows:
                ui.text(tr("res.none_units"), (x0 + 8, box.y + 114), "s", (120, 126, 140))
            for i in range(r["scroll"], min(len(rows), r["scroll"] + vis)):
                row = rows[i]
                y = box.y + 108 + (i - r["scroll"]) * 30
                pygame.draw.rect(self.screen, C_PANEL2, pygame.Rect(x0, y, 500, 28), border_radius=4)
                ui.text(ui.fit(row["unit"].name, "s", 250), (x0 + 8, y + 14), "s", C_TEXT, "midleft")
                st = row["state"]
                if ui.button((x0 + 262, y + 2, 100, 24), tr(state_lab[st]), font="xs", color=state_col[st],
                             tip=tr("res.state_tip")):
                    row["state"] = order[(order.index(st) + 1) % len(order)]
                if row["auto"]:
                    row["xp"] = 0 if row["state"] != "ok" else 1 + (1 if r["winner"] == side else 0)
                v = ui.stepper((x0 + 372, y + 2, 120, 24), row["xp"], 0, 9)
                if v != row["xp"]:
                    row["xp"], row["auto"] = v, False
        if longest > vis:
            if ui.button((box.x + 14, box.bottom - 88, 40, 26), "^", enabled=r["scroll"] > 0):
                r["scroll"] -= 1
            if ui.button((box.x + 60, box.bottom - 88, 40, 26), "v", enabled=r["scroll"] < longest - vis):
                r["scroll"] += 1
        ui.text(tr("res.note"), (box.x + 14, box.bottom - 50), "xs", C_DIM)
        r["note"] = ui.text_field("res_note", (box.x + 70, box.bottom - 56, 560, 30), r["note"], 120)
        if ui.button((box.right - 290, box.bottom - 56, 134, 30), tr("res.save"), color=(60, 120, 76),
                     enabled=r["att"] is not None):
            clash = r["clash"] if (r["clash"] and (r["clash"].att_fid, r["clash"].def_fid) == (r["att"], r["dfn"])) else None
            att_rows = [(d["unit"], d["state"], d["xp"]) for d in r["rows"]["att"]]
            def_rows = [(d["unit"], d["state"], d["xp"]) for d in r["rows"]["def"]]
            msgs = camp.record_battle(q, r["att"], r["dfn"], r["winner"], att_rows, def_rows, r["note"], clash)
            self.set_status(tr("status.recorded", q=quad_label(q.col, q.row)) + ("  " + " ".join(msgs) if msgs else ""))
            self.dialog = None
            ui.focus = None
        if ui.button((box.right - 148, box.bottom - 56, 134, 30), tr("res.cancel")):
            self.dialog = None
            ui.focus = None

    # ---- facción OPR (selector de libro de ejército) ---------------------------
    def open_books(self, fid: int):
        fac = self.campaign.faction(fid)
        if fac is None:
            return
        self.pick = dict(fid=fid, filter="", scroll=0)
        self.dialog = "books"
        self.ui.focus = None
        code = fac.army_system
        if code in CATALOG_SYSTEMS and not self.opr.book_list(code):
            self.opr.request_list(code)

    def draw_books_dialog(self, ui: UI):
        camp, pk = self.campaign, self.pick
        fac = camp.faction(pk["fid"]) if pk else None
        if fac is None:
            self.dialog = None
            return
        code = fac.army_system
        dim = pygame.Surface((WIN_W, WIN_H), pygame.SRCALPHA)
        dim.fill((0, 0, 0, 170))
        self.screen.blit(dim, (0, 0))
        box = pygame.Rect(230, 50, 820, 620)
        ui.panel(box, tr("books.title", s=f"{code} · {tr('sys.' + code)}"))
        pygame.draw.rect(self.screen, C_ACCENT, box, 2, border_radius=8)
        if code not in CATALOG_SYSTEMS:
            ui.text(tr("books.none_sys"), (box.x + 16, box.y + 50), "s", C_WARN)
            if ui.button((box.right - 132, box.bottom - 44, 120, 30), tr("books.close")):
                self.dialog = None
            return
        if ui.button((box.x + 12, box.y + 34, 270, 28), tr("books.download"), enabled=not self.opr.busy,
                     color=(60, 110, 150), tip=tr("books.download_tip"), font="xs"):
            self.opr.request_list(code)
        if self.opr.msg:
            ui.text(ui.fit(self.opr.msg, "xs", 500), (box.x + 294, box.y + 42), "xs",
                    C_BAD if self.opr.err else C_GOOD)
        ui.text(tr("books.filter"), (box.x + 14, box.y + 76), "xs", C_DIM)
        pk["filter"] = ui.text_field("books_filter", (box.x + 76, box.y + 70, 320, 28), pk["filter"], 40)
        metas = self.opr.book_list(code)
        flt = pk["filter"].strip().lower()
        shown = [m for m in metas if flt in m["name"].lower()] if flt else metas
        vis = 14
        if ui.over(box) and ui.wheel:
            pk["scroll"] -= ui.wheel
        pk["scroll"] = clamp(pk["scroll"], 0, max(0, len(shown) - vis))
        if not shown:
            for k, line in enumerate(ui.wrap(tr("books.empty", s=code), "s", 780)[:3]):
                ui.text(line, (box.x + 16, box.y + 114 + k * 20), "s", C_DIM)
        cur = (fac.opr_faction or {}).get("uid")
        for i in range(pk["scroll"], min(len(shown), pk["scroll"] + vis)):
            m = shown[i]
            row = pygame.Rect(box.x + 12, box.y + 108 + (i - pk["scroll"]) * 30, 796, 28)
            pygame.draw.rect(self.screen, (74, 62, 36) if m["uid"] == cur else C_PANEL2, row, border_radius=4)
            ui.text(ui.fit(m["name"], "s", 560), (row.x + 10, row.centery), "s", C_TEXT, "midleft")
            ui.text(m["version"], (row.x + 600, row.centery), "xs", C_DIM, "midleft")
            if ui.button((row.right - 96, row.y + 2, 90, 24), tr("books.choose"), font="xs"):
                fac.opr_faction = dict(uid=m["uid"], name=m["name"], system=code, gs=m.get("gs"))
                self.set_status(tr("fac.opr_line", s=code, f=m["name"]))
                self.dialog = None
                ui.focus = None
                return
        yb = box.y + 108 + vis * 30 + 6
        if fac.opr_faction:
            ui.text(ui.fit(tr("books.current", n=fac.opr_faction["name"]), "s", 380), (box.x + 14, yb + 8), "s", C_ACCENT)
            if ui.button((box.x + 420, yb + 2, 150, 28), tr("books.clear"), font="xs"):
                fac.opr_faction = None
        if ui.button((box.right - 132, yb + 2, 120, 28), tr("books.close")):
            self.dialog = None
            ui.focus = None
        ui.text(ui.fit(tr("books.folder", p=self.opr.dir), "xs", 790), (box.x + 14, yb + 40), "xs", C_DIM)
        ui.text(ui.fit(tr("books.local_hint", s=code), "xs", 790), (box.x + 14, yb + 56), "xs", C_DIM)
        ui.text(ui.fit(tr("cat.note"), "xs", 790), (box.x + 14, yb + 72), "xs", C_DIM)

    # ---- catálogo OPR local ("Army Forge en local") ------------------------------
    def open_catalog(self, fid: int, fi: int):
        fac = self.campaign.faction(fid)
        if fac is None or not fac.opr_faction:
            return
        of = fac.opr_faction
        self.cat = dict(fid=fid, fi=fi, filter="", sel_unit=0, sel={}, rscroll=0, uscroll=0)
        self.dialog = "catalog"
        self.ui.focus = None
        if self.opr.get_book(of["uid"], of["system"]) is None:
            self.opr.request_book(of["uid"], of["system"], of.get("gs"))

    @staticmethod
    def rules_tip(book: dict, rules: List[str]) -> str:
        parts = []
        for rl in rules:
            name = re.sub(r"\s*\(.*\)$", "", rl).strip()
            d = book["rules"].get(name)
            if d:
                parts.append(f"{name}: {d}")
        return " | ".join(parts)[:700]

    def draw_catalog_dialog(self, ui: UI):
        camp, cat = self.campaign, self.cat
        fac = camp.faction(cat["fid"]) if cat else None
        if fac is None or not fac.opr_faction or cat["fi"] >= len(fac.forces):
            self.dialog = None
            return
        of = fac.opr_faction
        fc = fac.forces[cat["fi"]]
        dim = pygame.Surface((WIN_W, WIN_H), pygame.SRCALPHA)
        dim.fill((0, 0, 0, 175))
        self.screen.blit(dim, (0, 0))
        box = pygame.Rect(40, 40, 1200, 640)
        ui.panel(box, tr("cat.title", n=f"{of['name']} ({of['system']})"))
        pygame.draw.rect(self.screen, C_ACCENT, box, 2, border_radius=8)
        book = self.opr.get_book(of["uid"], of["system"])
        if ui.button((box.right - 132, box.bottom - 40, 120, 30), tr("books.close")):
            self.dialog = None
            ui.focus = None
            return
        if book is None:
            ui.text(tr("cat.no_book"), (box.x + 16, box.y + 50), "s", C_WARN)
            if self.opr.msg:
                ui.text(ui.fit(self.opr.msg, "s", 1100), (box.x + 16, box.y + 76), "s",
                        C_BAD if self.opr.err else C_GOOD)
            if ui.button((box.x + 16, box.y + 104, 200, 30), tr("cat.download"), enabled=not self.opr.busy,
                         color=(60, 110, 150)):
                self.opr.request_book(of["uid"], of["system"], of.get("gs"))
            return

        # ---- columna izquierda: unidades
        x0 = box.x + 14
        ui.text(tr("cat.search"), (x0, box.y + 36), "xs", C_DIM)
        cat["filter"] = ui.text_field("cat_filter", (x0 + 90, box.y + 30, 250, 28), cat["filter"], 40)
        flt = cat["filter"].strip().lower()
        idxs = [i for i, u in enumerate(book["units"]) if not flt or flt in u["name"].lower()]
        vis = 19
        left = pygame.Rect(x0, box.y + 66, 346, vis * 26 + 4)
        if ui.over(left) and ui.wheel:
            cat["uscroll"] -= ui.wheel * 2
        cat["uscroll"] = clamp(cat["uscroll"], 0, max(0, len(idxs) - vis))
        ui.text(tr("cat.units", n=len(idxs)), (x0, box.bottom - 32), "xs", C_DIM)
        for k in range(cat["uscroll"], min(len(idxs), cat["uscroll"] + vis)):
            ui_idx = idxs[k]
            u = book["units"][ui_idx]
            row = pygame.Rect(x0, box.y + 68 + (k - cat["uscroll"]) * 26, 346, 24)
            on = ui_idx == cat["sel_unit"]
            pygame.draw.rect(self.screen, (74, 62, 36) if on else (C_PANEL2 if ui.over(row) else (36, 40, 50)),
                             row, border_radius=4)
            ui.text(ui.fit(f"{u['name']} [{u['size']}]", "s", 250), (row.x + 8, row.centery), "s", C_TEXT, "midleft")
            ui.text(f"{u['cost']} pts", (row.right - 8, row.centery), "xs", C_DIM, "midright")
            if ui.clicked(row) and not on:
                cat["sel_unit"], cat["sel"], cat["rscroll"] = ui_idx, {}, 0

        # ---- columna derecha: ficha de la unidad y mejoras
        if not book["units"]:
            return
        unit = book["units"][clamp(cat["sel_unit"], 0, len(book["units"]) - 1)]
        x1 = box.x + 376
        total = catalog_cost(book, unit, cat["sel"])
        ui.text(ui.fit(unit["name"], "l", 600), (x1, box.y + 34), "l", C_TEXT)
        ui.text(tr("cat.total", c=total), (box.right - 16, box.y + 36), "m", C_ACCENT, "topright")
        ui.text(tr("cat.stats", q=unit["quality"], d=unit["defense"], s=unit["size"], c=unit["cost"]),
                (x1, box.y + 66), "s", C_GOOD)
        yy = box.y + 92
        rtxt = tr("cat.rules", t=", ".join(unit["rules"]) or "-")
        for line in ui.wrap(rtxt, "s", 800)[:3]:
            ui.text(line, (x1, yy), "s", C_TEXT)
            yy += 18
        if ui.over((x1, box.y + 92, 800, 54)):
            tip = self.rules_tip(book, unit["rules"])
            if tip:
                ui.tip = tip
        yy = max(yy, box.y + 146) + 4
        wtxt = tr("cat.weapons", t=", ".join(unit["weapons"]) or "-")
        for line in ui.wrap(wtxt, "s", 800)[:4]:
            ui.text(line, (x1, yy), "s", C_DIM)
            yy += 18
        yy += 8
        ui.text(tr("cat.upgrades"), (x1, yy), "xs", C_ACCENT)
        pygame.draw.line(self.screen, C_LINE, (x1, yy + 16), (box.right - 16, yy + 16))
        area_top = yy + 22
        secs = catalog_sections(book, unit)
        flat = []
        for key, sec in secs:
            suffix = tr("cat.replace") if sec["mode"] == "replace" else (tr("cat.one") if sec["select"] == 1 else tr("cat.any"))
            flat.append(("hdr", key, sec, None, f"{sec['label']} {suffix}"))
            for oi, opt in enumerate(sec["options"]):
                flat.append(("opt", key, sec, oi, tr("cat.opt", l=opt["label"], c=opt["cost"])))
        rows_vis = max(1, (box.bottom - 66 - area_top) // 26)
        area = pygame.Rect(x1, area_top, 800, rows_vis * 26)
        if ui.over(area) and ui.wheel:
            cat["rscroll"] -= ui.wheel
        cat["rscroll"] = clamp(cat["rscroll"], 0, max(0, len(flat) - rows_vis))
        if not flat:
            ui.text(tr("cat.no_upgrades"), (x1, area_top + 4), "s", (120, 126, 140))
        for k in range(cat["rscroll"], min(len(flat), cat["rscroll"] + rows_vis)):
            kind, key, sec, oi, label = flat[k]
            ry = area_top + (k - cat["rscroll"]) * 26
            if kind == "hdr":
                ui.text(ui.fit(label, "s", 780), (x1 + 4, ry + 4), "s", C_ACCENT)
                continue
            chosen = cat["sel"].setdefault(key, set())
            tip = ""
            if sec["options"][oi]["weapons"] or sec["options"][oi]["rules"]:
                tip = "; ".join(sec["options"][oi]["weapons"] + sec["options"][oi]["rules"])
            if ui.button((x1 + 16, ry, 780, 24), label, active=(oi in chosen), align="left", font="xs", tip=tip):
                if sec["select"] == 1:
                    cat["sel"][key] = set() if oi in chosen else {oi}
                elif oi in chosen:
                    chosen.discard(oi)
                else:
                    chosen.add(oi)
        # pie
        if ui.button((x1, box.bottom - 46, 420, 34), tr("cat.add", n=cat["fi"] + 1), color=(60, 120, 76)):
            nu = catalog_to_unit(book, unit, cat["sel"], camp.pts_per_rr)
            fc.units.append(nu)
            fv = self.views["factions"]
            if fv.army_fid == fac.fid and fv.army_fi == cat["fi"]:
                fv.sel_unit = len(fc.units) - 1
            self.set_status(tr("cat.added", u=nu.name, a=fc.army_name or fc.name))
            cat["sel"] = {}
        ui.text(ui.fit(tr("cat.note"), "xs", 330), (box.x + 14, box.bottom - 18), "xs", C_DIM)

    # ---- dibujo -----------------------------------------------------------
    def draw_topbar(self, ui: UI):
        pygame.draw.rect(self.screen, (16, 18, 23), (0, 0, WIN_W, TOPBAR_H))
        pygame.draw.line(self.screen, C_LINE, (0, TOPBAR_H - 1), (WIN_W, TOPBAR_H - 1))
        ui.text("OPR Manager", (16, 12), "l", C_ACCENT)
        for i, (key, tab) in enumerate(self.TAB_KEYS):
            if ui.button((190 + i * 200, 8, 196, 32), tr(key), active=(self.tab == tab)):
                self.switch_tab(tab)
        n = len(self.slots)
        label = self.campaign.name + (f"  ({self.active + 1}/{n})" if n > 1 else "")
        if ui.button((800, 8, 200, 32), label, tip=tr("top.files_tip"), font="xs"):
            self.open_files()
        for i, lang in enumerate(LANGS):
            if ui.button((1008 + i * 40, 8, 36, 32), lang.upper(), active=(LANG == lang),
                         tip=tr("top.lang_tip"), font="xs"):
                self.change_lang(lang)
        if ui.button((1092, 8, 168, 32), tr("top.fs_off") if self.fullscreen else tr("top.fs_on"),
                     font="xs"):
            self.toggle_fullscreen()

    def draw_statusbar(self, ui: UI):
        r = pygame.Rect(0, WIN_H - STATUS_H, WIN_W, STATUS_H)
        pygame.draw.rect(self.screen, (16, 18, 23), r)
        if self.status and pygame.time.get_ticks() < self.status_until:
            ui.text(ui.fit(self.status, "s", WIN_W - 260), (12, r.centery), "s",
                    C_BAD if self.status_err else C_GOOD, "midleft")
        else:
            ui.text(tr("status.hint"), (12, r.centery), "xs", C_DIM, "midleft")
        ui.text("OPR Campaign & Battle Manager v5", (WIN_W - 12, r.centery), "xs", C_DIM, "midright")

    def draw_files_dialog(self, ui: UI):
        dim = pygame.Surface((WIN_W, WIN_H), pygame.SRCALPHA)
        dim.fill((0, 0, 0, 170))
        self.screen.blit(dim, (0, 0))
        box = pygame.Rect((WIN_W - 760) // 2, 46, 760, 628)
        ui.panel(box, tr("dlg.title"))
        pygame.draw.rect(self.screen, C_ACCENT, box, 2, border_radius=8)
        x = box.x + 12
        ui.text(ui.fit(tr("dlg.new_title"), "xs", 736), (x, box.y + 32), "xs", C_ACCENT)
        if ui.button((x, box.y + 52, 130, 30), tr("dlg.type", t=campaign_tag(self.dlg_type)),
                     tip=tr("dlg.type_tip"), font="xs"):
            self.dlg_type = CAMPAIGN_TYPES[(CAMPAIGN_TYPES.index(self.dlg_type) + 1) % len(CAMPAIGN_TYPES)]
        self.dlg_base = ui.text_field("dlg_base", (x + 138, box.y + 52, 300, 30), self.dlg_base, 40)
        composed = compose_campaign_name(self.dlg_type, self.dlg_base) if self.dlg_base.strip() else ""
        base_ok = bool(self.dlg_base.strip())
        if ui.button((x + 446, box.y + 52, 90, 30), tr("dlg.create"), color=(60, 120, 76), enabled=base_ok):
            if any(s["campaign"].name == composed for s in self.slots):
                self.dlg_msg = tr("dlg.name_exists")
            else:
                camp = Campaign(self.dlg_type, self.dlg_base)
                self.activate(self.add_slot(camp, BattleState(), None))
                self.set_status(tr("status.created", n=camp.name))
                self.dialog = None
                ui.focus = None
                return
        if ui.button((x + 544, box.y + 52, 192, 30), tr("dlg.rename"), enabled=base_ok, font="xs"):
            if any(s["campaign"].name == composed and i != self.active for i, s in enumerate(self.slots)):
                self.dlg_msg = tr("dlg.name_exists")
            else:
                slot = self.slots[self.active]
                old = slot["file"]
                self.campaign.rename(self.dlg_type, self.dlg_base)
                new = safe_filename(self.campaign.name) + ".json"
                if old and old != new and os.path.isfile(os.path.join(CAMPAIGN_DIR, old)) \
                        and not os.path.exists(os.path.join(CAMPAIGN_DIR, new)):
                    try:
                        os.replace(os.path.join(CAMPAIGN_DIR, old), os.path.join(CAMPAIGN_DIR, new))
                        slot["file"] = new
                    except OSError:
                        pass
                self.save_slot(self.active)
                self.save_settings()
                self.refresh_files()
                self.set_status(tr("status.renamed", n=self.campaign.name))
                self.dlg_msg = ""
        ui.text(("-> " + composed) if composed else tr("dlg.name_empty"), (x, box.y + 88), "xs",
                C_GOOD if composed else C_WARN)
        if self.dlg_msg:
            ui.text(self.dlg_msg, (x + 400, box.y + 88), "xs", C_BAD)

        # --- campañas abiertas
        n = len(self.slots)
        ui.text(tr("dlg.open_title", n=n), (x, box.y + 112), "xs", C_ACCENT)
        vis_o = 5
        area_o = pygame.Rect(x, box.y + 128, 736, vis_o * 34)
        if ui.over(area_o) and ui.wheel:
            self.dlg_scroll_open -= ui.wheel
        self.dlg_scroll_open = clamp(self.dlg_scroll_open, 0, max(0, n - vis_o))
        close_idx = switch_idx = None
        for i in range(self.dlg_scroll_open, min(n, self.dlg_scroll_open + vis_o)):
            s = self.slots[i]
            row = pygame.Rect(x, box.y + 128 + (i - self.dlg_scroll_open) * 34, 736, 32)
            on = i == self.active
            pygame.draw.rect(self.screen, (74, 62, 36) if on else C_PANEL2, row, border_radius=5)
            ui.text(ui.fit(s["campaign"].name, "s", 400), (row.x + 10, row.centery), "s",
                    C_ACCENT if on else C_TEXT, "midleft")
            ui.text(("T" + str(s["campaign"].turn)) + ("  *" if not s["file"] else ""), (row.x + 420, row.centery),
                    "xs", C_DIM, "midleft")
            if on:
                ui.text(tr("dlg.active"), (row.x + 500, row.centery), "xs", C_GOOD, "midleft")
            if ui.button((row.right - 206, row.y + 3, 96, 26), tr("dlg.activate"), enabled=not on, font="xs"):
                switch_idx = i
            if ui.button((row.right - 104, row.y + 3, 96, 26), tr("dlg.close_camp"), font="xs",
                         tip=tr("dlg.close_camp_tip")):
                close_idx = i
        # --- guardadas
        yb = box.y + 128 + vis_o * 34 + 10
        ui.text(tr("dlg.saved_title"), (x, yb), "xs", C_ACCENT)
        vis_s = 6
        area_s = pygame.Rect(x, yb + 16, 736, vis_s * 34)
        if ui.over(area_s) and ui.wheel:
            self.dlg_scroll_saved -= ui.wheel
        self.dlg_scroll_saved = clamp(self.dlg_scroll_saved, 0, max(0, len(self.dlg_files) - vis_s))
        if not self.dlg_files:
            ui.text(tr("dlg.empty"), (x + 8, yb + 24), "s", C_DIM)
        open_path = None
        for i in range(self.dlg_scroll_saved, min(len(self.dlg_files), self.dlg_scroll_saved + vis_s)):
            fn, mt = self.dlg_files[i]
            row = pygame.Rect(x, yb + 16 + (i - self.dlg_scroll_saved) * 34, 736, 32)
            pygame.draw.rect(self.screen, C_PANEL2, row, border_radius=5)
            ui.text(ui.fit(fn, "s", 440), (row.x + 10, row.centery), "s", C_TEXT, "midleft")
            ui.text(time.strftime("%Y-%m-%d %H:%M", time.localtime(mt)), (row.x + 470, row.centery), "xs", C_DIM,
                    "midleft")
            if ui.button((row.right - 104, row.y + 3, 96, 26), tr("dlg.open"), font="xs"):
                open_path = os.path.join(CAMPAIGN_DIR, fn)
        yf = box.bottom - 70
        ui.text(ui.fit(tr("dlg.folder", path=CAMPAIGN_DIR), "xs", 736), (x, yf), "xs", C_DIM)
        if ui.button((x, yf + 18, 170, 30), tr("dlg.save_active"), color=(60, 120, 76), font="xs"):
            self.save_campaign()
        if ui.button((x + 178, yf + 18, 170, 30), tr("dlg.save_all"), font="xs"):
            self.save_all()
        if ui.button((box.right - 132, yf + 18, 120, 30), tr("dlg.close")):
            self.dialog = None
            ui.focus = None
        if switch_idx is not None:
            self.activate(switch_idx)
            self.dialog = None
        elif close_idx is not None:
            self.close_slot(close_idx)
        elif open_path and self.load_file(open_path):
            self.dialog = None

    # ---- bucle principal --------------------------------------------------
    def run(self):
        ui = self.ui
        while self.running:
            events = self.convert_events(pygame.event.get())
            for e in events:
                if e.type == pygame.QUIT:
                    self.running = False
                    continue
                if e.type == pygame.VIDEORESIZE and getattr(pygame, "version", None) \
                        and pygame.version.vernum[0] < 2 and not self.fullscreen:
                    self.windowed_size = (max(320, e.w), max(180, e.h))
                    self.window = pygame.display.set_mode(self.windowed_size, pygame.RESIZABLE)
                    continue
                if e.type == pygame.KEYDOWN:
                    ctrl = e.mod & (pygame.KMOD_CTRL | pygame.KMOD_META)
                    alt = e.mod & pygame.KMOD_ALT
                    if e.key == pygame.K_F11 or (alt and e.key in (pygame.K_RETURN, pygame.K_KP_ENTER)):
                        self.toggle_fullscreen()
                        continue
                    if ui.focus is None:
                        if self.dialog and e.key == pygame.K_ESCAPE:
                            self.dialog = None
                            continue
                        if self.fullscreen and e.key == pygame.K_ESCAPE:
                            self.toggle_fullscreen()
                            continue
                        if ctrl and e.key == pygame.K_s:
                            self.save_campaign()
                            continue
                        if ctrl and e.key == pygame.K_l:
                            self.open_files()
                            continue
                        if not ctrl and not self.dialog and e.key in (pygame.K_1, pygame.K_2, pygame.K_3):
                            self.switch_tab(("campaign", "battle", "factions")[e.key - pygame.K_1])
                if self.dialog:
                    continue
                if e.type in (pygame.MOUSEBUTTONDOWN, pygame.MOUSEBUTTONUP,
                              pygame.MOUSEMOTION, pygame.KEYDOWN):
                    if e.type == pygame.MOUSEBUTTONDOWN and e.pos[1] < TOPBAR_H:
                        continue
                    self.views[self.tab].handle_event(e, ui)

            ui.begin(events)
            self.screen.fill(C_BG)
            ui.input_enabled = self.dialog is None
            self.views[self.tab].draw(ui)
            self.draw_topbar(ui)
            self.draw_statusbar(ui)
            ui.input_enabled = True
            if self.dialog == "files":
                self.draw_files_dialog(ui)
            elif self.dialog == "result":
                self.draw_result_dialog(ui)
            elif self.dialog == "books":
                self.draw_books_dialog(ui)
            elif self.dialog == "catalog":
                self.draw_catalog_dialog(ui)
            ui.draw_tooltip()
            self.present()
            self.clock.tick(FPS)
        self.save_settings()
        pygame.quit()


if __name__ == "__main__":
    App().run()
    sys.exit(0)
