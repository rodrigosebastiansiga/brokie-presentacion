# BROKIE V04.0G.3 - GEOMETRIA PURA + ILEGAL RECUPERABLE
from flask import Flask, render_template, request, jsonify, Response
import chess
import chess.engine
import time
import threading
import random
import inspect
import os
import fcntl
import uuid
from collections import deque

try:
    import bitacora
except Exception:
    bitacora = None


def _bit(cat, msg, **d):
    if bitacora:
        getattr(bitacora, cat)(msg, **d)


def _diag_vision(evento, **extra):
    """Diagnostico detallado de vision en la bitacora existente.

    Consultar desde cualquier navegador:
        /log?cat=vision&n=200
    """
    try:
        datos = {
            'evento': evento,
            'color_brazo': globals().get('color_brazo'),
        }
        if 'tablero' in globals():
            datos['turno'] = 'blancas' if tablero.turn == chess.WHITE else 'negras'
            datos['fen'] = tablero.fen()
        if vision is not None:
            datos['vision_estado'] = getattr(vision, 'estado_ciclo', None)
            datos['vision_detalle'] = getattr(vision, 'estado_detalle', None)
            datos['vision_pausada'] = getattr(vision, '_pausada', None)
            datos['vision_motivo_pausa'] = getattr(vision, '_motivo_pausa', None)
        datos.update(extra)
        _bit('vision', 'DIAG ' + evento, **datos)
    except Exception:
        pass


try:
    import vision
except Exception as _ev:
    vision = None
    print(f"Vision no disponible: {_ev}")
# Bloqueo maestro de emergencia. Normalmente queda apagado para que cada
# partida pueda elegir CON BRAZO o SIN BRAZO desde el touch. Puede forzarse
# con BROKIE_FORZAR_SIN_BRAZO=1 sin modificar el código.
MODO_PRUEBA_SIN_BRAZO = os.environ.get(
    'BROKIE_FORZAR_SIN_BRAZO', '0').strip().lower() in ('1', 'true', 'si', 'yes')
vision_con_brazo = False
# Mientras exista, el FEN YA contiene la jugada de BROKIE pero la madera espera
# que el usuario la reproduzca. La vision queda pausada hasta confirmar LISTO.
jugada_brokie_manual = None
vision_activa = False         # si estaba mirando al apagar, vuelve a mirar sola
espera_home_s = 5.0           # segundos que se espera tras llegar a home ANTES
                              # de fijar la referencia. La camara va en la
                              # muñeca y el brazo sigue vibrando al frenar: una
                              # foto tomada antes queda desde otra posicion y
                              # todas las casillas se leen corridas.
estabilizando_hasta = 0.0     # marca de tiempo hasta cuando esta asentandose
jugada_pendiente = None       # jugada del motor que el brazo no pudo ejecutar.
                              # Sin esto la partida quedaba trabada: mi jugada
                              # aplicada, la de BROKIE no, y el turno de BROKIE
                              # para siempre.
_desfase_previo = None        # desacuerdo anterior, para confirmar
desfase_tablero = None        # ultima verificacion que no cuadro: el tablero
                              # de madera no coincide con el de la partida
falla_vision = None           # ultima deteccion que no se pudo interpretar:
aviso_ilegal = None          # solo aviso visual; NO bloquea la vision
ilegal_pendiente = None       # hecho físico ilegal ya identificado; espera PRE
fin_manual = None             # rendición/tablas acordadas fuera de python-chess

                              # el jugador tiene que resolverla desde la
                              # pantalla, si no el tablero se desincroniza

# --- ANCLA DE ESTADO DE LA VISION ---
# Un cambio de imagen NO equivale a una jugada: una mano que pasa por encima
# puede disparar la deteccion. La jugada candidata debe poder demostrarse
# contra el estado fisico esperado y permanecer estable.
_ancla_vision_fisica = None
_ultima_candidata_vision = None
# BROKIE 4.0: firma ya notificada para ILEGAL/DUDOSO.
_firma_notificada_40 = None
_ultima_candidata_ts = 0.0
VISION_CONFIRMACION_S = 1.50
VISION_CONFIRMACION_MAX = 2.5
# Margen UART preliminar de HOME. Si no alcanza, decide el canónico completo
# de cuatro ArUco; esta cifra queda como diagnóstico articular secundario.
VISION_TOL_HOME = 12

# Monitor ambiental GY-302/BH1750 en el bus I2C software 3 (SDA GPIO5,
# SCL GPIO6). Sólo marca cambios globales; no interpreta piezas ni manos.
_gy302_estado = {'pendiente': False, 'lux': None, 'referencia': None,
                 'cambio_ts': None, 'error': None, 'estable': False,
                 'lectura_ts': None, 'suspendida': True,
                 'home_confirmado': False,
                 'motivo_suspension': 'esperando_confirmacion_home'}
_gy302_lock = threading.Lock()
# Exclusión del acceso físico al bus I2C. El lock de estado anterior evita
# publicar una muestra obsoleta; éste garantiza además que ninguna transacción
# del GY-302 se solape con el comienzo de una orden del brazo.
_gy302_io_lock = threading.Lock()
_luz_home = False
_luz_movimientos = 0
_luz_generacion = 0
_mediciones_bloqueadas_hasta = 0.0
# vision.en_pose() puede consultarse varias veces durante una sola deduccion.
# Reutiliza brevemente la ultima comprobacion fisica para no repetir cuatro
# consultas UART consecutivas. La generacion impide reutilizarla despues de
# cualquier orden de movimiento, aunque esa orden ya haya terminado.
HOME_CACHE_TTL_S = 0.50
_home_cache_valor = False
_home_cache_ts = 0.0
_home_cache_generacion = -1
_home_lecturas_uart = 0
_home_canonico_generacion = -1

# Modo de mantenimiento para redefinir HOME mirando la imagen cruda. Sólo la
# petición HTTP marcada puede abrir la cámara fuera de HOME; vigilancia y
# GY-302 siguen usando la compuerta normal. La concesión vence sola.
_ajuste_home_lock = threading.Lock()
_ajuste_home_hasta = 0.0
_captura_mantenimiento_ctx = threading.local()

# Prueba técnica de repetición. Mientras está activa, la cámara (incluida una
# pestaña vieja de /vision/encuadre) y el GY-302 quedan fuera del hardware aun
# durante las pausas entre dos tramos. El movimiento conserva sus lecturas
# UART normales y la prueba agrega VIN sólo cuando el brazo ya está quieto;
# nunca intercala sondeos dentro de una curva.
_prueba_tirones_lock = threading.Lock()
_prueba_tirones_stop = threading.Event()
_prueba_tirones_activa = False
_prueba_tirones_estado = {
    'activa': False,
    'estado': 'inactiva',
    'bloque': None,
    'ciclo': 0,
    'ciclos_por_bloque': 0,
    'repeticiones': 0,
    'jugada': 0,
    'jugadas_total': 70,
    'uci': None,
    'origen_plan': None,
    'fase': None,
    'detalle': 'Lista para iniciar',
    'error': None,
    'marcas': [],
    'voltajes': [],
    'voltaje_min_mv': {},
    'seq_inicio': None,
    'seq_actual': 0,
}


def _ajuste_home_activo():
    """La concesion de mantenimiento nunca sobrevive a una vigilancia.

    Una pestaña vieja de ``/vision/encuadre`` puede renovarla durante los
    segundos iniciales de un reinicio, antes de que el hilo restaure la
    vigilancia de partida. En cuanto la vigilancia está activa, la concesión
    deja de tener sentido y, si se conservara, bloquearía la primera respuesta
    física de BROKIE aunque el brazo estuviera correctamente en HOME.
    """
    global _ajuste_home_hasta
    with _ajuste_home_lock:
        if getattr(globals().get('vision'), 'vigilando', False):
            _ajuste_home_hasta = 0.0
            return False
        return time.monotonic() < _ajuste_home_hasta


def _renovar_ajuste_home(duracion_s=60.0):
    global _ajuste_home_hasta
    with _ajuste_home_lock:
        _ajuste_home_hasta = time.monotonic() + max(1.0, float(duracion_s))


def _cerrar_ajuste_home():
    global _ajuste_home_hasta
    with _ajuste_home_lock:
        _ajuste_home_hasta = 0.0


def _luz_confirmar_home(pos):
    """Usa posiciones ya leídas: no agrega consultas al UART."""
    global _luz_home, _home_cache_valor, _home_cache_ts
    global _home_cache_generacion
    with _gy302_lock:
        ahora = time.monotonic()
        completa = bool(pos and all(pos.get(s) is not None for s in (1, 2, 3, 4)))
        canonico_vigente = (_home_canonico_generacion == _luz_generacion)
        _luz_home = bool(not _luz_movimientos and (canonico_vigente or
                          (completa and all(
            pos.get(s) is not None and servo_home.get(s) is not None
            and abs(pos[s] - servo_home[s]) <= VISION_TOL_HOME
            for s in (1, 2, 3, 4)))))
        estabilizando = bool(_luz_home and ahora < _mediciones_bloqueadas_hasta)
        _gy302_estado['home_confirmado'] = _luz_home
        _gy302_estado['suspendida'] = not _luz_home or estabilizando
        if _luz_home and not estabilizando:
            _gy302_estado['motivo_suspension'] = None
        else:
            _gy302_estado['motivo_suspension'] = (
                'brazo_en_movimiento' if _luz_movimientos else
                'estabilizando_home' if estabilizando else
                'brazo_fuera_de_home' if completa else
                'esperando_confirmacion_home')
            _gy302_estado.update(estable=False, pendiente=False,
                                 cambio_ts=None, lectura_ts=None)
        _home_cache_valor = _luz_home
        _home_cache_ts = ahora
        _home_cache_generacion = _luz_generacion
    return _luz_home


def _luz_confirmar_home_canonico():
    """HOME óptico permanece válido sólo hasta la próxima orden física."""
    global _home_canonico_generacion
    _home_canonico_generacion = _luz_generacion
    return _luz_confirmar_home(None)


def _mediciones_permitidas():
    """Estado sin UART: compuerta común para cámara y sensor ambiental."""
    with _gy302_lock:
        ahora = time.monotonic()
        if _prueba_tirones_activa:
            return False, 'prueba_tirones', 0.0
        if _luz_movimientos:
            return False, 'brazo_en_movimiento', 0.0
        # Excepción exclusiva del hilo que atiende la imagen cruda durante el
        # ajuste. No habilita el sensor ni el ciclo normal de vigilancia.
        if (getattr(_captura_mantenimiento_ctx, 'ajuste_home', False)
                and _ajuste_home_activo()):
            return True, 'ajuste_home', 0.0
        if not _luz_home:
            return False, 'brazo_fuera_de_home', 0.0
        restante = max(0.0, _mediciones_bloqueadas_hasta - ahora)
        if restante > 0:
            return False, 'estabilizando_home', restante
        return True, None, 0.0


def _bloquear_mediciones_estabilizacion(segundos):
    """Extiende la pausa óptica/I2C sin consultar posiciones de servos."""
    global _mediciones_bloqueadas_hasta
    with _gy302_lock:
        _mediciones_bloqueadas_hasta = max(
            _mediciones_bloqueadas_hasta,
            time.monotonic() + max(0.0, float(segundos)))
        _gy302_estado.update(suspendida=True, estable=False,
                             motivo_suspension='estabilizando_home',
                             pendiente=False, cambio_ts=None, lectura_ts=None)


def _luz_token():
    with _gy302_lock:
        habilitada = (not _prueba_tirones_activa and
                      not _luz_movimientos and _luz_home and
                      time.monotonic() >= _mediciones_bloqueadas_hasta)
        return _luz_generacion if habilitada else None


_propietario_movimiento = threading.RLock()
_fallo_retorno_home = None
_cancelacion_movimiento = 0
_error_trayectoria = threading.local()


def _excluir_movimientos(formato='dict'):
    """Un único escritor; las órdenes concurrentes se rechazan, no se encolan."""
    from functools import wraps
    def decorar(fn):
        @wraps(fn)
        def ejecutar(*args, **kwargs):
            if not _propietario_movimiento.acquire(blocking=False):
                error = 'Brazo ocupado: orden no ejecutada ni encolada'
                if formato == 'http':
                    return jsonify({'ok': False, 'error': error}), 409
                if formato == 'tupla':
                    return False, error
                return {'ok': False, 'error': error}
            try:
                return fn(*args, **kwargs)
            finally:
                _propietario_movimiento.release()
        return ejecutar
    return decorar


def _suspender_luz_durante_movimiento(home=False):
    from functools import wraps
    def decorar(fn):
        @wraps(fn)
        def ejecutar(*args, **kwargs):
            global _luz_home, _luz_movimientos, _luz_generacion
            global _mediciones_bloqueadas_hasta
            global _fallo_retorno_home

            # Barrera real antes de la primera orden: espera una captura o
            # lectura I2C que ya estuviera en curso y luego invalida ambas
            # fuentes mientras todavía conserva sus candados físicos. Una
            # solicitud nueva verá el estado bloqueado y no tocará hardware.
            camara_lock = (getattr(vision, '_lock_camara', None)
                           if vision is not None else None)
            if camara_lock is not None:
                camara_lock.acquire()
            _gy302_io_lock.acquire()
            try:
                with _gy302_lock:
                    _luz_movimientos += 1
                    _luz_generacion += 1
                    _luz_home = False
                    _gy302_estado.update(suspendida=True, estable=False,
                                         home_confirmado=False,
                                         motivo_suspension='brazo_en_movimiento',
                                         pendiente=False, cambio_ts=None,
                                         lectura_ts=None)
            finally:
                _gy302_io_lock.release()
                if camara_lock is not None:
                    camara_lock.release()
            resultado = None
            try:
                resultado = fn(*args, **kwargs)
                return resultado
            finally:
                with _gy302_lock:
                    _luz_movimientos -= 1
                canonico_ok = False
                if (home and isinstance(resultado, dict)
                        and not resultado.get('ok')
                        and resultado.get('validar_home_canonico')
                        and vision is not None):
                    try:
                        canonico_ok, detalle = vision.validar_home_canonico()
                    except Exception as exc:
                        detalle = {'ok': False, 'error': str(exc)[:180]}
                    resultado['home_canonico'] = detalle
                    if canonico_ok:
                        resultado.update(
                            ok=True, home_confirmado_por='cuatro_aruco',
                            aviso_uart_home=resultado.get('error'))
                        resultado.pop('error', None)
                        _bit('brazo', 'HOME confirmado por canónico: 4 ArUco',
                             uart=resultado.get('posicion_real_final'),
                             detalle=detalle)
                with _gy302_lock:
                    if (home and isinstance(resultado, dict)
                            and resultado.get('ok')):
                        _mediciones_bloqueadas_hasta = max(
                            _mediciones_bloqueadas_hasta,
                            time.monotonic() + espera_home_s)
                if home and isinstance(resultado, dict) and resultado.get('ok'):
                    _fallo_retorno_home = None
                    if canonico_ok:
                        _luz_confirmar_home_canonico()
                    else:
                        _luz_confirmar_home(resultado.get('posicion_real_final'))
        return ejecutar
    return decorar


def _reiniciar_referencia_gy302():
    """Alinea la referencia ambiental con la iluminación de este momento."""
    with _gy302_lock:
        lux = _gy302_estado.get('lux')
        if lux is not None and _gy302_estado.get('error') is None:
            _gy302_estado['referencia'] = lux
        _gy302_estado['pendiente'] = False
        _gy302_estado['cambio_ts'] = None

def _descartar_gy302_transitorio(estado, pausa_ambiental=False):
    """Bajo _gy302_lock: cancela un aviso aún no mostrado si volvió a su base.

    Exige la ventana estable existente (~2 s) y retorno dentro de 3%/2 lux.
    Una pausa ya abierta queda a cargo de los botones del jugador.
    """
    if (pausa_ambiental or not estado.get('pendiente')
            or estado.get('error') or not estado.get('estable')):
        return False
    lux, base = estado.get('lux'), estado.get('referencia')
    if lux is None or base is None:
        return False
    if abs(lux - base) > max(abs(base) * 0.03, 2.0):
        return False
    estado.update(pendiente=False, cambio_ts=None)
    return True


def _vigilar_gy302():
    while True:
        token = _luz_token()
        if token is None:
            time.sleep(0.2)
            continue
        fd = None
        try:
            with _gy302_io_lock:
                if _luz_token() != token:
                    continue
                fd = os.open('/dev/i2c-3', os.O_RDWR)
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                fcntl.ioctl(fd, 0x0703, 0x23)
                for cmd in (0x01, 0x07, 0x42, 0x65, 0x10):
                    os.write(fd, bytes([cmd]))
            muestras = deque(maxlen=11)
            candidato = None
            while True:
                time.sleep(0.2)
                with _gy302_io_lock:
                    if _luz_token() != token:
                        break
                    respuesta = os.read(fd, 2)
                if len(respuesta) != 2:
                    raise OSError('Respuesta I2C incompleta')
                raw = int.from_bytes(respuesta, 'big')
                if raw == 65535:
                    raise OSError('GY-302 saturado')
                lux = raw / 1.2
                now = time.monotonic()
                muestras.append((now, lux))
                estable = (len(muestras) == 11 and
                    muestras[-1][0]-muestras[0][0] >= 2.0 and
                    max(v for _,v in muestras)-min(v for _,v in muestras)
                    <= max(lux*0.03, 2.0))
                with _gy302_lock:
                    # Si comenzó un movimiento durante el I/O, descartar esa
                    # lectura sin demorar el brazo ni publicar un aviso.
                    if not _luz_home or _luz_movimientos or token != _luz_generacion:
                        break
                    _gy302_estado.update(lux=round(lux,2), error=None,
                                         estable=estable, lectura_ts=now,
                                         suspendida=False, home_confirmado=True,
                                         motivo_suspension=None)
                    if _descartar_gy302_transitorio(
                            _gy302_estado,
                            getattr(vision, '_motivo_pausa', None) == 'confirmando_cambio_luz'):
                        _bit('vision', 'GY302: transitorio descartado; volvió a referencia',
                             lux=_gy302_estado['lux'], referencia=_gy302_estado['referencia'])
                        candidato = None
                    base = _gy302_estado['referencia']
                    if base is None and estable:
                        _gy302_estado['referencia'] = lux
                    elif base is not None and not _gy302_estado['pendiente']:
                        if abs(lux-base) >= max(base*0.15,3.0):
                            if candidato is None:
                                candidato = now
                            if now-candidato >= 0.6:
                                _gy302_estado.update(pendiente=True,
                                                     cambio_ts=time.time(),
                                                     lux_disparo=round(lux, 2),
                                                     referencia_disparo=base)
                                _bit('vision', 'GY302: cambio sostenido detectado',
                                     lux=round(lux, 2), referencia=base,
                                     diferencia_pct=round(100 * (lux-base) / max(abs(base), 0.01), 2))
                                candidato = None
                        else:
                            candidato = None
                    else:
                        candidato = None
        except Exception as e:
            with _gy302_lock:
                if _luz_home and not _luz_movimientos and token == _luz_generacion:
                    _gy302_estado.update(error=str(e)[:160], estable=False)
        finally:
            if fd is not None:
                with _gy302_io_lock:
                    os.close(fd)
        time.sleep(2)



def _brazo_en_home():
    """Pose aproximada para visión, con cache breve y lectura UART atómica.

    Una ráfaga de ``en_pose()`` reutiliza la comprobación durante 500 ms. La
    generación cambia al comenzar cualquier movimiento, por lo que un valor
    anterior nunca sobrevive a una orden del brazo. El candado cubre el lote
    de cuatro lecturas: el movimiento empieza antes del lote o después, no
    entre consultas de articulaciones distintas.
    """
    global _home_lecturas_uart
    if not SERVOS_OK:
        return True
    with _gy302_lock:
        if _luz_movimientos:
            return False
        ahora = time.monotonic()
        if (_home_cache_generacion == _luz_generacion and
                ahora - _home_cache_ts < HOME_CACHE_TTL_S):
            return _home_cache_valor
        try:
            _home_lecturas_uart += 1
            pos = pos_real()
        except Exception:
            pos = None

    # Se actualizan sensor y cache bajo su propio candado. Si una orden logró
    # comenzar justo al terminar el lote, _luz_confirmar_home devuelve False
    # y guarda el resultado en la generación nueva, nunca un HOME obsoleto.
    if pos is None:
        _luz_confirmar_home(None)
        return False
    return bool(_luz_confirmar_home(pos))


def _confirmar_home_arranque_luz(intentos=3, registrar=True):
    """Confirma HOME al arrancar sin habilitar torque ni mandar posiciones."""
    pos = None
    ultimo_error = None
    for intento in range(max(1, int(intentos))):
        try:
            if SERVOS_OK:
                pos, sospechosos = leer_posiciones_robusta()
                if sospechosos:
                    raise RuntimeError(f'lecturas dudosas: {sospechosos}')
            else:
                from lx16a import LX16A
                angulos = LX16A.read_physical_angles(
                    '/dev/ttyUSB0', ids=(1, 2, 3, 4))
                pos = {sid: g2u(angulos[sid]) for sid in (1, 2, 3, 4)}
            if _luz_confirmar_home(pos):
                if registrar:
                    _bit('sistema', 'GY302: HOME confirmado al arrancar sin movimiento',
                         posiciones=pos, intento=intento + 1)
                return True
            # La referencia útil de HOME es óptica: si el canónico reconstruye
            # los cuatro ArUco con pose PnP válida, unos ticks de diferencia
            # articular no deben dejar cámara y sensor suspendidos.
            if vision is not None:
                try:
                    canonico_ok, detalle = vision.validar_home_canonico()
                except Exception as exc:
                    canonico_ok, detalle = False, {'error': str(exc)[:180]}
                if canonico_ok:
                    _luz_confirmar_home_canonico()
                    if registrar:
                        _bit('sistema', 'HOME de arranque confirmado por 4 ArUco',
                             posiciones=pos, detalle=detalle)
                    return True
            if registrar:
                _bit('sistema', 'GY302: sensor suspendido; brazo fuera de HOME',
                     posiciones=pos, home=servo_home,
                     canonico=detalle if vision is not None else None)
            return False
        except Exception as e:
            ultimo_error = str(e)[:160]
            time.sleep(0.15)
    _luz_confirmar_home(None)
    if registrar:
        _bit('sistema', 'GY302: esperando confirmacion de HOME al arrancar',
             error=ultimo_error)
    return False


def _recuperar_home_arranque_luz(duracion_s=120.0, intervalo_s=2.0):
    """Recupera la carrera de enumeración USB/I2C de un arranque en frío.

    Sólo lee las posiciones. Nunca habilita torque ni ordena movimientos. Si
    obtiene una lectura válida fuera de HOME se detiene: en ese caso el sensor
    debe seguir suspendido hasta que una llegada real a HOME lo reactive.
    """
    inicio = time.monotonic()
    intentos = 0
    while time.monotonic() - inicio < max(0.0, float(duracion_s)):
        with _gy302_lock:
            if _luz_home:
                return True
            moviendo = bool(_luz_movimientos)
            motivo = _gy302_estado.get('motivo_suspension')

        if motivo == 'brazo_fuera_de_home':
            return False

        if not moviendo:
            intentos += 1
            if _confirmar_home_arranque_luz(intentos=1, registrar=False):
                _bit('sistema', 'GY302: HOME recuperado tras enumeracion de arranque',
                     intentos=intentos,
                     demora_s=round(time.monotonic() - inicio, 2))
                return True
            with _gy302_lock:
                if _gy302_estado.get('motivo_suspension') == 'brazo_fuera_de_home':
                    return False
        time.sleep(max(0.1, float(intervalo_s)))

    _bit('sistema', 'GY302: no se pudo confirmar HOME durante el arranque',
         intentos=intentos,
         duracion_s=round(time.monotonic() - inicio, 2))
    return False


if vision is not None:
    vision.verificar_pose = _brazo_en_home
    vision.captura_permitida = _mediciones_permitidas
import json
import os
import math

# Pin del electroiman. Estaba en el GPIO 17, pero la pantalla tactil de 3.5"
# usa ese pin para la interrupcion del touch, asi que paso al 26.
PIN_ELECTROIMAN = int(os.environ.get('BROKIE_PIN_IMAN', '26'))

# Tope inferior de la MUÑECA. Estaba en 180 desde el lente anterior; con el
# gran angular de 105 grados la camara quedo en otra pose y el brazo necesita
# bajar mas. Medido en el brazo real: 154. Por debajo la muñeca toca el codo.
MUNECA_MIN = int(os.environ.get('BROKIE_MUNECA_MIN', '170'))

try:
    from gpiozero import OutputDevice
    # GPIO 26: se movio del 17 porque la pantalla tactil de 3.5" usa el 17
    # para la interrupcion del touch. Configurable por si vuelve a cambiar.
    electroiman = OutputDevice(PIN_ELECTROIMAN, active_high=True, initial_value=False)
    GPIO_OK = True
except Exception as e:
    print(f"GPIO no disponible: {e}")
    GPIO_OK = False

# ── Conversion unidades (0-1000) <-> grados (0-240) ──────
def u2g(u): return u * 240.0 / 1000.0
def g2u(g): return int(round(g * 1000.0 / 240.0))

# V03.8.26 — TRAZA DE ORDENES DE SERVO EN IDLE.
# No cambia la mecanica. Solo arma una "trampa" despues de fijar la referencia.
# Si CUALQUIER codigo Python manda un move() mientras BROKIE ya estaba mirando,
# se registra la PRIMERA orden con servo/objetivo/tiempo/caller y se desarma para
# no inundar la bitacora con los micropasos del suavizador.
_servo_idle_trace = False
_servo_idle_trace_generacion = 0

# Caja negra de las ordenes que realmente llegan al ultimo wrapper antes del
# UART. Vive solo en RAM: no consulta servos y no escribe un evento por cada
# micropaso en la bitacora. Asi permite distinguir una consigna inesperada de
# un movimiento fisico que ocurrio sin que Python lo ordenara, sin perturbar el
# tiempo del lazo de movimiento.
_servo_ordenes_lock = threading.Lock()
_servo_ordenes = deque(maxlen=12000)
_servo_orden_secuencia = 0
_servo_ultima_orden_ns = {}
_servo_auditoria_contexto = threading.local()

# Prueba descartada: repetir una consigna reinicia la interpolación interna de
# los LX-225 y produjo vibración continua. Debe permanecer desactivada; el
# flujo normal vuelve a emitir exactamente una trama por punto de trayectoria.
SERVO_REDUNDANCIA_UART = False
SERVO_REDUNDANCIA_PAUSA_S = 0.003


def _registrar_orden_servo(sid, solicitado_u, aplicado_u, tiempo_ms,
                           origen, ok=True, error=None,
                           copia_uart='primaria'):
    """Registra una escritura ya intentada, sin ninguna lectura del UART."""
    global _servo_orden_secuencia
    try:
        ahora_ns = time.monotonic_ns()
        contexto = getattr(_servo_auditoria_contexto, 'traza_id', None)
        with _servo_ordenes_lock:
            anterior_ns = _servo_ultima_orden_ns.get(sid)
            _servo_orden_secuencia += 1
            registro = {
                'seq': _servo_orden_secuencia,
                'monotonic_ns': ahora_ns,
                'hora': time.strftime('%H:%M:%S'),
                'servo': int(sid),
                'solicitado_u': int(solicitado_u),
                'aplicado_u': int(aplicado_u),
                'tiempo_ms': int(tiempo_ms or 0),
                'desde_anterior_ms': (None if anterior_ns is None else
                                      round((ahora_ns-anterior_ns)/1_000_000, 3)),
                'origen': str(origen),
                'copia_uart': str(copia_uart),
                'traza_id': contexto,
                'hilo': threading.current_thread().name,
                'ok': bool(ok),
            }
            if error:
                registro['error'] = str(error)[:160]
            _servo_ordenes.append(registro)
            _servo_ultima_orden_ns[sid] = ahora_ns
    except Exception:
        # La auditoria nunca puede impedir ni alterar una orden del brazo.
        pass

_torque_liberado_idle = False


@_suspender_luz_durante_movimiento()
def _retomar_torque_para_jugada():
    """Reactiva torque sólo después de tomar una REFERENCIA REAL de los servos.

    V03.8.28:
      1) con torque todavía OFF, lee varias veces la posición física real;
      2) toma la mediana por servo como referencia de arranque;
      3) habilita torque;
      4) manda exactamente esa referencia real como primer objetivo;
      5) sincroniza los suavizadores con esa posición;
      6) recién después el movimiento normal toma el control.

    No modifica servo_home ni calibración. Esta referencia sirve únicamente
    para evitar que al reactivar torque el brazo salte hacia una posición vieja.
    """
    global _torque_liberado_idle
    if not SERVOS_OK:
        return False
    if not _torque_liberado_idle:
        return True

    # 1) REFERENCIA REAL con torque todavía liberado.
    muestras = {sid: [] for sid in servos}
    for _ in range(5):
        for sid, s in servos.items():
            try:
                a = s.get_physical_angle()
                if a is not None:
                    muestras[sid].append(float(a))
            except Exception:
                pass
        time.sleep(0.04)

    ref_ang = {}
    ref_u = {}
    for sid, vals in muestras.items():
        if not vals:
            _bit('brazo', 'fallo referencia real antes de torque',
                 servo=sid, motivo='sin lecturas')
            return False
        vals = sorted(vals)
        a = vals[len(vals)//2]
        ref_ang[sid] = a
        try:
            ref_u[sid] = g2u(a)
        except Exception:
            ref_u[sid] = None

    _bit('brazo', 'REFERENCIA REAL tomada antes de torque',
         posiciones=ref_u,
         muestras={sid: len(v) for sid, v in muestras.items()})

    # 2) Reactivar exactamente sobre la referencia real recién medida.
    ok = True
    lote_retorno = []
    for sid, s in servos.items():
        try:
            s.enable_torque()
            lote_retorno.append((sid, ref_ang[sid], 350))
        except Exception as e:
            ok = False
            _bit('brazo', 'fallo retomando torque para jugada',
                 servo=sid, error=str(e)[:120])

    if not ok:
        return False
    try:
        _enviar_lote_servo(lote_retorno)
    except Exception as e:
        _bit('brazo', 'fallo enviando referencia redundante al retomar torque',
             error=str(e)[:120])
        return False

    # 3) Sincronizar suavizadores para que ningún perfil pendiente arranque
    #    desde una posición antigua.
    for sid, sm in smooth.items():
        try:
            sm.x = 1.0
        except Exception:
            pass

    _torque_liberado_idle = False
    _bit('brazo', 'TORQUE RETOMADO DESDE REFERENCIA REAL',
         posiciones=ref_u)
    time.sleep(0.40)
    return True


class _ServoTrazado:
    def __init__(self, sid, real):
        self._sid = sid
        self._real = real
        self._tope_muneca_activo = False

    def __getattr__(self, name):
        return getattr(self._real, name)

    def move(self, angle, time=0, *args, **kwargs):
        global _servo_idle_trace
        copia_uart = kwargs.pop('_copia_uart', 'primaria')
        solicitado_u = g2u(float(angle))
        # Última barrera común a TODAS las órdenes, incluidas las directas y
        # las del panel manual. La geometría normal ya limita sus perfiles,
        # pero este clamp impide que una ruta vieja o un llamado aislado mande
        # físicamente la muñeca por debajo del mínimo seguro.
        if self._sid == 4:
            objetivo_u = g2u(float(angle))
            if objetivo_u < MUNECA_MIN:
                if not self._tope_muneca_activo:
                    _bit('brazo', 'TOPE MUNECA aplicado',
                         solicitado=objetivo_u, aplicado=MUNECA_MIN)
                angle = u2g(MUNECA_MIN)
                self._tope_muneca_activo = True
            else:
                self._tope_muneca_activo = False
        aplicado_u = g2u(float(angle))
        try:
            marco = inspect.currentframe()
            llamador = marco.f_back if marco is not None else None
            origen_orden = ('desconocido' if llamador is None else
                            f'{llamador.f_code.co_name}:{llamador.f_lineno}')
        except Exception:
            origen_orden = 'desconocido'
        finally:
            try:
                del marco
                del llamador
            except Exception:
                pass
        if _servo_idle_trace:
            _servo_idle_trace = False
            try:
                st = inspect.stack()
                origen = ' <- '.join(
                    f"{f.function}:{f.lineno}" for f in st[1:5])
            except Exception:
                origen = 'desconocido'
            try:
                objetivo_u = g2u(float(angle))
            except Exception:
                objetivo_u = None
            _bit('brazo', 'ORDEN SERVO DURANTE IDLE',
                 servo=self._sid, objetivo_u=objetivo_u,
                 tiempo_ms=time, origen=origen,
                 generacion=_servo_idle_trace_generacion)
        try:
            resultado = self._real.move(angle, time, *args, **kwargs)
        except Exception as e:
            registrar = globals().get('_registrar_orden_servo')
            if registrar is not None:
                registrar(self._sid, solicitado_u, aplicado_u, time,
                          origen_orden, ok=False, error=e,
                          copia_uart=copia_uart)
            raise
        registrar = globals().get('_registrar_orden_servo')
        if registrar is not None:
            registrar(self._sid, solicitado_u, aplicado_u, time,
                      origen_orden, ok=True, copia_uart=copia_uart)
        return resultado


def _armar_traza_servo_idle():
    global _servo_idle_trace, _servo_idle_trace_generacion
    _servo_idle_trace_generacion += 1
    _servo_idle_trace = True
    _bit('brazo', 'SERVO IDLE TRACE armado',
         generacion=_servo_idle_trace_generacion)


def _desarmar_traza_servo_idle(motivo=''):
    global _servo_idle_trace
    if _servo_idle_trace:
        _servo_idle_trace = False
        _bit('brazo', 'SERVO IDLE TRACE desarmado', motivo=motivo)


SERVOS_OK = False
servos = {}
smooth = {}

def _inicializar_servos():
    global servos, smooth, SERVOS_OK
    if SERVOS_OK:
        return True, 'ya inicializados'
    try:
        from lx16a import LX16A
        from servo_smooth import SmoothServo

        LX16A.initialize('/dev/ttyUSB0')

        servos = {}
        for sid in [1, 2, 3, 4]:
            servos[sid] = LX16A(sid, disable_torque=True)

        _pos_arranque = {sid: s.get_physical_angle() for sid, s in servos.items()}

        for sid, s in servos.items():
            s.enable_torque()
            s.move(_pos_arranque[sid], 500)

        servos = {sid: _ServoTrazado(sid, s) for sid, s in servos.items()}
        smooth = {sid: SmoothServo(servos[sid]) for sid in servos}
        SERVOS_OK = True

        print("Servos OK (quintic):",
              {sid: g2u(a) for sid, a in _pos_arranque.items()})

    except Exception as e:
        print(f"Servos no disponibles: {e}")
        SERVOS_OK = False
        return False, str(e)

    return True, 'servos inicializados'

ARCHIVO_CALIBRACION = '/home/rodri/chess_robot/calibracion.json'

ALTURAS = ('peon', 'rey')

def _cargar_punto_2alturas(pos):
    """Normaliza un punto del JSON al formato de 2 alturas con claves de servo int."""
    out = {}
    for alt in ALTURAS:
        if alt in pos and isinstance(pos[alt], dict):
            out[alt] = _claves_servo(pos[alt])
    return out

def _escaque_valido(sq):
    """'e2' -> 'E2'. None si no es un escaque del tablero."""
    if not isinstance(sq, str):
        return None
    sq = sq.strip().upper()
    if len(sq) == 2 and sq[0] in 'ABCDEFGH' and sq[1] in '12345678':
        return sq
    return None


def _claves_servo(d):
    """{'1':x, 'null':y} -> {1:x}. Descarta lo que no sea una clave valida.

    Un solo dato malo en el archivo -por ejemplo una clave nula guardada por
    una peticion mal formada- hacia fallar la carga ENTERA de la calibracion
    y el sistema arrancaba sin puntos, sin tabla y sin ajustes.
    """
    out = {}
    for k, v in (d or {}).items():
        try:
            ki = int(k)
        except (TypeError, ValueError):
            continue
        if ki in (1, 2, 3, 4) and v is not None:
            out[ki] = v
    return out


def cargar_calibracion():
    global calibracion_puntos, tabla_escaques, servo_home
    global retraso_muneca_val, traslado_hombro, traslado_codo
    global factor_vel_traslado, vel_muneca_bajada
    global vel_muneca_bajada_cercana, vel_muneca_bajada_media
    global despegue_codo, margen_aterrizaje_lejana, bajada_codo
    global bajada_codo_escaque
    global compensacion_muneca_cercana
    global aterrizaje_directo, aterrizaje_ms, aterrizaje_vel, base_solo_arriba
    global paso_transito, paso_bajada, codo_max_encare, margen_max_encare, margen_max_cercana
    global verif_activa, verif_tolerancia, verif_ms, ruta_ms
    global punto_captura, captura_altura_mm, color_brazo, volver_a_home
    global iman_espera_s, iman_soltar_s, punto_espera, enroque_por_afuera
    global vision_activa, vision_con_brazo, espera_home_s
    global nivel_actual, reinicio_horas
    global puntos_derivados
    if os.path.exists(ARCHIVO_CALIBRACION):
        try:
            with open(ARCHIVO_CALIBRACION, 'r') as f:
                data = json.load(f)
                calibracion_puntos.update({
                    k: _cargar_punto_2alturas(pos)
                    for k, pos in data.get('puntos', {}).items()
                })
                tabla_escaques.update({
                    k: _cargar_punto_2alturas(pos)
                    for k, pos in data.get('tabla', {}).items()
                })
                if isinstance(data.get('captura'), dict):
                    punto_captura = _claves_servo(data['captura']) or None
                if isinstance(data.get('espera'), dict):
                    punto_espera = _claves_servo(data['espera']) or None
                if isinstance(data.get('rutas'), dict):
                    rutas_bajada.update({
                        k: [_claves_servo(paso) for paso in ruta_g]
                        for k, ruta_g in data['rutas'].items()})
                if 'home' in data:
                    servo_home.update(_claves_servo(data['home']))
                aj = data.get('ajustes', {})
                if 'retraso_muneca_val' in aj and aj['retraso_muneca_val'] is not None:
                    retraso_muneca_val = float(aj['retraso_muneca_val'])
                if 'traslado_hombro' in aj:
                    traslado_hombro = aj['traslado_hombro']
                if 'traslado_codo' in aj:
                    traslado_codo = aj['traslado_codo']
                if 'factor_vel_traslado' in aj and aj['factor_vel_traslado'] is not None:
                    factor_vel_traslado = float(aj['factor_vel_traslado'])
                if 'vel_muneca_bajada' in aj and aj['vel_muneca_bajada'] is not None:
                    vel_muneca_bajada = float(aj['vel_muneca_bajada'])
                if aj.get('vel_muneca_bajada_cercana') is not None:
                    vel_muneca_bajada_cercana = max(
                        0.5, min(4.0, float(aj['vel_muneca_bajada_cercana'])))
                if aj.get('vel_muneca_bajada_media') is not None:
                    vel_muneca_bajada_media = max(
                        0.5, min(4.0, float(aj['vel_muneca_bajada_media'])))
                if 'despegue_codo' in aj and aj['despegue_codo'] is not None:
                    despegue_codo = int(aj['despegue_codo'])
                if 'margen_aterrizaje_lejana' in aj and aj['margen_aterrizaje_lejana'] is not None:
                    margen_aterrizaje_lejana = int(aj['margen_aterrizaje_lejana'])
                if 'bajada_codo' in aj and aj['bajada_codo'] is not None:
                    bajada_codo = int(aj['bajada_codo'])
                if aj.get('compensacion_muneca_cercana') is not None:
                    compensacion_muneca_cercana = max(
                        0, min(80, int(aj['compensacion_muneca_cercana'])))
                if aj.get('aterrizaje_directo') is not None:
                    aterrizaje_directo = bool(aj['aterrizaje_directo'])
                if aj.get('aterrizaje_ms') is not None:
                    aterrizaje_ms = int(aj['aterrizaje_ms'])
                if aj.get('aterrizaje_vel') is not None:
                    aterrizaje_vel = float(aj['aterrizaje_vel'])
                if aj.get('base_solo_arriba') is not None:
                    base_solo_arriba = bool(aj['base_solo_arriba'])
                if aj.get('paso_transito') is not None:
                    paso_transito = float(aj['paso_transito'])
                if aj.get('paso_bajada') is not None:
                    paso_bajada = float(aj['paso_bajada'])
                if aj.get('codo_max_encare') is not None:
                    codo_max_encare = int(aj['codo_max_encare'])
                if aj.get('margen_max_encare') is not None:
                    margen_max_encare = int(aj['margen_max_encare'])
                if aj.get('margen_max_cercana') is not None:
                    margen_max_cercana = int(aj['margen_max_cercana'])
                # Campo histórico: desde V60 la verificación es únicamente
                # diagnóstica y nunca puede reactivar correcciones físicas.
                verif_activa = False
                if aj.get('verif_tolerancia') is not None:
                    verif_tolerancia = int(aj['verif_tolerancia'])
                if aj.get('verif_ms') is not None:
                    verif_ms = int(aj['verif_ms'])
                if aj.get('ruta_ms') is not None:
                    ruta_ms = int(aj['ruta_ms'])
                if aj.get('captura_altura_mm') is not None:
                    captura_altura_mm = int(aj['captura_altura_mm'])
                if aj.get('iman_espera_s') is not None:
                    iman_espera_s = float(aj['iman_espera_s'])
                if aj.get('iman_soltar_s') is not None:
                    iman_soltar_s = float(aj['iman_soltar_s'])
                if aj.get('enroque_por_afuera') is not None:
                    enroque_por_afuera = bool(aj['enroque_por_afuera'])
                if aj.get('espera_home_s') is not None:
                    espera_home_s = float(aj['espera_home_s'])
                if aj.get('vision_activa') is not None:
                    vision_activa = bool(aj['vision_activa'])
                if aj.get('vision_con_brazo') is not None:
                    vision_con_brazo = bool(aj['vision_con_brazo'])
                if aj.get('color_brazo') in ('blancas', 'negras'):
                    color_brazo = aj['color_brazo']
                if aj.get('volver_a_home') is not None:
                    volver_a_home = bool(aj['volver_a_home'])
                if aj.get('nivel') is not None:
                    nivel_actual = int(aj['nivel'])
                if aj.get('reinicio_horas') is not None:
                    reinicio_horas = float(aj['reinicio_horas'])
                if isinstance(aj.get('bajada_codo_banda'), dict):
                    bajada_codo_banda.update({k: int(v) for k, v in
                                              aj['bajada_codo_banda'].items()
                                              if v is not None})
                if isinstance(aj.get('bajada_codo_escaque'), dict):
                    bajada_codo_escaque.update({str(k).upper().replace('|PEON', '|peon')
                                                .replace('|REY', '|rey'): int(v)
                                                for k, v in aj['bajada_codo_escaque'].items()
                                                if v is not None})
                puntos_derivados = set(data.get('derivados', []))
            print(f"Calibracion cargada: {len(calibracion_puntos)} puntos (formato 2 alturas)")
            print(f"Ajustes: retraso={retraso_muneca_val} "
                  f"traslado_hombro={traslado_hombro} traslado_codo={traslado_codo}")
        except Exception as e:
            print(f"Error cargando calibracion: {e}")

def guardar_calibracion():
    """Guarda de forma ATOMICA y sincronizada a disco.

    json.dump deja los datos en el buffer del sistema: si la Pi se apaga poco
    despues, el cambio se pierde aunque la respuesta haya dicho OK. Se escribe
    en un temporal, se fuerza fsync y recien ahi se reemplaza el archivo, asi
    tampoco puede quedar a medias si se corta la luz durante la escritura."""
    tmp = ARCHIVO_CALIBRACION + '.tmp'
    try:
        with open(tmp, 'w') as f:
            json.dump({
                'puntos': calibracion_puntos,
                'tabla': tabla_escaques,
                'home': servo_home,
                'rutas': rutas_bajada,
                'captura': punto_captura,
                'espera': punto_espera,
                'derivados': sorted(puntos_derivados),
                'ajustes': {
                    'retraso_muneca_val': retraso_muneca_val,
                    'traslado_hombro': traslado_hombro,
                    'traslado_codo': traslado_codo,
                    'factor_vel_traslado': factor_vel_traslado,
                    'vel_muneca_bajada': vel_muneca_bajada,
                    'vel_muneca_bajada_cercana': vel_muneca_bajada_cercana,
                    'vel_muneca_bajada_media': vel_muneca_bajada_media,
                    'despegue_codo': despegue_codo,
                    'margen_aterrizaje_lejana': margen_aterrizaje_lejana,
                    'bajada_codo': bajada_codo,
                    'bajada_codo_banda': bajada_codo_banda,
                    'bajada_codo_escaque': bajada_codo_escaque,
                    'compensacion_muneca_cercana': compensacion_muneca_cercana,
                    'aterrizaje_directo': aterrizaje_directo,
                    'aterrizaje_ms': aterrizaje_ms,
                    'aterrizaje_vel': aterrizaje_vel,
                    'base_solo_arriba': base_solo_arriba,
                    'paso_transito': paso_transito,
                    'paso_bajada': paso_bajada,
                    'codo_max_encare': codo_max_encare,
                    'margen_max_encare': margen_max_encare,
                    'margen_max_cercana': margen_max_cercana,
                    'verif_activa': verif_activa,
                    'verif_tolerancia': verif_tolerancia,
                    'verif_ms': verif_ms,
                    'ruta_ms': ruta_ms,
                    'captura_altura_mm': captura_altura_mm,
                    'iman_espera_s': iman_espera_s,
                    'iman_soltar_s': iman_soltar_s,
                    'enroque_por_afuera': enroque_por_afuera,
                    'vision_activa': vision_activa,
                    'espera_home_s': espera_home_s,
                    'vision_con_brazo': vision_con_brazo,
                    'color_brazo': color_brazo,
                    'volver_a_home': volver_a_home,
                    'nivel': nivel_actual,
                    'reinicio_horas': reinicio_horas,
                }
            }, f, indent=2)
            f.flush()
            os.fsync(f.fileno())        # al disco de verdad, no al buffer
        os.replace(tmp, ARCHIVO_CALIBRACION)   # reemplazo atomico
        try:                            # sincronizar tambien la entrada de directorio
            d = os.open(os.path.dirname(ARCHIVO_CALIBRACION) or '.', os.O_RDONLY)
            os.fsync(d); os.close(d)
        except Exception:
            pass
    except Exception as e:
        print(f"Error guardando calibracion: {e}")
        try:
            os.remove(tmp)
        except Exception:
            pass

app = Flask(__name__)

tablero = chess.Board()  # BROKIE CIERRE: siempre arrancar en posicion inicial
engine = None
electroiman_estado = False

# ── ZONA DE CAPTURA ───────────────────────────────────────
# Punto sobre la caja de descarte. La pieza se SUELTA desde altura (no se
# apoya), asi no hace falta apilar con precision ni calibrar casilleros.
# Se graba a mano como cualquier punto: /captura/grabar con el brazo puesto.
punto_captura = None          # {1:..,2:..,3:..,4:..} sobre la caja
captura_altura_mm = 40        # cuanto MAS ARRIBA suelta respecto del punto
iman_espera_s = 1.0           # segundos que espera con el iman YA ENCENDIDO
                              # antes de levantar. La bobina tarda en establecer
                              # el campo y atraer la arandela; con menos tiempo
                              # a veces la pieza no queda bien magnetizada.
iman_soltar_s = 0.3           # espera al apagar, para que la pieza se libere

# En el enroque NO hay conflicto de trayectorias: el rey va a g1/c1 y la torre
# a f1/d1, que quedan libres. Alcanza con dos movimientos normales, primero el
# rey y despues la torre.
# El punto de maniobra fuera del tablero queda como OPCION por si en la
# practica alguna trayectoria roza: ahi la torre espera mientras se mueve el rey.
punto_espera = None
enroque_por_afuera = False    # True = usar el punto de maniobra

# En el enroque, a que casillas va la torre segun la jugada del rey
TORRE_ENROQUE = {'e1g1': ('h1', 'f1'), 'e1c1': ('a1', 'd1'),
                 'e8g8': ('h8', 'f8'), 'e8c8': ('a8', 'd8')}
volver_a_home = True          # al terminar la jugada, replegarse a home: quedar
                              # extendido sobre el escaque fuerza los servos

# COLOR DEL BRAZO. Las piezas del brazo se ponen SIEMPRE del lado del brazo
# (el lado de A1 fisico). Si el brazo juega negras, esas piezas estan cerca de
# el pero logicamente ocupan las filas 7-8, asi que el mapeo logico->fisico se
# rota 180 grados. Un solo parametro define las dos cosas.
color_brazo = 'blancas'       # 'blancas' = el brazo abre | 'negras' = responde

def sq_fisico(sq):
    """Escaque logico -> escaque FISICO del tablero calibrado."""
    sq = sq.upper()
    if color_brazo == 'blancas':
        return sq
    col = chr(ord('H') - (ord(sq[0]) - ord('A')))   # A<->H
    fila = str(9 - int(sq[1]))                       # 1<->8
    return col + fila

# Que altura de la tabla usa cada pieza
ALTURA_PIEZA = {'p': 'peon', 'n': 'rey', 'b': 'rey',
                'r': 'rey', 'q': 'rey', 'k': 'rey'}
servo_home = {1: 500, 2: 500, 3: 500, 4: 500}
calibracion_puntos = {}
tabla_escaques = {}
# Puntos generados por la PRE-CALIBRACION (no medidos a mano). Formato "A3:rey".
# Se usan para: a) no ensuciar el offset rey->peon con valores derivados,
# b) poder regenerarlos sin pisar lo que mediste vos.
puntos_derivados = set()

retraso_muneca_val = 1.0   # 1.0 = muñeca sincronizada con hombro
traslado_hombro = 402      # postura de traslado banda CERCANA (1-2) = punto de encare
traslado_codo   = 481      # perpendicular (imán vertical, medido en brazo). Ajustable.
factor_vel_traslado = 1.0  # multiplica step de tramos intermedios (2,3,4).
vel_muneca_bajada = 1.0       # velocidad de la muñeca en la bajada respecto a hombro/codo.
                                # transito; se conserva para que el HTML/JSON no rompan)
vel_muneca_bajada_cercana = 1.0  # en filas 1-2 debe avanzar sincronizada;
                                  # 1.3 hacía que llegara al ángulo final antes
                                  # que hombro/codo y tocara piezas al bajar.
vel_muneca_bajada_media = 1.0    # mismo sincronismo en filas 3-6. En B1->C3
                                  # la muñeca hacía mínimo->432 un 30% antes que
                                  # hombro/codo y entraba adelantada.
despegue_codo = 80              # u de codo (+) en el despegue COORDINADO (una sola curva
                                # con el hombro). La subida vertical de este brazo es
                                # sobre todo codo. Ajustable + persistente.
margen_aterrizaje_lejana = 70   # margen vertical (u de hombro) del punto intermedio de
                                # bajada en filas LEJANAS (7-8). Ajustable + persistente.
bajada_codo = 50                # u de codo (+) del punto intermedio de la BAJADA, sobre
                                # la vertical del destino (espejo del despegue). El
                                # tramo final baja hombro+margen y CIERRA codo-bajada_codo
                                # = vertical real, sin arco del hombro que barra la fila
                                # de atras (campana se trababa en E5 al aterrizar en E4).
                                # 0 = comportamiento viejo. Ajustable + persistente.

aterrizaje_directo = False   # True = el ultimo tramo se manda como UNA sola orden
                             # move() por servo (el servo interpola internamente).
                             # Evita la zona muerta: en la bajada el hombro solo
                             # recorre ~36u y en micro-pasos de <1.2u no arranca.
aterrizaje_ms = 500          # TIEMPO MINIMO de esa orden unica
aterrizaje_vel = 0.12        # velocidad del aterrizaje en u/ms. El tiempo se
                             # calcula con el RECORRIDO: con tiempo fijo, la
                             # banda lejana (margen 180u) bajaba 5x mas rapido
                             # que la cercana (36u) y despegaba la pieza.

# Diagnóstico post-aterrizaje. Se conserva el umbral y las claves históricas
# del JSON/API para no romper el panel, pero desde V60 nunca genera órdenes:
# la diferencia física se informa y el centrador absorbe el error residual.
verif_activa = False
verif_tolerancia = 2         # u de referencia para informar asentado_fino
verif_ms = 300               # compatibilidad de configuración; no mueve servos

# RUTAS DE BAJADA grabadas a mano: {'D1|rey': [ {1:..,2:..,3:..,4:..}, ... ]}
# Si un escaque tiene ruta, el transito la REPITE tramo por tramo (una orden por
# servo) en vez de calcular el punto intermedio. Sirve donde la formula de
# perpendicularidad no vale (fila 1: pide muñeca por debajo del tope).
rutas_bajada = {}
ruta_ms = 450                   # duracion de cada tramo de una ruta grabada

# Puntos GRABADOS A MANO: {'D4|rey', ...}. Se distinguen de los generados para
# que ninguna regeneracion los pise y para poder usarlos como anclas del modelo.

bajada_codo_banda = {}          # override de bajada_codo por banda:
                                # {'cercana': 20} p.ej. En los escaques mas
                                # cercanos el codo cierra hacia adentro y la
                                # campana roza el servo de la base; ahi conviene
                                # menos cierre aunque la bajada sea menos vertical.
bajada_codo_escaque = {}        # ajuste local "E1|rey": 170. Tiene prioridad
                                # sobre la banda y permite corregir un roce sin
                                # alterar los otros 127 perfiles auditados.
compensacion_muneca_cercana = 20  # retrasa la muñeca sólo en los tramos altos
                                  # de filas 1-2. MUNECA_MIN sigue siendo el
                                  # límite absoluto y los aterrizajes grabados
                                  # no se modifican.

transito_pausado = False

ESPERA_PAUSA_MAX = 300   # segundos. Una espera sin tope congela la aplicacion
                         # entera: este bucle corre con el candado de la partida
                         # tomado, asi que nada mas puede avanzar mientras tanto.

def esperar_si_pausado(etiqueta=""):
    """Si transito_pausado esta activo, espera a que se reanude.

    Con TOPE: si nadie reanuda, aborta. Nunca equivale a una reanudación.
    """
    if not transito_pausado:
        return
    _bit('brazo', f'transito PAUSADO en: {etiqueta}')
    t0 = time.time()
    generacion = globals().get('_cancelacion_movimiento', 0)
    while transito_pausado:
        if generacion != globals().get('_cancelacion_movimiento', 0):
            raise RuntimeError('Movimiento cancelado al liberar servos')
        if time.time() - t0 > ESPERA_PAUSA_MAX:
            _bit('brazo', f'pausa de {ESPERA_PAUSA_MAX}s sin reanudar: cancelo movimiento',
                 etiqueta=etiqueta)
            raise TimeoutError('Pausa de tránsito vencida; movimiento cancelado')
        time.sleep(0.1)
    _bit('brazo', f'transito reanudado en: {etiqueta}')

TRASLADO_LEJANA = {2: 791, 3: 834, 4: 270}   # hombro, codo, muñeca
TRASLADO_MEDIA = {2: 625, 3: 582, 4: 309}    # hombro, codo, muñeca

FILAS_LEJANAS = ('7', '8')
FILAS_MEDIAS  = ('3', '4', '5', '6')
FILAS_CERCANAS = ('1', '2')

def banda_de(sq):
    """Devuelve 'lejana', 'media' o 'cercana' segun la fila del escaque destino."""
    if not sq or len(sq) < 2:
        return 'cercana'
    fila = sq[-1]
    if fila in FILAS_LEJANAS:
        return 'lejana'
    if fila in FILAS_MEDIAS:
        return 'media'
    return 'cercana'


# Stockfish acotado: en una Pi de 1GB el Hash por defecto se come RAM que
# no hace falta. Con 16MB y 1 hilo juega muchisimo mas fuerte que cualquier
# humano y deja la maquina libre para el control de los servos.
SF_HASH_MB = int(os.environ.get('SF_HASH_MB', '16'))
SF_THREADS = int(os.environ.get('SF_THREADS', '1'))
try:
    engine = chess.engine.SimpleEngine.popen_uci("/usr/games/stockfish")
    try:
        engine.configure({'Hash': SF_HASH_MB, 'Threads': SF_THREADS})
    except Exception as _e:
        print(f"Stockfish sin configurar Hash/Threads: {_e}")
    STOCKFISH_OK = True
except Exception as e:
    print(f"Stockfish no disponible: {e}")
    STOCKFISH_OK = False

# ── NIVELES DE JUEGO ──────────────────────────────────────
# 10 niveles por NOMBRE, no por Elo: los Elo de Stockfish estan calibrados
# contra otros motores y por debajo de ~1320 el motor no los soporta, asi que
# poner un numero seria inventarlo.
#
# Los niveles bajos NO se consiguen limitando la profundidad (eso da un rival
# que calcula poco pero igual no cuelga piezas). Se consiguen con MultiPV:
# se le piden al motor las N mejores jugadas y se elige entre ellas al azar
# con un sesgo. Asi comete errores de verdad, como un principiante.
# 'perdida' = cuantos centipeones puede ceder como maximo respecto de la mejor
# jugada. Es LO QUE HACE QUE UN NIVEL BAJO SEA DEBIL PERO NO ABSURDO: antes se
# elegia entre las N mejores por PUESTO, sin mirar la evaluacion, asi que podia
# preferir la cuarta opcion aunque significara regalar una torre. Ahora solo se
# aparta de la mejor mientras el costo entre en ese margen.
NIVELES = [
    # nombre        multipv  sesgo  depth  uci_elo  perdida
    ('Novato',            8,  0.00,     4,  None,      250),
    ('Principiante',      6,  0.15,     5,  None,      180),
    ('Aprendiz',          5,  0.30,     6,  None,      130),
    ('Casual',            4,  0.45,     7,  None,       90),
    ('Intermedio',        3,  0.60,     8,  None,       60),
    ('Club',              2,  0.75,    10,  None,       35),
    ('Avanzado',          1,  1.00,  None,  1500,        0),
    ('Fuerte',            1,  1.00,  None,  1750,        0),
    ('Experto',           1,  1.00,  None,  2000,        0),
    ('Maestro',           1,  1.00,  None,  2300,        0),
]
nivel_actual = 3                      # 1..10

def _rango_elo_motor():
    """(min, max) de UCI_Elo que soporta este binario. None si no lo soporta."""
    try:
        o = engine.options.get('UCI_Elo')
        if o is not None:
            return int(o.min), int(o.max)
    except Exception:
        pass
    return None

def aplicar_nivel(n):
    """Configura el motor para el nivel n (1..10). Devuelve (ok, detalle)."""
    global nivel_actual, reinicio_horas
    if not engine:
        return False, 'Motor no disponible'
    n = max(1, min(len(NIVELES), int(n)))
    nombre, multipv, sesgo, depth, elo, _perd = NIVELES[n - 1]
    opts = {}
    rango = _rango_elo_motor()
    if elo and rango:
        opts['UCI_LimitStrength'] = True
        opts['UCI_Elo'] = max(rango[0], min(rango[1], elo))
    else:
        opts['UCI_LimitStrength'] = False
        # Skill Level acompaña: bajo en los primeros niveles
        opts['Skill Level'] = int(round(4 + sesgo * 16))
    try:
        engine.configure(opts)
    except Exception as e:
        return False, f'No se pudo configurar el motor: {e}'
    nivel_actual = n
    return True, {'nivel': n, 'nombre': nombre, 'opciones': opts}

def elegir_jugada():
    """Jugada del motor segun el nivel.

    En los niveles bajos elige entre varias jugadas buenas, pero SOLO entre las
    que no pierden mas de 'perdida' centipeones respecto de la mejor. Elegir
    por puesto sin mirar la evaluacion hacia que un nivel bajo pudiera dejar de
    comer una torre o no responder a un jaque de forma sensata: eso no es jugar
    mas debil, es regalar material.
    """
    nombre, multipv, sesgo, depth, elo, perdida = NIVELES[nivel_actual - 1]
    lim = chess.engine.Limit(depth=depth) if depth else chess.engine.Limit(time=0.6)
    if multipv <= 1:
        return engine.play(tablero, lim).move
    try:
        info = engine.analyse(tablero, lim, multipv=multipv)
    except Exception:
        return engine.play(tablero, lim).move

    opciones = []
    for i in info:
        if not i.get('pv'):
            continue
        try:
            pov = i['score'].pov(tablero.turn)
            cp = pov.score(mate_score=100000)
        except Exception:
            cp = None
        opciones.append((i['pv'][0], cp))
    if not opciones:
        return engine.play(tablero, lim).move

    mejor_cp = opciones[0][1]
    if mejor_cp is not None:
        # descartar todo lo que cueste mas de 'perdida' centipeones
        opciones = [(mv, cp) for mv, cp in opciones
                    if cp is None or (mejor_cp - cp) <= perdida]
    jugadas = [mv for mv, _cp in opciones]
    if len(jugadas) == 1 or sesgo >= 1.0:
        return jugadas[0]

    pesos = [(1.0 - sesgo) ** k for k in range(len(jugadas))]
    total = sum(pesos) or 1.0
    r = random.random() * total
    acum = 0.0
    for mv, p in zip(jugadas, pesos):
        acum += p
        if r <= acum:
            return mv
    return jugadas[0]

# ── CINEMATICA DE PERPENDICULARIDAD ───────────────────────
#   muñeca = 256.0 + 1.0143*hombro - 0.9837*codo
def muneca_perp(hombro, codo):
    """Muñeca que deja el iman perpendicular (pieza vertical) para ese hombro/codo.
    SEGURIDAD: nunca menor a MUNECA_MIN (mas abajo la muñeca toca el codo)."""
    m = 256.0 + 1.0143 * hombro - 0.9837 * codo
    return int(max(MUNECA_MIN, min(1000, m)))


def muneca_transito(hombro, codo, banda):
    """Muñeca de tránsito con corrección exclusiva de la banda cercana.

    La corrección se aplica después del cálculo geométrico y nunca puede
    atravesar MUNECA_MIN=154. No se usa para el aterrizaje calibrado.
    """
    objetivo = muneca_perp(hombro, codo)
    if banda == 'cercana':
        objetivo = max(MUNECA_MIN,
                       objetivo - max(0, int(compensacion_muneca_cercana)))
    return objetivo


def leer_posiciones_u():
    """Posiciones reales en unidades 0-1000."""
    pos = {}
    for sid, s in servos.items():
        try:
            pos[sid] = g2u(s.get_physical_angle())
            _lecturas_servos_actuales[sid] = (time.monotonic(), True)
        except Exception:
            pos[sid] = None
            _lecturas_servos_actuales[sid] = (time.monotonic(), False)
    return pos

def _leer_servo_robusto(s, intentos=3):
    """Lee un servo con reintentos. Descarta lecturas fuera de rango fisico (0-1000u)."""
    for _ in range(intentos):
        try:
            g = s.get_physical_angle()
            if g is None:
                continue
            u = g2u(g)
            if 0 <= u <= 1000:
                return u
        except Exception:
            pass
        time.sleep(0.02)
    return None

def leer_posiciones_robusta(referencia=None, salto_max=None):
    """Lee las 4 posiciones de forma robusta (reintento + rango + salto maximo)."""
    pos = {}
    sospechosos = []
    for sid, s in servos.items():
        u = _leer_servo_robusto(s)
        _lecturas_servos_actuales[sid] = (time.monotonic(), u is not None)
        if u is None:
            sospechosos.append(sid)
            if referencia is not None and referencia.get(sid) is not None:
                pos[sid] = referencia[sid]
            else:
                pos[sid] = None
            continue
        if (referencia is not None and salto_max is not None
                and referencia.get(sid) is not None
                and abs(u - referencia[sid]) > salto_max):
            sospechosos.append(sid)
            pos[sid] = referencia[sid]
        else:
            pos[sid] = u
    return pos, sospechosos


def _contar_lecturas(sospechosos):
    global lecturas_ok, lecturas_falladas
    if sospechosos:
        lecturas_falladas += 1
        for sid in sospechosos:
            fallas_por_servo[sid] = fallas_por_servo.get(sid, 0) + 1
    else:
        lecturas_ok += 1

def pos_real(referencia=None):
    """Lectura fresca para ANCLAR el arranque de una interpolacion."""
    p, sosp = leer_posiciones_robusta(referencia=referencia,
                                      salto_max=SALTO_MAX_ARRANQUE)
    _contar_lecturas(sosp)
    return p

TOPE_MOVIMIENTO_S = 25   # segundos. Sin tope, si un servo no termina su curva
                         # este bucle gira para siempre CON EL CANDADO DE LA
                         # PARTIDA TOMADO: la aplicacion entera queda colgada
                         # y no hay forma de salir sin reiniciar el servicio.

# Prueba: una única consigna cada 25 ms. La redundancia UART permanece OFF.
# Las duraciones geométricas no cambian; sólo se duplica el muestreo temporal.
SERVO_COMANDO_INTERVALO_S = 0.025


def _mover_servo_copia(sid, angulo, tiempo_ms, copia_uart):
    """Etiqueta la copia en el wrapper real sin exigirlo a dobles de prueba."""
    servo = servos[sid]
    try:
        return servo.move(angulo, tiempo_ms, _copia_uart=copia_uart)
    except TypeError as exc:
        # Compatibilidad con el LX16A crudo y dobles antiguos. Sólo se omite
        # la etiqueta interna; cualquier otro TypeError conserva su causa.
        if '_copia_uart' not in str(exc):
            raise
        return servo.move(angulo, tiempo_ms)


def _repetir_lote_servo(comandos):
    """Segunda copia UART de un lote ya enviado, sin lecturas intermedias."""
    if not globals().get('SERVO_REDUNDANCIA_UART', False) or not comandos:
        return
    time.sleep(max(0.0, float(globals().get(
        'SERVO_REDUNDANCIA_PAUSA_S', 0.003))))
    for sid, angulo, tiempo_ms in comandos:
        _mover_servo_copia(sid, angulo, tiempo_ms, 'redundante')


def _enviar_lote_servo(comandos):
    """Envía 1-2-3-4 y luego su copia 1-2-3-4 con el mismo objetivo."""
    lote = list(comandos)
    for sid, angulo, tiempo_ms in lote:
        _mover_servo_copia(sid, angulo, tiempo_ms, 'primaria')
    _repetir_lote_servo(lote)

# Auditoría temporal de trayectoria. Registra las consignas que el suavizador
# ya envió; NO lee posiciones ni agrega consultas al bus de servos.
TRAZA_MOVIMIENTO_ACTIVA = True
TRAZA_MOVIMIENTO_MS = 100

# Movimiento sin el supervisor experimental anti-tirones.
# Se conservan el perfil suave, el reloj monótono y el tope histórico de 25 s.
# No hay prevuelo añadido, retenciones por desfase ni enclavamiento posterior.
def mover_suave_a(pos_u, step=0.025, hasta=1.0, desde=None, retraso_muneca=1.0):
    """Ejecuta la curva sin consultas de seguimiento ni retenciones añadidas."""
    participantes = [sid for sid in servos if pos_u.get(sid) is not None]
    generacion = globals().get('_cancelacion_movimiento', 0)
    trazar = bool(globals().get('TRAZA_MOVIMIENTO_ACTIVA', False))
    intervalo_traza = max(50, int(globals().get('TRAZA_MOVIMIENTO_MS', 100)))
    traza_id = str(time.monotonic_ns())[-10:]
    traza_inicio = time.monotonic()
    siguiente_traza_ms = 0
    # Un eje excluido del tramo (por ejemplo la base al bajar) no debe recibir
    # puntos residuales del tramo anterior. Esto no limita el movimiento.
    for sm in smooth.values():
        sm.running = False
    if not participantes:
        return True
    contexto_auditoria = globals().get('_servo_auditoria_contexto')
    traza_anterior = (getattr(contexto_auditoria, 'traza_id', None)
                      if contexto_auditoria is not None else None)
    if contexto_auditoria is not None:
        contexto_auditoria.traza_id = traza_id
    try:
        if trazar:
            _bit('brazo', 'TRAZA CURVA inicio', traza_id=traza_id,
                 desde={sid: (desde or {}).get(sid) for sid in participantes},
                 destino={sid: pos_u.get(sid) for sid in participantes},
                 step=step, hasta=hasta, retraso_muneca=retraso_muneca)
        for sid in participantes:
            sa = None
            if desde is not None and desde.get(sid) is not None:
                sa = u2g(desde[sid])
            step_sid = (step / retraso_muneca
                        if sid == 4 and retraso_muneca > 0 else step)
            smooth[sid].start(u2g(pos_u[sid]), step=step_sid,
                              start_angle=sa)
        t0 = time.monotonic()
        while any(smooth[sid].is_running() and
                  (hasta >= 1.0 or smooth[sid].x < hasta)
                  for sid in participantes):
            if generacion != globals().get('_cancelacion_movimiento', 0):
                return False
            if globals().get('transito_pausado', False):
                inicio_pausa = time.monotonic()
                esperar_si_pausado('curva suave')
                t0 += time.monotonic() - inicio_pausa
            if time.monotonic() - t0 > TOPE_MOVIMIENTO_S:
                _bit('brazo', f'MOVIMIENTO TRABADO tras {TOPE_MOVIMIENTO_S}s: aborto',
                     destino=pos_u)
                return False
            ms = time.monotonic_ns() // 1_000_000
            lote_redundante = []
            for sid in participantes:
                anterior_ms = smooth[sid].last_command_ms
                smooth[sid].update(ms)
                if smooth[sid].last_error is not None:
                    _bit('brazo', 'movimiento abortado por fallo de escritura',
                         servo=sid, error=str(smooth[sid].last_error))
                    return False
                if smooth[sid].last_command_ms != anterior_ms:
                    lote_redundante.append((
                        sid, smooth[sid].last_command_angle,
                        smooth[sid].command_interval_ms))
            # SmoothServo ya emitió la pasada primaria para todos los ejes.
            # Repetir el lote completo conserva el orden 1-2-3-4 / 1-2-3-4.
            _repetir_lote_servo(lote_redundante)
            transcurrido_ms = int((time.monotonic() - traza_inicio) * 1000)
            if trazar and transcurrido_ms >= siguiente_traza_ms:
                consignas = {}
                avances = {}
                for sid in participantes:
                    sm = smooth[sid]
                    angulo = getattr(sm, 'last_command_angle', None)
                    consignas[sid] = (None if angulo is None else g2u(angulo))
                    avances[sid] = round(float(getattr(sm, 'x', 0.0)), 3)
                _bit('brazo', 'TRAZA CURVA punto', traza_id=traza_id,
                     ms=transcurrido_ms, consigna=consignas, avance=avances)
                siguiente_traza_ms = transcurrido_ms + intervalo_traza
            time.sleep(0.01)
        time.sleep(0.050)
        if trazar:
            _bit('brazo', 'TRAZA CURVA fin', traza_id=traza_id,
                 ms=int((time.monotonic() - traza_inicio) * 1000),
                 destino={sid: pos_u.get(sid) for sid in participantes})
        return True
    except Exception as e:
        _bit('brazo', 'no inicio movimiento sin posición real', error=str(e))
        return False
    finally:
        for sm in smooth.values():
            sm.running = False
        if contexto_auditoria is not None:
            if traza_anterior is None:
                try:
                    del contexto_auditoria.traza_id
                except AttributeError:
                    pass
            else:
                contexto_auditoria.traza_id = traza_anterior


def _pendientes_ruta_monotona(tiempos, valores):
    """Pendientes PCHIP: continuidad C1 sin sobrepasar puntos calibrados."""
    n = len(valores)
    if n < 2:
        return [0.0] * n
    h = [tiempos[i + 1] - tiempos[i] for i in range(n - 1)]
    d = [(valores[i + 1] - valores[i]) / h[i] for i in range(n - 1)]
    m = [0.0] * n                 # inicio y final realmente detenidos
    for i in range(1, n - 1):
        if d[i - 1] == 0 or d[i] == 0 or d[i - 1] * d[i] <= 0:
            m[i] = 0.0            # extremo/inversion: ese eje sí debe frenar
            continue
        w1 = 2 * h[i] + h[i - 1]
        w2 = h[i] + 2 * h[i - 1]
        m[i] = (w1 + w2) / (w1 / d[i - 1] + w2 / d[i])
    return m


def _valor_ruta_monotona(tiempos, valores, pendientes, ahora):
    """Evalúa un tramo Hermite monótono de la trayectoria multipunto."""
    if ahora <= tiempos[0]:
        return float(valores[0]), 0
    if ahora >= tiempos[-1]:
        return float(valores[-1]), len(tiempos) - 2
    i = 0
    while i + 1 < len(tiempos) and ahora > tiempos[i + 1]:
        i += 1
    h = tiempos[i + 1] - tiempos[i]
    u = (ahora - tiempos[i]) / h
    u2, u3 = u * u, u * u * u
    h00 = 2 * u3 - 3 * u2 + 1
    h10 = u3 - 2 * u2 + u
    h01 = -2 * u3 + 3 * u2
    h11 = u3 - u2
    valor = (h00 * valores[i] + h10 * h * pendientes[i]
             + h01 * valores[i + 1] + h11 * h * pendientes[i + 1])
    return valor, i


def _pendientes_ruta_coordinada(tiempos, valores):
    pendientes = {sid: _pendientes_ruta_monotona(tiempos, v)
                  for sid, v in valores.items()}
    if len(tiempos) < 3:
        return pendientes
    fracciones = [(v[-2] - v[-3]) / (v[-1] - v[-3])
                  for v in valores.values() if v[-1] != v[-3]]
    f = fracciones[0] if fracciones else None
    colineales = f is not None and 0 < f < 1 and all(
        abs(v[-2] - (v[-3] + f * (v[-1] - v[-3]))) < 1e-8
        for v in valores.values())
    if colineales:
        progreso = _pendientes_ruta_monotona(tiempos[-3:], [0.0, f, 1.0])
        for sid, v in valores.items():
            pendientes[sid][-3:] = [(v[-1] - v[-3]) * m for m in progreso]
    return pendientes


def _muneca_contacto(pose, ancla, adelanto_u=0.0):
    """Compensación diferencial local; conserva la orientación calibrada.

    En las primeras/últimas 8 unidades articulares sigue H/C exactamente.
    Entre 8 y 20 se funde suavemente con la trayectoria existente. Fuera
    de esa zona no modifica el encare ni el tránsito. No implica verticalidad
    cartesiana ni sustituye la calibración física.
    """
    dh, dc = pose[2] - ancla[2], pose[3] - ancla[3]
    distancia = max(abs(dh), abs(dc))
    if distancia >= 20.0:
        return pose[4]
    u = max(0.0, (distancia - 8.0) / 12.0)
    peso = 1.0 - u*u*u*(10.0 + u*(-15.0 + 6.0*u))
    objetivo = ancla[4] + 1.0143*dh - 0.9837*dc
    # Al retirar una pieza ya suelta puede quedar un pequeño error físico de
    # muñeca respecto de la pose calibrada. No corregirlo de golpe estando
    # todavía apoyado: incorporarlo durante las primeras 8u de elevación y
    # fundirlo junto con la compensación local antes de abandonar la pieza.
    entrada = min(1.0, distancia / 8.0)
    entrada = entrada*entrada*(3.0 - 2.0*entrada)
    objetivo += max(0.0, float(adelanto_u)) * entrada
    return max(MUNECA_MIN, min(1000.0,
               pose[4] + peso*(objetivo - pose[4])))


def mover_suave_ruta(puntos, pasos, contexto='transicion continua',
                     compensar_salida=False, compensar_llegada=False,
                     adelanto_salida_u=0.0, salida_codo_primero=False):
    """Recorre varios puntos como UNA curva temporal continua.

    Los puntos intermedios siguen siendo respetados exactamente, pero no
    reinician el perfil. Cada eje conserva velocidad a través del punto si
    continúa en el mismo sentido; sólo frena si queda fijo o invierte sentido.
    """
    intervalo_comando_s = float(globals().get(
        'SERVO_COMANDO_INTERVALO_S', 0.025))
    error_local = globals().get('_error_trayectoria')
    if error_local is not None:
        error_local.detalle = None
    if len(puntos) < 2 or len(pasos) != len(puntos) - 1:
        return False
    participantes = list(servos)
    # Una pose incompleta no autoriza a mover sólo los ejes restantes.
    # Validar todo antes de emitir la primera consigna.
    try:
        validos = participantes and all(
            math.isfinite(float(p[sid])) and 0 <= float(p[sid]) <= 1000
            for p in puntos for sid in participantes)
        pasos_validos = all(math.isfinite(float(p)) and float(p) > 0
                            for p in pasos)
    except (KeyError, TypeError, ValueError, OverflowError):
        return False
    if not validos or not pasos_validos:
        return False

    # `step` expresa la velocidad histórica a 50 ms. Estas duraciones se
    # conservan aunque ahora se evalúe y emita la curva cada 25 ms: así se
    # duplica la resolución sin duplicar la velocidad física.
    duraciones = [0.050 * max(1, math.ceil(1.0 / float(p)))
                  for p in pasos]
    tiempos = [0.0]
    for duracion in duraciones:
        tiempos.append(tiempos[-1] + duracion)
    valores = {sid: [float(p[sid]) for p in puntos]
               for sid in participantes}
    # Los dos últimos tramos de aterrizaje son una misma recta articular,
    # dividida únicamente para reservar tiempo al contacto. Un progreso
    # escalar compartido evita que cada articulación curve esa recta.
    pendientes = _pendientes_ruta_coordinada(tiempos, valores)

    for sm in smooth.values():
        sm.running = False
    trazar = bool(globals().get('TRAZA_MOVIMIENTO_ACTIVA', False))
    intervalo_traza = max(50, int(globals().get('TRAZA_MOVIMIENTO_MS', 100)))
    traza_id = str(time.monotonic_ns())[-10:]
    auditoria = globals().get('_servo_auditoria_contexto')
    traza_anterior = (getattr(auditoria, 'traza_id', None)
                      if auditoria is not None else None)
    if auditoria is not None:
        auditoria.traza_id = traza_id
    inicio = time.monotonic()
    generacion = globals().get('_cancelacion_movimiento', 0)
    siguiente_envio = 0.0
    tiempo_ruta = 0.0
    siguiente_traza_ms = 0
    ultimo = None
    try:
        if trazar:
            _bit('brazo', 'TRAZA CONTINUA inicio', traza_id=traza_id,
                 contexto=contexto, puntos=puntos, pasos=pasos,
                 duracion_ms=round(tiempos[-1] * 1000))
        while True:
            if generacion != globals().get('_cancelacion_movimiento', 0):
                return False
            if globals().get('transito_pausado', False):
                inicio_pausa = time.monotonic()
                esperar_si_pausado(contexto)
                # No recuperar el tiempo de pausa con un salto de consigna,
                # ni descontarlo del tiempo máximo de movimiento activo.
                inicio += time.monotonic() - inicio_pausa
            transcurrido = time.monotonic() - inicio
            if transcurrido > TOPE_MOVIMIENTO_S:
                _bit('brazo', f'MOVIMIENTO TRABADO tras {TOPE_MOVIMIENTO_S}s: aborto',
                     contexto=contexto, destino=puntos[-1])
                return False
            if transcurrido + 1e-9 >= siguiente_envio:
                # El reloj de la curva avanza UNA muestra por escritura. Si el
                # proceso queda demorado, no intenta recuperar tiempo enviando
                # varias consignas juntas ni salta hacia una muestra lejana.
                # La consecuencia segura de una demora es que el movimiento se
                # prolonga, nunca que aumente su velocidad instantánea.
                t_eval = min(tiempo_ruta, tiempos[-1])
                consignas = {}
                tramo = 0
                pose = {}
                for sid in participantes:
                    valor, tramo = _valor_ruta_monotona(
                        tiempos, valores[sid], pendientes[sid], t_eval)
                    pose[sid] = valor
                if salida_codo_primero and tramo == 0:
                    # El codo abre durante el primer tramo, pero la muñeca
                    # acompaña con la relación geométrica medida para que conserve
                    # su orientación. Sin esta compensación el servo 4 queda
                    # quieto, aunque físicamente la mano cabecea hacia delante
                    # por el giro del antebrazo.
                    pose[4] = (puntos[0][4]
                               - 0.9837*(pose[3] - puntos[0][3]))
                elif compensar_salida and tramo == 0:
                    pose[4] = _muneca_contacto(
                        pose, puntos[0], adelanto_u=adelanto_salida_u)
                elif compensar_llegada and tramo >= len(puntos) - 3:
                    pose[4] = _muneca_contacto(pose, puntos[-1])
                lote = []
                for sid in participantes:
                    valor = pose[sid]
                    if sid == 4:
                        valor = max(MUNECA_MIN, valor)
                    consignas[sid] = int(round(valor))
                    lote.append((
                        sid, u2g(valor),
                        round(intervalo_comando_s * 1000)))
                _enviar_lote_servo(lote)
                ultimo = consignas
                tiempo_ruta = min(
                    tiempos[-1], tiempo_ruta + intervalo_comando_s)
                siguiente_envio = transcurrido + intervalo_comando_s
                ms = int(transcurrido * 1000)
                if trazar and ms >= siguiente_traza_ms:
                    _bit('brazo', 'TRAZA CONTINUA punto', traza_id=traza_id,
                         ms=ms, tramo=tramo + 1, consigna=consignas)
                    siguiente_traza_ms = ms + intervalo_traza
                if t_eval >= tiempos[-1]:
                    # La última consigna debe disponer del horizonte completo.
                    time.sleep(intervalo_comando_s)
                    break
            time.sleep(0.005)
        if trazar:
            _bit('brazo', 'TRAZA CONTINUA fin', traza_id=traza_id,
                 ms=int((time.monotonic() - inicio) * 1000),
                 destino={sid: puntos[-1][sid] for sid in participantes},
                 ultima_consigna=ultimo)
        return True
    except Exception as e:
        _bit('brazo', 'movimiento continuo abortado por fallo de escritura',
             contexto=contexto, error=str(e))
        if error_local is not None:
            error_local.detalle = f'Movimiento interrumpido: {e}'
        return False
    finally:
        if auditoria is not None:
            if traza_anterior is None:
                try:
                    del auditoria.traza_id
                except AttributeError:
                    pass
            else:
                auditoria.traza_id = traza_anterior


def _mover_directo(destino, sids, tiempo_ms, contexto):
    """Orden directa histórica: envío y espera, sin supervisor añadido."""
    try:
        _enviar_lote_servo([
            (sid, u2g(destino[sid]), int(tiempo_ms))
            for sid in sids if destino.get(sid) is not None
        ])
    except Exception as e:
        _bit('brazo', 'fallo de servo en movimiento directo',
             contexto=contexto, error=str(e))
        return False
    time.sleep(max(1, int(tiempo_ms)) / 1000.0 + 0.15)
    return True

paso_bajada = 0.030      # step del ultimo tramo de BAJADA (del hover al punto).
# Perfil de contacto: el primer 85% conserva el ritmo rapido y los ultimos
# 15% tienen un segundo propio de amortiguacion. No se acelera artificialmente
# el tramo anterior para compensar: el aterrizaje agrega solo 0.4 s.
FRACCION_PRECONTACTO = 0.85
FRACCION_TIEMPO_PRECONTACTO = 1.0
CONTACTO_FINAL_S = 1.0
# El retiro vacío sólo necesita separarse de la pieza recién soltada. Al
# transportar una pieza se agregan 20u de altura para librar una pieza posterior
# aunque alguna de las dos haya quedado ligeramente descentrada. El retiro con
# pieza recorre 60u en los mismos 0,75s que antes usaba para 50u: es un aumento
# moderado del 20% limitado exclusivamente a este primer tramo vertical.
RETIRO_CODO_POST_SUELTA_U = 40
RETIRO_CODO_CON_PIEZA_U = 60
PASO_RETIRO_POST_SUELTA = 1.0 / 12.0
PASO_RETIRO_CON_PIEZA = 1.0 / 15.0
# Mantener la velocidad histórica de la salida vacía. El ensayo a 1,15x hizo
# más brusca la gran transición angular de muñeca posterior al codo inicial y
# dificultó distinguirla de la compensación geométrica de esos primeros 40u.
FACTOR_SALIDA_VACIA = 1.0

# Simetria local comprobada con la salida limpia B8->C6. Al pasar por el mismo
# hombro/codo del encare de B8, la salida lleva la muñeca cerca de 219u; la
# bajada calculada la llevaba al límite mínimo y la base del caballo invadía B7.
# Sólo cambia la orientación al entrar en la curva; el destino calibrado B8,
# el tiempo y hombro/codo permanecen intactos.
MUNECA_ENCARE_ESCAQUE = {
    'B8|rey': 219,
}

# Encare de la fila 2 que reproduce al revés el despegue limpio comprobado en
# G2->B7. Evita que la base de la pieza transportada barra la cabeza de una
# pieza en la fila 1. Los valores son desplazamientos respecto del destino
# final (subida de hombro, apertura de codo); la muñeca continúa calculándose.
# Se aplica a ambas alturas y no modifica la fila 1 ni las demás bandas.
ENCARE_HC_FILA = {
    '2': (160, 222),
}
                         # Mas chico = llega mas despacio y frena mas suave. El
                         # brazo tiene 1-2cm de flexion y llegar con inercia lo
                         # deja vibrando varios segundos: eso obliga a esperar
                         # antes de fotografiar y descalibra la lectura de
                         # casillas si se mira demasiado pronto.
paso_transito = 0.032    # step del tramo de transito (despegue -> encare).
                         # Mas chico = mas lento. El despegue usa 0.03; este
                         # tramo es el mas largo (media vuelta de base en un
                         # A1->H8) y conviene mas suave.

transito_directo = True  # True = del despegue al punto de encare en UN solo
                         # movimiento suave: todos los servos interpolan con el
                         # mismo perfil, asi el codo no puede adelantarse al
                         # hombro. False = riel de posturas fijas (viejo).

base_solo_arriba = True  # una vez llegada arriba, la base NO se toca mas:
                         # se la excluye del aterrizaje y de la verificacion, asi
                         # no queda ningun giro lateral al tocar la pieza. Ponerlo
                         # en False solo para volver al comportamiento viejo.
codo_max_encare = 790    # tope del codo en el punto de encare. Cada escaque
                         # saca de aca cuanta altura puede tomar: los del fondo
                         # (codo alto al aterrizar) suben poco, los de fila 7
                         # mucho mas. Un margen fijo para toda la banda dejaba
                         # a E7 entrando raspando sobre E6.
margen_max_encare = 120  # tope de altura del encare (u de hombro, ~10cm)
margen_max_cercana = 80  # en la banda CERCANA el brazo esta plegado y subir
                         # 10cm es un movimiento de hombro innecesario, pero
                         # 3cm no libra las piezas de fila 1 al bajar en fila 2.
                         # 80u = 6.7cm: pasa por encima de una pieza de 5.6cm

DESPEGUE_HOMBRO = 60     # ~5cm de subida vertical pura al salir
ATERRIZAJE_HOMBRO = 36   # ~3cm de bajada vertical pura al llegar

SALTO_MAX_ARRANQUE = 150  # u: salto max plausible entre lecturas

# Salud del enlace serie. Cada lectura fallida se sustituye por el valor viejo,
# y si ese valor alimenta el arranque de una interpolacion, el servo SALTA.
# Se cuentan para poder ver la degradacion antes de que se note moviendo.
lecturas_ok = 0
_lecturas_servos_actuales = {}
lecturas_falladas = 0
fallas_por_servo = {1: 0, 2: 0, 3: 0, 4: 0}
arranque_ts = time.time()

# Reinicio preventivo: el enlace serie se degrada con las horas. Se reinicia
# solo cuando el brazo esta QUIETO, para no cortar a mitad de un movimiento.
# DESACTIVADO por defecto: al cumplirse las horas el proceso se cierra solo y
# depende de que el servicio tenga Restart=always para volver a levantar. Si no
# lo tiene, la app se cae y no vuelve. Activalo solo despues de verificar:
#     grep -i restart /etc/systemd/system/chess.service
reinicio_horas = 0          # 0 = desactivado
reinicio_quieto_s = 45      # segundos de inactividad exigidos
ultimo_mov_ts = time.time()

# Se carga DESPUES de definir todos los ajustes: si se llamara antes, las
# asignaciones por defecto de mas abajo pisarian lo leido del archivo.
cargar_calibracion()
# La camara va en la muneca: para esta version la estabilizacion minima es 8 s.
# Si el JSON viejo tenia 5 s, no se permite volver a una espera mas corta.
# BROKIE 4.0: estabilización post-HOME fijada a 5 s (solicitado y probado sobre V35).
espera_home_s = 5.0

# ── MALLA DE SEGURIDAD ────────────────────────────────────
# Ninguna orden puede salir del envolvente que define el propio tablero ya
# calibrado, ni saltar mas de lo plausible desde donde esta el brazo.
limites_servo = {}          # {sid: (min, max)} calculado de la calibracion
relacion_codo = None        # (a, b): en un aterrizaje, codo ~ a*hombro + b.
                            # Hombro y codo NO son libres: los dos dependen de
                            # la distancia al escaque. Un hombro valido con un
                            # codo que no le corresponde = pose imposible.
tol_relacion = 70           # u de desvio tolerado en esa relacion
margen_limites = 60         # u de tolerancia sobre lo calibrado
salto_max_orden = 350       # u: salto maximo de un servo en una sola orden
malla_activa = True

def recalcular_limites():
    """Envolvente seguro a partir de TODO lo calibrado (puntos + tabla)."""
    global limites_servo
    vals = {sid: [] for sid in (1, 2, 3, 4)}
    for origen in (calibracion_puntos, tabla_escaques):
        for _sq, capas in origen.items():
            if not isinstance(capas, dict):
                continue
            for _alt, p in capas.items():
                if not isinstance(p, dict):
                    continue
                for sid in (1, 2, 3, 4):
                    if p.get(sid) is not None:
                        vals[sid].append(p[sid])
    limites_servo = {sid: (min(v) - margen_limites, max(v) + margen_limites)
                     for sid, v in vals.items() if v}
    # recta codo-hombro por minimos cuadrados sobre TODOS los aterrizajes
    global relacion_codo
    xs, ys = vals.get(2, []), vals.get(3, [])
    if len(xs) >= 8 and len(xs) == len(ys):
        n = len(xs); sx = sum(xs); sy = sum(ys)
        sxx = sum(x * x for x in xs); sxy = sum(x * y for x, y in zip(xs, ys))
        den = n * sxx - sx * sx
        if den:
            a = (n * sxy - sx * sy) / den
            relacion_codo = (a, (sy - a * sx) / n)
    return limites_servo

def validar_pose(pos, actual=None, ctx='', en_tablero=True):
    """(ok, motivo). Rechaza poses fuera del envolvente o saltos absurdos.
    en_tablero=False para poses que NO son un aterrizaje (home, posturas de
    servicio): esas no tienen por que cumplir la geometria del tablero."""
    if not malla_activa:
        return True, None
    for sid in (1, 2, 3, 4):                 # limite fisico, siempre
        v = pos.get(sid)
        if v is not None and not (0 <= v <= 1000):
            return False, f'{ctx}servo {sid} en {v}, fuera del rango fisico'
    if not en_tablero or not limites_servo:
        return True, None
    for sid, (lo, hi) in limites_servo.items():
        v = pos.get(sid)
        if v is None:
            continue
        if not (lo <= v <= hi):
            return False, (f'{ctx}servo {sid} en {v}, fuera del rango seguro '
                           f'[{int(lo)}, {int(hi)}] que define la calibracion')
    if relacion_codo and pos.get(2) is not None and pos.get(3) is not None:
        a, b = relacion_codo
        esperado = a * pos[2] + b
        if abs(pos[3] - esperado) > tol_relacion:
            return False, (f'{ctx}codo {pos[3]} no corresponde a hombro {pos[2]} '
                           f'(esperado ~{int(esperado)}, desvio {int(abs(pos[3]-esperado))}u). '
                           f'Pose incoherente con el tablero calibrado')
    if actual:
        for sid in (1, 2, 3, 4):
            if pos.get(sid) is None or actual.get(sid) is None:
                continue
            d = abs(pos[sid] - actual[sid])
            if d > salto_max_orden:
                return False, (f'{ctx}salto de {d}u en servo {sid} '
                               f'(maximo {salto_max_orden})')
    return True, None

recalcular_limites()   # envolvente inicial con lo que haya calibrado
if STOCKFISH_OK:
    _ok_n, _det_n = aplicar_nivel(nivel_actual)
    print(f"Nivel de juego: {_det_n if _ok_n else _det_n}")

def _leer_home_asentado(home, timeout=3.0):
    """Sólo lecturas: si llega retrasado, permite asentarse sin reenviar poses."""
    inicio = time.monotonic()
    consecutivas = 0
    while True:
        pos, sospechosos = leer_posiciones_robusta()
        _contar_lecturas(sospechosos)
        dentro = all(pos.get(s) is not None and
                     abs(pos[s]-home[s]) <= VISION_TOL_HOME for s in (1,2,3,4))
        consecutivas = consecutivas + 1 if dentro else 0
        if consecutivas >= 2 or time.monotonic()-inicio >= timeout:
            return pos, consecutivas >= 2
        time.sleep(0.25)


@_excluir_movimientos()
@_suspender_luz_durante_movimiento(home=True)
def mover_a_home(contacto_salida=None):
    _desarmar_traza_servo_idle('mover_a_home explicito')
    # V34/V28: si HOME se pide manualmente durante IDLE con torque libre,
    # recuperar torque DESDE la posición física real antes de mover.
    if not _retomar_torque_para_jugada():
        return {'ok': False, 'error': 'no pude retomar torque para ir a HOME'}
    """Regreso dedicado a HOME con un unico encare desde arriba.

    Flujo V03.8.22:
      posicion actual
        -> despegue seguro
        -> punto 30u ARRIBA de HOME, con la base ya en su destino
        -> UNA sola bajada coordinada al HOME, sin reenviar la base
        -> lectura final

    HOME no usa banda_de(), riel de casillas ni pseudo-hover.
    Tampoco hace ciclos bajar/subir/bajar para corregir: el propio traslado
    termina 30u por arriba y el HOME se encara una sola vez desde ese flanco.
    """
    home = {sid: servo_home.get(sid) for sid in (1, 2, 3, 4)}

    if home.get(4) is not None and home[4] < MUNECA_MIN:
        _bit('brazo', 'HOME bloqueado: muneca por debajo del minimo',
             home=home, minimo=MUNECA_MIN)
        return {'ok': False,
                'error': f'HOME invalido: muneca {home[4]} < minimo {MUNECA_MIN}'}

    ok_v, motivo = validar_pose(home, ctx='HOME: ', en_tablero=False)
    if not ok_v:
        _bit('brazo', 'HOME bloqueado por seguridad', motivo=motivo, home=home)
        return {'ok': False, 'error': f'HOME bloqueado por seguridad: {motivo}'}

    ref, _sr = leer_posiciones_robusta()
    _contar_lecturas(_sr)
    actual, sospechosos = leer_posiciones_robusta(
        referencia=ref, salto_max=SALTO_MAX_ARRANQUE)
    _contar_lecturas(sospechosos)

    faltan = [sid for sid in (1, 2, 3, 4) if actual.get(sid) is None]
    if faltan:
        return {'ok': False,
                'error': f'Sin lectura confiable de servos {faltan}. '
                         f'Tocar "Sincronizar real" y reintentar.',
                'sospechosos': faltan}

    # Solo evitar movimiento si ya esta realmente bien asentado, no simplemente
    # dentro de la tolerancia optica amplia (VISION_TOL_HOME).
    if all(abs(actual[sid] - home[sid]) <= verif_tolerancia
           for sid in (1, 2, 3, 4)):
        _bit('brazo', 'HOME: ya estaba asentado', real=actual, home=home)
        return {'ok': True, 'ya_estaba': True,
                'posicion_real_final': actual,
                'error_final': {sid: actual[sid] - home[sid]
                                for sid in (1, 2, 3, 4)}}

    fv = factor_vel_traslado if factor_vel_traslado > 0 else 1.0
    HOME_ENCARE_U = 30

    # Punto de encare: 30u por arriba de HOME. Hombro sube (-), codo abre (+)
    # con la misma relación vertical del brazo. La fórmula perpendicular daba
    # una muñeca menor que el límite, se clampeaba a 154 y la bajada siguiente
    # la devolvía a 173: una contracción/corrección visible e innecesaria. Como
    # HOME no transporta pieza, la muñeca llega aquí directamente a su valor
    # final y queda inmóvil durante la última bajada.
    h_arriba = max(0, min(1000, home[2] - HOME_ENCARE_U))
    c_arriba = max(0, min(1000, home[3] + int(round(
        HOME_ENCARE_U * RATIO_CODO_BAJADA))))
    m_arriba = max(MUNECA_MIN, min(1000, home[4]))
    encare = {1: home[1], 2: h_arriba, 3: c_arriba, 4: m_arriba}

    _bit('brazo', 'HOME dedicado: inicio', real=actual, home=home,
         encare=encare,
         trayectoria='despegue_seguro->encare_30_arriba->home')

    # 1) DESPEGUE seguro desde la posicion actual.
    esperar_si_pausado('HOME: antes de despegue')
    _sube = DESPEGUE_HOMBRO
    # El brazo ya soltó la pieza: este regreso vacío no debe reutilizar
    # ``despegue_codo`` (200u), que es el gran margen de despeje reservado al
    # transporte CON pieza. Con 60u de hombro ese exceso abría el codo 200u y
    # la perpendicularidad obligaba a contraer la muñeca hasta casi su tope
    # (caso real D6: 418 -> 160 -> 173). Para HOME alcanza la relación vertical
    # del brazo; conserva altura sin fabricar esa contracción.
    _abre = int(round(_sube * RATIO_CODO_BAJADA))
    despegado = dict(actual)
    despegado[2] = max(0, min(1000, actual[2] - _sube))
    despegado[3] = max(0, min(1000, actual[3] + _abre))
    despegado[4] = max(MUNECA_MIN, min(1000,
                        muneca_perp(despegado[2], despegado[3])))

    # En una colocación conocemos la pose calibrada donde se soltó la pieza.
    # Si la lectura real quedó unos ticks atrasada, conservar ciegamente ese
    # error durante la elevación arrastra la pieza hacia atrás. Calculamos sólo
    # la diferencia angular observable y la aplicamos progresivamente; una
    # orden HOME manual, sin pose de contacto, conserva el comportamiento base.
    adelanto_retiro = 0.0
    if contacto_salida and all(contacto_salida.get(s) is not None
                               for s in (2, 3, 4)):
        esperado_real = (contacto_salida[4]
                         + 1.0143*(actual[2] - contacto_salida[2])
                         - 0.9837*(actual[3] - contacto_salida[3]))
        adelanto_retiro = max(0.0, min(8.0, esperado_real - actual[4]))
        _bit('brazo', 'RETIRO POST-SUELTA compensacion adaptativa',
             contacto=contacto_salida, real=actual,
             adelanto_u=round(adelanto_retiro, 2))

    ok_d, motivo_d = validar_pose(despegado, ctx='despegue HOME: ',
                                  en_tablero=False)
    if not ok_d:
        return {'ok': False, 'error': f'Despegue a HOME bloqueado: {motivo_d}'}

    # Una sola línea temporal: despegado y encare son puntos de paso, no
    # finales que frenen todo el brazo. PCHIP conserva cada punto calibrado y
    # sólo lleva a velocidad cero al eje que realmente invierte el sentido.
    factor_retiro_vacio = (float(globals().get('FACTOR_SALIDA_VACIA', 1.0))
                           if contacto_salida else 1.0)
    puntos_retiro = [actual, despegado, encare, home]
    pasos_retiro = [paso_bajada * factor_retiro_vacio,
                    paso_transito * fv * factor_retiro_vacio,
                    paso_bajada * factor_retiro_vacio]
    codo_primero = bool(contacto_salida)
    if codo_primero:
        inicial = dict(actual)
        inicial[3] = actual[3] + RETIRO_CODO_POST_SUELTA_U
        inicial[4] = (actual[4]
                      - 0.9837 * RETIRO_CODO_POST_SUELTA_U)
        # La muñeca sólo compensa el giro del antebrazo; base y hombro quedan
        # inmóviles durante los primeros 40u.
        if (inicial[3] > 1000
                or not MUNECA_MIN <= inicial[4] <= 1000):
            return {'ok': False,
                    'error': 'Retiro codo +40u fuera de límites articulares'}
        ok_i, motivo_i = validar_pose(
            inicial, ctx='retiro codo primero: ', en_tablero=False)
        if not ok_i:
            return {'ok': False, 'error': motivo_i}
        puntos_retiro.insert(1, inicial)
        pasos_retiro.insert(0, PASO_RETIRO_POST_SUELTA)
        _bit('brazo', 'RETIRO POST-SUELTA codo primero 40u',
             real=actual, inicial=inicial, duracion_inicial_ms=600)
        _bit('brazo', 'RETIRO POST-SUELTA velocidad vacia',
             factor=factor_retiro_vacio,
             contacto_final_s=CONTACTO_FINAL_S)
    esperar_si_pausado('HOME: antes de transicion continua')
    if not mover_suave_ruta(
            puntos_retiro, pasos_retiro,
            contexto='regreso completo a HOME', compensar_salida=True,
            adelanto_salida_u=adelanto_retiro,
            salida_codo_primero=codo_primero):
        return {'ok': False,
                'error': 'Movimiento trabado durante transicion continua a HOME'}

    time.sleep(0.20)

    # HOME termina con una lectura diagnóstica. No se persiguen los últimos
    # ticks y no se emite ninguna orden posterior a la curva coordinada.
    _bit('brazo', 'HOME: final sin correcciones físicas V60',
         criterio='margen UART; respaldo canónico de cuatro ArUco',
         tolerancia_uart=VISION_TOL_HOME)

    global ultimo_mov_ts
    ultimo_mov_ts = time.time()

    # Medición final SIN asiento fino. Desde acá no se vuelve a ordenar
    # ningún movimiento hasta que exista una nueva jugada.
    real_final, home_asentado = _leer_home_asentado(home)
    diag_final = {
        sid: (None if real_final.get(sid) is None
              else real_final[sid] - home[sid])
        for sid in (1, 2, 3, 4)
    }
    en_home = home_asentado
    asentado_fino = all(real_final.get(sid) is not None
                        and abs(real_final[sid] - home[sid]) <= verif_tolerancia
                        for sid in (1, 2, 3, 4))

    _bit('brazo', 'HOME dedicado: final', home=home, encare=encare,
         real=real_final, error=diag_final,
         en_home=en_home, asentado_fino=asentado_fino)

    if not en_home:
        return {'ok': False,
                'error': 'Llego a HOME pero quedo fuera del margen UART',
                'validar_home_canonico': True,
                'posicion_real_final': real_final,
                'error_final': diag_final}

    return {'ok': True, 'ya_estaba': False,
            'trayectoria': 'despegue_seguro->encare_30_arriba->home',
            'posicion_real_final': real_final,
            'error_final': diag_final,
            'asentado_fino': asentado_fino}

@_excluir_movimientos()
@_suspender_luz_durante_movimiento()
def mover_con_transito(pos_destino, sq_destino=None, sq_origen=None, altura=None):
    """Transito por RIEL DE POSTURAS coherentes (todas medidas en el brazo real):

    1. DESPEGUE: hombro -DESPEGUE_HOMBRO y codo +despegue_codo COORDINADOS en una
       sola curva. Muñeca por formula. Base quieta.
    2. RIEL: postura de banda del ORIGEN -> intermedias -> postura del DESTINO.
       La base va directamente al destino durante el primer tramo y después
       queda excluida de la bajada.
    3. BAJADA VERTICAL (espejo del despegue): postura de banda -> punto sobre la
       VERTICAL del destino (hombro -margen, codo +bajada_codo) -> aterrizaje al
       CALIBRADO. El ultimo tramo baja hombro Y CIERRA codo juntos = descenso
       vertical real, sin arco del hombro que barra la fila de atras.
    4. Lectura diagnóstica final, sin reentradas ni correcciones físicas.

    SEGURIDAD: lectura robusta al arrancar; muñeca nunca < MUNECA_MIN."""
    if pos_destino.get(4) is not None and pos_destino[4] < MUNECA_MIN:
        print(f"[transito] AVISO: muñeca destino {pos_destino[4]} < {MUNECA_MIN}, "
              f"clampeada a {MUNECA_MIN}")
        pos_destino = dict(pos_destino)
        pos_destino[4] = MUNECA_MIN

    ok_v, motivo = validar_pose(pos_destino, ctx='destino: ',
                                en_tablero=bool(sq_destino))
    if not ok_v:
        print(f"[malla] BLOQUEADO -> {motivo}")
        return {'ok': False, 'error': f'Movimiento bloqueado por seguridad: {motivo}'}
    ref, _sr = leer_posiciones_robusta()
    _contar_lecturas(_sr)
    actual, sospechosos = leer_posiciones_robusta(referencia=ref, salto_max=SALTO_MAX_ARRANQUE)
    _contar_lecturas(sospechosos)

    faltan = [sid for sid in [1, 2, 3, 4] if actual.get(sid) is None]
    if faltan:
        print(f"[transito] ABORTADO: sin lectura confiable de servos {faltan}. "
              f"Usa 'Sincronizar real' y reintenta.")
        return {'ok': False, 'error': f'Sin lectura confiable de servos {faltan}. '
                                      f'Tocar "Sincronizar real" y reintentar.',
                'sospechosos': faltan}
    if sospechosos:
        print(f"[transito] AVISO: lecturas dudosas en servos {sospechosos}, "
              f"se uso la referencia.")

    posturas = {
        'cercana': (traslado_hombro if traslado_hombro is not None else TRASLADO_MEDIA[2],
                    traslado_codo   if traslado_codo   is not None else TRASLADO_MEDIA[3]),
        'media':   (TRASLADO_MEDIA[2], TRASLADO_MEDIA[3]),
        'lejana':  (TRASLADO_LEJANA[2], TRASLADO_LEJANA[3]),
    }
    orden = ['cercana', 'media', 'lejana']
    banda_dest = banda_de(sq_destino)
    h_act = actual[2]
    banda_orig = 'lejana' if h_act >= 750 else ('media' if h_act >= 550 else 'cercana')
    fv = factor_vel_traslado if factor_vel_traslado > 0 else 1.0

    # 1b. PUNTO DE ENTRADA A LA BAJADA (hover): de donde arranca el descenso.
    #     Se calcula ANTES del riel para poder acotarlo: si una postura de
    #     transito esta MAS ABAJO que este punto, el brazo bajaria para despues
    #     volver a subir (zigzag). La postura lejana (hombro 791) esta a la
    #     misma altura que un aterrizaje de fila 8 (793), asi que con el margen
    #     de 180u el brazo subia 15cm y volvia a bajarlos.
    # La ruta grabada usa su primer punto, pero el despegue también necesita
    # un margen definido. Antes esta rama dejaba `margen` sin inicializar y
    # fallaba antes de mover el brazo.
    margen = margen_aterrizaje_lejana if banda_dest == 'lejana' else ATERRIZAJE_HOMBRO
    ruta = rutas_bajada.get(f"{sq_destino}|{altura}") if (sq_destino and altura) else None
    if ruta:
        hover = (ruta[0].get(2, pos_destino[2]), ruta[0].get(3, pos_destino[3]))
    else:
        # cuanto puede subir ESTE escaque sin pasar el tope del codo.
        # En LEJANA y MEDIA: ahi hay piezas altas en la casilla de adelante y
        # 3cm de encare no las libra. En CERCANA no: el brazo esta plegado y
        # subir 9cm es un movimiento de hombro innecesario.
        if codo_max_encare and pos_destino.get(3) is not None:
            _por_codo = int((codo_max_encare - pos_destino[3]) / RATIO_CODO_BAJADA)
            _tope = (margen_max_cercana if banda_dest == 'cercana'
                     else margen_max_encare)
            margen = max(margen, min(_por_codo, _tope))
        # El codo SE DERIVA del margen: para bajar vertical tiene que cerrar
        # RATIO_CODO_BAJADA por cada unidad que baja el hombro. Tenerlos sueltos
        # hacia que en la banda lejana (margen 180, codo 50) la punta se corriera
        # 4.5cm hacia afuera mientras "bajaba".
        # si el despegue ya dejo el brazo MAS ALTO que el encare, se arranca la
        # bajada desde ahi: si no, sube y vuelve a bajar (movimiento de mas).
        clave_bc = (f"{str(sq_destino).upper()}|{altura}"
                    if sq_destino and altura else None)
        bc_banda = bajada_codo_escaque.get(clave_bc)
        if bc_banda is None:
            bc_banda = bajada_codo_banda.get(banda_dest)
        if bc_banda is None:
            bc_banda = int(round(margen * RATIO_CODO_BAJADA))
        fila_encare = (str(sq_destino).upper()[-1]
                       if sq_destino else None)
        encare_hc = (globals().get('ENCARE_HC_FILA', {}) or {}).get(fila_encare)
        if encare_hc is not None:
            margen, bc_banda = (int(encare_hc[0]), int(encare_hc[1]))
        hover = (max(0, pos_destino[2] - margen),
                 max(0, min(1000, pos_destino[3] + bc_banda)))

    clave_encare = (f"{str(sq_destino).upper()}|{altura}"
                     if sq_destino and altura else None)
    _munecas_encare = globals().get('MUNECA_ENCARE_ESCAQUE', {}) or {}
    muneca_hover = int(_munecas_encare.get(
        clave_encare, muneca_transito(hover[0], hover[1], banda_dest)))
    usar_transicion_continua = bool(
        transito_directo and not ruta and not aterrizaje_directo)

    # 1. DESPEGUE coordinado (una sola curva, sin escalas): sube vertical.
    # HOME ya es una postura de tránsito segura y no contiene ninguna pieza.
    # Aplicarle el despegue de una casilla hacía que el codo pasara, por
    # ejemplo, de ~712 a ~935 antes de volver a cerrarse hacia el encare de
    # D3. Además de ser recorrido inútil, ese extremo compromete el torque.
    # Se omite SOLO si las cuatro lecturas reales confirman HOME; fuera de
    # HOME se conserva intacto el despegue necesario para levantar una pieza.
    sale_de_home = all(
        servo_home.get(sid) is not None
        and abs(actual[sid] - servo_home[sid]) <= VISION_TOL_HOME
        for sid in (1, 2, 3, 4))
    # Fuera de HOME y sin pieza agarrada, el primer despegue y el tránsito
    # pueden ser algo más rápidos. La aproximación y el contacto del siguiente
    # escaque conservan exactamente sus tiempos actuales.
    salida_vacia = bool(
        not sale_de_home
        and not sq_origen
        and not globals().get('electroiman_estado', False))
    factor_salida_vacia = (float(globals().get('FACTOR_SALIDA_VACIA', 1.0))
                           if salida_vacia else 1.0)
    if salida_vacia and factor_salida_vacia != 1.0:
        _bit('brazo', 'SALIDA VACIA acelerada',
             factor=factor_salida_vacia, destino=sq_destino)
    # Si el electroimán ya tomó una pieza del tablero, abrir primero el codo
    # 60u y compensar sólo la muñeca para conservar la orientación del extremo.
    # Base y hombro permanecen inmóviles hasta el despegue general. Esto libra
    # las piezas de la fila posterior también al llevar una capturada a la caja.
    retiro_con_pieza = None
    if not sale_de_home and sq_origen:
        retiro_con_pieza = dict(actual)
        retiro_con_pieza[3] = actual[3] + RETIRO_CODO_CON_PIEZA_U
        retiro_con_pieza[4] = (actual[4]
                               - 0.9837 * RETIRO_CODO_CON_PIEZA_U)
        if (retiro_con_pieza[3] > 1000
                or not MUNECA_MIN <= retiro_con_pieza[4] <= 1000):
            return {'ok': False,
                    'error': ('Retiro con pieza codo '
                              f'+{RETIRO_CODO_CON_PIEZA_U}u fuera de límites articulares')}
        ok_r, motivo_r = validar_pose(
            retiro_con_pieza, ctx='retiro con pieza codo primero: ',
            en_tablero=False)
        if not ok_r:
            return {'ok': False, 'error': motivo_r}
        _bit('brazo',
             f'RETIRO CON PIEZA codo primero {RETIRO_CODO_CON_PIEZA_U}u',
             origen=sq_origen, real=actual, inicial=retiro_con_pieza,
             duracion_inicial_ms=750)
    if sale_de_home:
        despegado = dict(actual)
        _bit('brazo', 'HOME -> encare: despegue de pieza omitido',
             real=actual, destino=sq_destino, hover=hover)
    else:
        esperar_si_pausado("antes de despegue")
        # Sube al menos hasta la ALTURA DEL ENCARE del destino: asi el traslado
        # cruza a altura constante (camino en L) en vez de ir en diagonal pasando
        # bajo por encima de las casillas intermedias. El despegue ya era vertical;
        # esto hace que el tramo del medio tambien lo respete.
        _sube = max(DESPEGUE_HOMBRO, margen)
        _abre = max(despegue_codo, int(round(_sube * RATIO_CODO_BAJADA)))
        # La fila 2 conserva su despeje de salida probado: necesita librar las
        # piezas de la fila 1. Esto permite bajar el resto de las trayectorias
        # sin reintroducir aquel roce local.
        fila_origen = (str(sq_origen).upper()[-1]
                       if sq_origen else None)
        salida_hc = (globals().get('ENCARE_HC_FILA', {}) or {}).get(fila_origen)
        if salida_hc is not None:
            _sube = max(_sube, int(salida_hc[0]))
            _abre = max(_abre, int(salida_hc[1]))
        despegado = dict(actual)
        despegado[2] = max(0, min(1000, actual[2] - _sube))
        despegado[3] = max(0, min(1000, actual[3] + _abre))
        despegado[4] = muneca_transito(
            despegado[2], despegado[3], banda_orig)
        # Despegue y aterrizaje comparten la misma velocidad vertical. El
        # factor de traslado queda reservado al riel entre casillas.
        if not usar_transicion_continua:
            desde_despegue = actual
            if retiro_con_pieza is not None:
                if not mover_suave_a(
                        retiro_con_pieza, step=PASO_RETIRO_CON_PIEZA,
                        hasta=1.0,
                        desde=actual):
                    return {'ok': False,
                            'error': 'Movimiento trabado en retiro inicial con pieza'}
                desde_despegue = retiro_con_pieza
            if not mover_suave_a(
                                 despegado,
                                 step=paso_bajada * factor_salida_vacia,
                                 hasta=1.0,
                                 desde=desde_despegue,
                                 retraso_muneca=retraso_muneca_val):
                return {'ok': False,
                        'error': 'Movimiento trabado durante despegue'}

    # Último destino comandado dentro de esta operación. Los tramos siguientes
    # se encadenan desde esta consigna, no desde una lectura física intermedia:
    # el servo puede ir unos ticks detrás sin que la próxima curva retroceda.
    pose_planificada = dict(despegado)

    # 2. RIEL de posturas: del origen al destino, pasando por las intermedias.
    #    Ninguna parada baja por debajo del hover.
    # La base forma parte de la misma curva suave y recibe su objetivo exacto.
    # V60 elimina el antiguo target+10 seguido de una reentrada directa: eran
    # dos inversiones adicionales y el centrador físico ya absorbe el pequeño
    # error estático residual.
    base_sp = max(0, min(1000, pos_destino[1]))
    i0, i1 = orden.index(banda_orig), orden.index(banda_dest)
    paso = 1 if i1 >= i0 else -1
    riel = [orden[i] for i in range(i0, i1 + paso, paso)]  # incluye origen y destino
    ultimo_h = None
    en_hover = False
    if transito_directo:
        parada = {1: base_sp, 2: hover[0], 3: hover[1],
                  4: muneca_hover}
        if not usar_transicion_continua:
            esperar_si_pausado("transito directo al encare")
            if not mover_suave_a(parada, step=paso_transito * fv, hasta=1.0,
                                 desde=pose_planificada):
                return {'ok': False,
                        'error': 'Movimiento trabado durante tránsito'}
        pose_planificada = dict(parada)
        en_hover = True
        riel = []
    for i, b in enumerate(riel):
        bh, bc = posturas[b]
        if bh > hover[0]:            # esa postura queda MAS ABAJO que el hover
            bh, bc = hover           # -> usar el hover (pose completa, coherente)
        if ultimo_h is not None and bh == ultimo_h:
            continue                 # parada repetida: no tiene sentido repetirla
        ultimo_h = bh
        en_hover = (bh, bc) == tuple(hover)
        parada = {1: base_sp, 2: bh, 3: bc,
                  4: (muneca_hover if en_hover
                      else muneca_transito(bh, bc, b))}
        esperar_si_pausado(f"riel: postura {b}")
        # la ULTIMA parada del riel es la llegada: se hace mas suave para
        # que el brazo no quede oscilando (vale tambien para el regreso a home)
        ultima = (i == len(riel) - 1)
        _paso = paso_bajada if ultima else (0.03 if i == 0 else 0.04)
        _paso *= factor_salida_vacia
        if not mover_suave_a(parada, step=_paso * fv,
                             desde=pose_planificada,
                             hasta=1.0):
            return {'ok': False,
                    'error': f'Movimiento trabado en riel {b}'}
        pose_planificada = dict(parada)

    # 3a. RUTA GRABADA A MANO: si el escaque tiene una, se repite tal cual.
    if ruta:
        esperar_si_pausado("antes de ruta grabada")
        for i_p, paso in enumerate(ruta):
            if i_p == 0 and en_hover and all(
                    pose_planificada.get(sid) == paso.get(sid)
                    for sid in (2, 3, 4)):
                continue           # el riel ya lo dejo en el primer tramo
            # La base NO: quedó asentada arriba. Se conserva la ruta grabada.
            if not _mover_directo(
                    paso, (2, 3, 4), int(ruta_ms),
                    f'ruta {sq_destino or "sin_escaque"} {i_p+1}/{len(ruta)}'):
                return {'ok': False,
                        'error': 'Fallo enviando una ruta grabada'}
            esperar_si_pausado(f"ruta tramo {i_p+1}/{len(ruta)}")
        ms_cierre = _ms_aterrizaje(ruta[-1], pos_destino)
        sids_at = (2, 3, 4) if base_solo_arriba else (1, 2, 3, 4)
        if not _mover_directo(
                pos_destino, sids_at, ms_cierre,
                f'cierre ruta {sq_destino or "sin_escaque"}'):
            return {'ok': False,
                    'error': 'Fallo enviando el cierre de una ruta grabada'}
        for sid in smooth:
            try:
                smooth[sid].x = 1.0
            except Exception:
                pass
    else:
        # 3. BAJADA VERTICAL (espejo del despegue). El punto intermedio es el DESTINO
        #    desplazado por una vertical REAL de este brazo: hombro -margen (mas
        #    arriba) y codo +bajada_codo (mas abierto). El ultimo tramo baja el hombro
        #    Y CIERRA el codo a la vez -> la punta desciende vertical, sin el arco
        #    hacia atras que trababa la campana en la arandela de la fila siguiente.
        medio = dict(pos_destino)   # base EXACTA del destino
        medio[2], medio[3] = hover  # mismo punto que acoto el riel
        medio[4] = muneca_hover
        if banda_dest == 'cercana':
            vel_muneca_tramo = vel_muneca_bajada_cercana
        elif banda_dest == 'media':
            vel_muneca_tramo = vel_muneca_bajada_media
        else:
            # La banda lejana conserva su ajuste histórico independiente.
            vel_muneca_tramo = vel_muneca_bajada
        retr_baj = (1.0 / vel_muneca_tramo) if vel_muneca_tramo > 0 else 1.0
        if usar_transicion_continua:
            # Desde HOME son dos tramos; transportando una pieza son tres.
            # Hover/despegado permanecen como geometría de seguridad, pero no
            # reinician el perfil ni detienen los cuatro ejes.
            puntos_continuos = [dict(actual)]
            pasos_continuos = []
            if retiro_con_pieza is not None:
                puntos_continuos.append(dict(retiro_con_pieza))
                pasos_continuos.append(PASO_RETIRO_CON_PIEZA)
            if not sale_de_home:
                puntos_continuos.append(dict(despegado))
                pasos_continuos.append(
                    paso_bajada * factor_salida_vacia)
            puntos_continuos.append(dict(medio))
            pasos_continuos.append(
                paso_transito * fv * factor_salida_vacia)

            # El aterrizaje sigue exactamente la recta medio->destino, pero
            # reserva un segundo para el contacto sin comprimir la aproximación.
            # Conserva los puntos calibrados; la bajada dura algo más.
            precontacto = dict(pos_destino)
            for sid in (2, 3, 4):
                precontacto[sid] = (
                    medio[sid] + FRACCION_PRECONTACTO
                    * (pos_destino[sid] - medio[sid]))
            muestras_bajada = max(2, int(math.ceil(1.0 / paso_bajada)))
            muestras_pre = max(1, int(math.ceil(
                muestras_bajada * FRACCION_TIEMPO_PRECONTACTO)))
            muestras_contacto = max(
                1, int(math.ceil(CONTACTO_FINAL_S / 0.050)))
            puntos_continuos.append(precontacto)
            pasos_continuos.append(1.0 / muestras_pre)
            puntos_continuos.append(dict(pos_destino))
            pasos_continuos.append(1.0 / muestras_contacto)
            esperar_si_pausado("antes de transicion continua")
            if not mover_suave_ruta(
                    puntos_continuos, pasos_continuos,
                    compensar_salida=not sale_de_home,
                    compensar_llegada=True,
                    salida_codo_primero=(retiro_con_pieza is not None),
                    contexto=(f'transicion completa '
                              f'{sq_origen or "?"}->{sq_destino or "?"}')):
                return {'ok': False,
                        'error': (getattr(globals().get('_error_trayectoria'),
                                          'detalle', None) or
                                  'Movimiento interrumpido durante transición continua')}
        else:
            if not en_hover:        # si el riel ya lo dejo ahi, no repetir
                esperar_si_pausado("antes de bajada intermedia")
                medio_mov = dict(medio)
                if base_solo_arriba:
                    medio_mov[1] = None
                # Todo el descenso conserva el mismo perfil vertical; la velocidad
                # de traslado no debe acelerar ni frenar una aproximacion.
                if not mover_suave_a(medio_mov, step=paso_bajada, hasta=1.0,
                                     retraso_muneca=retr_baj,
                                     desde=pose_planificada):
                    return {'ok': False,
                            'error': 'Movimiento trabado durante bajada intermedia'}
                pose_planificada = dict(medio)

            esperar_si_pausado("antes de aterrizaje")
        if usar_transicion_continua:
            pass
        elif aterrizaje_directo:
            # UNA orden por servo: el servo interpola internamente y no hay zona
            # muerta. El tiempo sale del RECORRIDO -> misma velocidad en todas
            # las bandas (con tiempo fijo, la lejana bajaba 5x mas rapido).
            ms_at = _ms_aterrizaje(medio, pos_destino)
            sids_at = (2, 3, 4) if base_solo_arriba else (1, 2, 3, 4)
            if not _mover_directo(
                    pos_destino, sids_at, ms_at,
                    f'aterrizaje directo {sq_destino or "sin_escaque"}'):
                return {'ok': False,
                        'error': 'Fallo enviando el aterrizaje directo'}
            for sid in smooth:                      # dejar el suavizador sincronizado
                try:
                    smooth[sid].x = 1.0
                except Exception:
                    pass
        else:
            # llegada final suave: paso_bajada manda para que el brazo no
            # quede oscilando al frenar (antes: 0.033 fijo)
            destino_bajada = dict(pos_destino)
            if base_solo_arriba:
                destino_bajada[1] = None
            if not mover_suave_a(destino_bajada, step=paso_bajada,
                                 retraso_muneca=retr_baj,
                                 # El tramo anterior acaba de dejar 2/3/4 en
                                 # este encare. No releer el UART entre ambos:
                                 # una pérdida transitoria de la muñeca dejaba
                                 # el brazo detenido arriba aun cuando el servo
                                 # seguía sano y contestaba inmediatamente luego.
                                 desde=medio):
                return {'ok': False,
                        'error': 'Movimiento trabado durante aterrizaje'}

    # 4. DIAGNÓSTICO ÚNICO: se lee una vez y no se vuelve a mover ningún eje.
    # Las antiguas verificaciones hacían hasta dos ciclos de sobrepaso y retorno
    # en hombro/codo/muñeca. Además de duplicar la llegada, esos pulsos eran los
    # "tirones" observados en la caja negra. La tolerancia queda sólo informativa.
    global ultimo_mov_ts
    ultimo_mov_ts = time.time()

    real_final, sospe_final = leer_posiciones_robusta()
    _contar_lecturas(sospe_final)
    err_aterrizaje = {
        sid: real_final[sid] - pos_destino[sid]
        for sid in (1, 2, 3, 4)
        if real_final.get(sid) is not None and pos_destino.get(sid) is not None
    }
    if err_aterrizaje:
        peor = max(err_aterrizaje.items(), key=lambda kv: abs(kv[1]))
        print(f"[aterrizaje] error por servo {err_aterrizaje} | peor: servo {peor[0]} "
              f"{peor[1]:+d}u")
    diag_final = {
        sid: (None if real_final.get(sid) is None or pos_destino.get(sid) is None
              else real_final[sid] - pos_destino[sid])
        for sid in (1,2,3,4)
    }
    _bit('brazo', 'posicion real final',
         destino={sid: pos_destino.get(sid) for sid in (1,2,3,4)},
         real={sid: real_final.get(sid) for sid in (1,2,3,4)},
         error=diag_final)

    # La carga y la altura producen errores estáticos variables en hombro,
    # codo y muñeca, y el centrador físico absorbe el pequeño descentramiento
    # residual de la base. La diferencia se conserva como diagnóstico, pero no
    # provoca otra orden ni veta el electroimán. Sólo se exige poder leer los 4.
    faltan_final = [sid for sid, error in diag_final.items()
                    if error is None or sid in sospe_final]
    if faltan_final:
        return {'ok': False, 'error': 'lectura física final incompleta',
                'servos_sin_confirmar': faltan_final,
                'posicion_real_final': real_final, 'error_final': diag_final}
    return {'ok': True,
            'error_aterrizaje': err_aterrizaje,
            'posicion_real_final': real_final,
            'error_final': diag_final}



def _serializar_partida(funcion):
    """Evita que dos confirmaciones o Acomodar cambien referencias a la vez."""
    from functools import wraps

    @wraps(funcion)
    def ejecutar(*args, **kwargs):
        with _lock_partida:
            return funcion(*args, **kwargs)
    return ejecutar


# ── BROKIE CIERRE — POPUP AMBIENTAL MANUAL (15 s) ─────────
AMBIENTE_POPUP_MOTIVO = 'confirmando_cambio_luz'
_ambiente_episodio = None


def _ambiente_fisico_actual():
    """Testigo físico vigente; el análisis de imagen no representa lux."""
    with _gy302_lock:
        gy = dict(_gy302_estado)
    ts = gy.get('lectura_ts')
    vigente = ts is not None and 0 <= time.monotonic() - ts <= 5
    disponible = (_luz_token() is not None and not gy.get('suspendida')
                  and vigente and gy.get('lux') is not None and not gy.get('error'))
    return dict(disponible=bool(disponible), pendiente=bool(disponible and gy.get('pendiente')),
                lux=gy.get('lux'), error=gy.get('error') or 'lectura GY-302 vencida o ausente')


def _ambiente_estado_elegible():
    """Sólo la escena masiva normal; nunca recuperación ilegal ni otros estados."""
    if vision is None:
        return False, 'sin vision'
    if fin_manual or tablero.is_game_over():
        return False, 'partida terminada'
    if ilegal_pendiente:
        return False, 'ilegal pendiente'
    if jugada_pendiente:
        return False, 'jugada pendiente'
    if jugada_brokie_manual:
        return False, 'colocacion manual pendiente'
    if getattr(vision, '_pausada', False):
        return False, 'vision pausada'

    gy = _ambiente_fisico_actual()
    if not gy['disponible']:
        return False, 'GY-302 no disponible'
    if not gy['pendiente']:
        return False, 'sin cambio confirmado por GY-302'
    if time.time() < estabilizando_hasta:
        return False, 'vision no disponible todavía'
    return True, {'origen': 'GY-302', 'lux': gy['lux']}


@app.route('/vision/ambiente/pausar', methods=['POST'])
@_serializar_partida
def vision_ambiente_pausar():
    global _ambiente_episodio
    if (vision is not None and vision._pausada
            and vision._motivo_pausa == AMBIENTE_POPUP_MOTIVO
            and not (ilegal_pendiente or jugada_pendiente or jugada_brokie_manual)):
        return jsonify({'ok': True, 'pausada': True,
                        'motivo': AMBIENTE_POPUP_MOTIVO, 'fen': tablero.fen(),
                        'episodio': _ambiente_episodio})
    ok, det = _ambiente_estado_elegible()
    if not ok:
        return jsonify({'ok': False, 'error': 'escena ya no elegible',
                        'detalle': det, 'fen': tablero.fen()}), 409
    fen_antes = tablero.fen()
    _ambiente_episodio = uuid.uuid4().hex
    vision.pausar(True, AMBIENTE_POPUP_MOTIVO)
    _bit('vision', 'POPUP AMBIENTAL: pausa confirmada',
         detalle=det, fen=fen_antes)
    return jsonify({'ok': True, 'pausada': True,
                    'motivo': AMBIENTE_POPUP_MOTIVO,
                    'episodio': _ambiente_episodio, 'fen': fen_antes})


@app.route('/vision/ambiente/cancelar', methods=['POST'])
@_serializar_partida
def vision_ambiente_cancelar():
    global _ambiente_episodio
    if vision is None:
        return jsonify({'ok': False, 'error': 'sin vision'}), 503
    if getattr(vision, '_motivo_pausa', None) != AMBIENTE_POPUP_MOTIVO:
        return jsonify({'ok': False, 'error': 'no hay pausa ambiental activa',
                        'fen': tablero.fen()}), 409
    data = request.get_json(silent=True) or {}
    if not _ambiente_episodio or data.get('episodio') != _ambiente_episodio:
        return jsonify({'ok': False, 'error': 'el aviso de luz cambió; actualizá la pantalla'}), 409
    fen_antes = tablero.fen()
    _ambiente_episodio = None
    vision.pausar(False)
    try:
        if hasattr(vision, 'resolver_cambio_luz'):
            vision.resolver_cambio_luz(False)
    except Exception as e:
        _bit('vision', 'no pude liberar estado ambiental cancelado',
             error=str(e)[:160])
    with _gy302_lock:
        _gy302_estado['pendiente'] = False
        _gy302_estado['cambio_ts'] = None
    _bit('vision', 'POPUP AMBIENTAL: cancelado sin cambiar referencia',
         fen=fen_antes)
    return jsonify({'ok': True, 'pausada': False,
                    'referencia_cambiada': False, 'fen': fen_antes})


@app.route('/vision/ambiente/confirmar', methods=['POST'])
@_serializar_partida
def vision_ambiente_confirmar():
    global falla_vision, _firma_notificada_40, _ambiente_episodio
    if vision is None:
        return jsonify({'ok': False, 'error': 'sin vision'}), 503
    if getattr(vision, '_motivo_pausa', None) != AMBIENTE_POPUP_MOTIVO:
        return jsonify({'ok': False, 'error': 'no hay pausa ambiental activa',
                        'fen': tablero.fen()}), 409
    if ilegal_pendiente or jugada_pendiente or jugada_brokie_manual:
        return jsonify({'ok': False,
                        'error': 'hay una operación prioritaria; no cambio referencia',
                        'fen': tablero.fen()}), 409

    data = request.get_json(silent=True) or {}
    if not _ambiente_episodio or data.get('episodio') != _ambiente_episodio:
        return jsonify({'ok': False, 'error': 'el aviso de luz cambió; actualizá la pantalla'}), 409
    if data.get('tablero_restaurado') is not True:
        return jsonify({'ok': False,
                        'error': 'Confirmá que las piezas coinciden con el tablero en pantalla',
                        'referencia_nueva': False}), 409
    with _gy302_lock:
        if _gy302_estado['pendiente'] and (
                _gy302_estado['error'] or not _gy302_estado.get('estable')):
            return jsonify({'ok': False, 'error': 'Esperá que la luz esté estable',
                            'pausada': True}), 409
    fen_antes = tablero.fen()
    # El usuario confirmó explícitamente que volvió al tablero mostrado.
    # Una firma ausente nunca se interpreta como ausencia de jugada.
    ok, det = vision.tomar_referencia(estable=True)
    if not ok:
        _bit('vision',
             'POPUP AMBIENTAL: confirmacion rechazada; referencia no estable',
             detalle=det, fen=fen_antes)
        return jsonify({'ok': False,
                        'error': 'no pude fijar una referencia estable',
                        'detalle': det, 'pausada': True,
                        'fen': fen_antes}), 409

    try:
        if hasattr(vision, 'resolver_cambio_luz'):
            vision.resolver_cambio_luz(True)
    except Exception as e:
        _bit('vision', 'no pude liberar estado ambiental confirmado',
             error=str(e)[:160])
    _fijar_ancla_vision_desde_tablero()
    falla_vision = None
    _firma_notificada_40 = None
    vision._cambio_luz_casillas = []
    _ambiente_episodio = None
    vision.pausar(False)
    with _gy302_lock:
        _gy302_estado['referencia'] = _gy302_estado['lux']
        _gy302_estado['pendiente'] = False
        _gy302_estado['cambio_ts'] = None
    fen_despues = tablero.fen()
    _bit('vision',
         'POPUP AMBIENTAL: referencia nueva confirmada; FEN intacto',
         fen_antes=fen_antes, fen_despues=fen_despues, detalle=det)
    return jsonify({'ok': True, 'referencia_nueva': True,
                    'fen': fen_despues,
                    'fen_intacto': (fen_antes == fen_despues)})


_AMBIENTE_POPUP_JS = r"""
<style id="brokie-ambiente-css">
#brokieAmbienteModal{display:none;position:fixed;z-index:99999;inset:0;background:rgba(0,0,0,.72);align-items:center;justify-content:center;padding:18px;box-sizing:border-box}
#brokieAmbienteCaja{width:min(560px,96vw);background:#171717;color:#fff;border:2px solid #d7a928;border-radius:16px;padding:22px;box-shadow:0 10px 40px rgba(0,0,0,.55);font-family:Arial,sans-serif;text-align:center}
#brokieAmbienteCaja h2{margin:0 0 12px;font-size:28px}
#brokieAmbienteCaja p{font-size:20px;line-height:1.35;margin:10px 0}
#brokieAmbienteCaja .detalle{font-size:15px;opacity:.78;min-height:20px}
#brokieAmbienteCaja .acciones{display:flex;gap:12px;justify-content:center;margin-top:18px;flex-wrap:wrap}
#brokieAmbienteCaja button{font-size:20px;padding:12px 18px;border-radius:10px;border:0;cursor:pointer}
#brokieAmbienteConfirmar{background:#d7a928;color:#111;font-weight:bold}
#brokieAmbienteCancelar{background:#555;color:#fff}
</style>
<div id="brokieAmbienteModal">
  <div id="brokieAmbienteCaja">
    <h2>Se detectó un cambio de luz</h2>
    <p>Si moviste una pieza, devolvela a la posición que muestra el tablero en pantalla.</p>
    <p>Comprobá que todas las piezas coincidan con la pantalla. Retirá la mano y confirmá.</p>
    <div class="detalle" id="brokieAmbienteDetalle"></div>
    <div class="acciones">
      <button id="brokieAmbienteConfirmar">Las piezas coinciden: confirmar</button>
      <button id="brokieAmbienteCancelar">Cancelar</button>
    </div>
  </div>
</div>
<script id="brokie-ambiente-js">
(function(){
  const ESPERA_MS=15000, POLL_MS=1000;
  let episodio=null, desde=null, modalActivo=false, episodioConsumido=false, ocupadaPeticion=false;
  const modal=document.getElementById('brokieAmbienteModal');
  const detalle=document.getElementById('brokieAmbienteDetalle');
  const bOk=document.getElementById('brokieAmbienteConfirmar');
  const bCancel=document.getElementById('brokieAmbienteCancelar');

  function detalleElegible(x){
    x=String(x||'').trim().toLowerCase();
    return /^\d+\s+casillas\s+tapadas$/.test(x) ||
           /^estabilizando\s+luz\s+\d+\/\d+$/.test(x);
  }
  function elegible(d){
    const cam=d&&d.camara||{};
    const gy=d&&d.ambiente_gy302||{};
    const porGy=!!gy.pendiente;
    if(!porGy || gy.error) return false;
    if(d.ilegal_pendiente||d.aviso_ilegal||d.jugada_pendiente||d.jugada_brokie_manual||d.acomodando) return false;
    if(d.fin||(d.partida&&d.partida.fin)) return false;
    return true;
  }
  function ocultar(){modal.style.display='none';modalActivo=false;}

  async function abrirSeguro(camDetalle){
    if(modalActivo||ocupadaPeticion||episodioConsumido) return;
    ocupadaPeticion=true;
    try{
      const r=await fetch('/vision/ambiente/pausar',{method:'POST',headers:{'Content-Type':'application/json'},body:'{}'});
      const d=await r.json();
      if(!r.ok||!d.ok){desde=null;return;}
      episodio=d.episodio;episodioConsumido=true;modalActivo=true;
      detalle.textContent=camDetalle?('Estado: '+camDetalle):'';
      modal.style.display='flex';
    }catch(e){desde=null;}
    finally{ocupadaPeticion=false;}
  }

  async function confirmar(){
    if(ocupadaPeticion)return;
    ocupadaPeticion=true;bOk.disabled=true;bCancel.disabled=true;
    detalle.textContent='Tomando referencia estable...';
    try{
      const r=await fetch('/vision/ambiente/confirmar',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({episodio,tablero_restaurado:true})});
      const d=await r.json();
      if(r.ok&&d.ok){
        detalle.textContent='Referencia actualizada. Continuando...';
        setTimeout(()=>{ocultar();desde=null;},450);
      }else{
        detalle.textContent=d.error||'No pude fijar una referencia estable. Probá nuevamente.';
      }
    }catch(e){detalle.textContent='Error de conexión. La visión sigue pausada.';}
    finally{bOk.disabled=false;bCancel.disabled=false;ocupadaPeticion=false;}
  }

  async function cancelar(){
    if(ocupadaPeticion)return;
    ocupadaPeticion=true;bOk.disabled=true;bCancel.disabled=true;
    try{
      const r=await fetch('/vision/ambiente/cancelar',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({episodio})});
      const d=await r.json();
      if(r.ok&&d.ok){ocultar();desde=null;}
      else detalle.textContent=d.error||'La pausa sigue activa.';
    }catch(e){detalle.textContent='Sin conexión. La pausa sigue activa.';}
    finally{bOk.disabled=false;bCancel.disabled=false;ocupadaPeticion=false;}
  }

  bOk.addEventListener('click',confirmar);
  bCancel.addEventListener('click',cancelar);

  async function poll(){
    /* Aunque el modal esté abierto seguimos leyendo /estado: otra pantalla
       puede haber resuelto el episodio. Sin esta lectura el cartel web queda
       huérfano y sus botones sólo reciben 409. */
    if(ocupadaPeticion)return;
    try{
      const r=await fetch('/estado',{cache:'no-store'});
      const d=await r.json();

      const camAhora=d&&d.camara||{};
      const gyAhora=d&&d.ambiente_gy302||{};
      const backendActivo=!!gyAhora.pendiente ||
        camAhora.motivo_pausa==='confirmando_cambio_luz';
      if(modalActivo && (!backendActivo || gyAhora.episodio!==episodio)){
        ocultar();
        desde=null;
        episodioConsumido=false;
        return;
      }
      if(modalActivo)return;

      if(d.ilegal_pendiente||d.aviso_ilegal){
        desde=null;episodioConsumido=false;return;
      }

      if(d.ambiente_gy302 && d.ambiente_gy302.pendiente){
        if(elegible(d)) await abrirSeguro('Cambio detectado por GY-302');
        return;
      }
      episodioConsumido=false;
      desde=null;
    }catch(e){desde=null;}
  }

  setInterval(poll,POLL_MS);
  setTimeout(poll,1200);
})();
</script>
"""


# ── RUTAS ─────────────────────────────────────────────────

@app.route('/')
def index():
    html = render_template('index.html',
        tablero=tablero,
        turno='Blancas' if tablero.turn == chess.WHITE else 'Negras',
        historial=list(tablero.move_stack))
    # BROKIE CIERRE: popup ambiental aislado; no modifica index.html.
    if '</body>' in html:
        html = html.replace('</body>', _AMBIENTE_POPUP_JS + '\n</body>', 1)
    else:
        html += _AMBIENTE_POPUP_JS
    return html

@app.route('/estado')
def estado():
    global aviso_ilegal

    if ilegal_pendiente:
        _comprobar_restauracion_ilegal()

    # Sólo estado cacheado: /estado se consulta cada segundo desde el touch y
    # nunca debe provocar lecturas UART/I2C. Estos campos faltaban en la
    # respuesta, por lo que el filtro del touch interpretaba ``undefined``
    # como "brazo no estable" y descartaba todos los avisos ambientales.
    with _gy302_lock:
        ambiente_gy302 = dict(_gy302_estado, episodio=_ambiente_episodio)
        movimiento_brazo_en_curso = bool(_luz_movimientos)
        brazo_en_home = bool(_luz_home)
        home_pendiente = bool(
            SERVOS_OK and not _luz_home and not _luz_movimientos)
        brazo_home_estable = bool(
            _luz_home and not _luz_movimientos
            and time.monotonic() >= _mediciones_bloqueadas_hasta)

    return jsonify({
        'fen': tablero.fen(),
        'turno': 'Blancas' if tablero.turn == chess.WHITE else 'Negras',
        'jaque': tablero.is_check(),
        'fin': tablero.is_game_over(),
        'stockfish': STOCKFISH_OK,
        'servos': SERVOS_OK,
        'electroiman': electroiman_estado,
        'partida': estado_partida(),
        'falla_vision': falla_vision,
        'aviso_ilegal': aviso_ilegal,
        'ilegal_pendiente': ilegal_pendiente,
        'desfase_tablero': desfase_tablero,
        'jugada_pendiente': jugada_pendiente,
        'jugada_brokie_manual': jugada_brokie_manual,
        'modo_prueba_sin_brazo': MODO_PRUEBA_SIN_BRAZO,
        'juego_sin_brazo': not vision_con_brazo,
        'brazo_activo': False if MODO_PRUEBA_SIN_BRAZO else vision_con_brazo,
        'movimiento_brazo_en_curso': movimiento_brazo_en_curso,
        'brazo_en_home': brazo_en_home,
        'home_pendiente': home_pendiente,
        'brazo_home_estable': brazo_home_estable,
        'recuperar_home': _fallo_retorno_home,
        'estabilizando': max(0, round(estabilizando_hasta - time.time(), 1)),
        'acomodando': (vision._motivo_pausa == 'acomodando') if vision else False,
        'ambiente_gy302': ambiente_gy302,
        'camara': ({'estado': vision.estado_ciclo, 'detalle': vision.estado_detalle,
                    'motivo_pausa': getattr(vision, '_motivo_pausa', None),
                    'cambio_luz_pendiente': bool(
                        getattr(vision, '_cambio_luz_pendiente', False)),
                    'cambio_luz_detalle': getattr(
                        vision, '_cambio_luz_detalle', None),
                    'cambio_luz_ts': getattr(vision, '_cambio_luz_ts', None)}
                   if vision is not None else None)
    })

def _em(on):
    """Enciende/apaga el electroiman."""
    global electroiman_estado
    electroiman_estado = bool(on)
    if GPIO_OK:
        try:
            electroiman.on() if on else electroiman.off()
        except Exception:
            pass

def _punto_base_fisico(sq, altura):
    """Devuelve exclusivamente la calibracion manual o la tabla generada."""
    sq = str(sq).upper()
    if sq in calibracion_puntos and altura in calibracion_puntos[sq]:
        return dict(calibracion_puntos[sq][altura]), 'punto'
    if sq in tabla_escaques and altura in tabla_escaques[sq]:
        return dict(tabla_escaques[sq][altura]), 'tabla'
    return None, None


def _pos_escaque(sq, altura):
    """Punto de juego rotado al tablero fisico, desde calibracion manual."""
    pos, _origen = _punto_base_fisico(sq_fisico(sq), altura)
    return pos

def _altura_de(sq_uci):
    """peon o rey segun la pieza que hay en ese escaque del tablero logico."""
    try:
        p = tablero.piece_at(chess.parse_square(sq_uci.lower()))
        if p:
            return ALTURA_PIEZA.get(p.symbol().lower(), 'rey')
    except Exception:
        pass
    return 'rey'

def _subir(pos, mm):
    """Misma pose pero mm mas arriba (vertical real de este brazo)."""
    dh = mm * U_HOMBRO_POR_MM
    h = int(max(0, min(1000, pos[2] - dh)))
    c = int(max(0, min(1000, pos[3] + dh * RATIO_CODO_BAJADA)))
    return {1: pos[1], 2: h, 3: c, 4: muneca_perp(h, c)}

def _tomar_y_dejar(sq_o, alt, destino_pos, sq_d=None, nota=''):
    """Levanta la pieza de sq_o y la deja en destino_pos. (ok, error)."""
    p = _pos_escaque(sq_o, alt)
    if not p:
        return False, f'{sq_o} no tiene altura {alt} calibrada'
    _em(False)
    r = mover_con_transito(p, sq_destino=sq_fisico(sq_o), altura=alt)
    if not r.get('ok'):
        return False, f'yendo a {sq_o}: {r.get("error")}'
    _em(True)
    time.sleep(iman_espera_s)
    r = mover_con_transito(destino_pos,
                           sq_destino=sq_fisico(sq_d) if sq_d else None,
                           sq_origen=sq_fisico(sq_o),
                           altura=alt if sq_d else None)
    if not r.get('ok'):
        _em(False)
        return False, f'llevando la pieza: {r.get("error")}'
    time.sleep(0.2)
    _em(False)
    time.sleep(iman_soltar_s)
    return True, None


def _retornar_home_tras_colocar(pasos, contacto_salida=None):
    """La pieza ya fue colocada: un fallo de retorno no permite repetirla."""
    global _fallo_retorno_home
    try:
        resultado = (mover_a_home(contacto_salida=contacto_salida)
                     if contacto_salida is not None else mover_a_home())
    except Exception as exc:
        resultado = {'ok': False, 'error': str(exc)}
    if resultado.get('ok'):
        pasos.append('vuelve a home')
        return
    _fallo_retorno_home = resultado.get('error') or 'HOME no confirmado'
    pasos.append('PIEZA COLOCADA; retorno a HOME fallido: ' + _fallo_retorno_home)
    _bit('brazo', 'PIEZA COLOCADA; requiere recuperar HOME, NO repetir jugada',
         error=_fallo_retorno_home)
    if vision is not None:
        vision.pausar(True, 'recuperar_home')


@_suspender_luz_durante_movimiento()
def _preparar_torque_fisico():
    """Punto común para cámara, confirmación manual y reintentos."""
    if _ajuste_home_activo():
        _bit('brazo', 'jugada bloqueada durante ajuste manual de HOME')
        return False
    _desarmar_traza_servo_idle('comienza ejecucion fisica')
    return _retomar_torque_para_jugada()


def _informar_fallo_fisico(fn):
    from functools import wraps
    @wraps(fn)
    def ejecutar(*args, **kwargs):
        try:
            resultado = fn(*args, **kwargs)
        except Exception as exc:
            resultado = (False, str(exc))
        if not resultado[0]:
            _em(False)
            _bit('brazo', 'ejecucion detenida; requiere intervencion',
                 detalle=str(resultado[1]))
            if vision is not None:
                vision.pausar(True, 'fallo_brazo')
                vision.estado_ciclo = 'brazo detenido'
                vision.estado_detalle = str(resultado[1])
        return resultado
    return ejecutar


@_excluir_movimientos('tupla')
@_informar_fallo_fisico
def ejecutar_enroque(uci):
    """Enroque completo: rey Y torre.

    Por defecto son dos movimientos normales, primero el rey y despues la
    torre: sus casillas de destino estan libres, asi que no se cruzan.
    Con enroque_por_afuera=True, la torre sale antes a un punto fuera del
    tablero (por si alguna trayectoria roza en la practica).
    """
    if uci not in TORRE_ENROQUE:
        return False, f'{uci} no es un enroque'
    if transito_pausado or globals().get('_fallo_retorno_home'):
        return False, 'Brazo pausado o pendiente de recuperar HOME'
    if not _preparar_torque_fisico():
        return False, 'No pude retomar torque desde referencia real'
    t_o, t_d = TORRE_ENROQUE[uci]

    if not enroque_por_afuera:
        # camino simple: rey y despues torre, cada uno como jugada normal
        ok, det = ejecutar_jugada_fisica(uci[:2], uci[2:4])
        if not ok:
            return False, f'moviendo el rey: {det}'
        ok2, det2 = ejecutar_jugada_fisica(t_o, t_d)
        if not ok2:
            return False, f'moviendo la torre: {det2}'
        return True, [f'rey {uci[:2]} -> {uci[2:4]}', f'torre {t_o} -> {t_d}']

    if punto_espera is None:
        return False, ('falta el punto de espera fuera del tablero '
                       '(POST /espera/grabar con el brazo puesto ahi)')
    r_o, r_d = uci[:2], uci[2:4]
    alt_r = _altura_de(r_o)
    alt_t = _altura_de(t_o)
    pasos = []

    if vision is not None:
        vision.pausar(True, 'enroque')
    try:
        ok, err = _tomar_y_dejar(t_o, alt_t, dict(punto_espera))
        if not ok:
            return False, f'sacando la torre: {err}'
        pasos.append(f'torre {t_o} -> afuera')

        p_rd = _pos_escaque(r_d, alt_r)
        if not p_rd:
            return False, f'{r_d} no tiene altura {alt_r} calibrada'
        ok, err = _tomar_y_dejar(r_o, alt_r, p_rd, sq_d=r_d)
        if not ok:
            return False, f'moviendo el rey: {err}'
        pasos.append(f'rey {r_o} -> {r_d}')

        p_td = _pos_escaque(t_d, alt_t)
        if not p_td:
            return False, f'{t_d} no tiene altura {alt_t} calibrada'
        # la torre esta en el punto de espera: ir, tomarla y llevarla
        _em(False)
        r = mover_con_transito(dict(punto_espera))
        if not r.get('ok'):
            return False, f'volviendo por la torre: {r.get("error")}'
        _em(True)
        time.sleep(iman_espera_s)
        r = mover_con_transito(p_td, sq_destino=sq_fisico(t_d), altura=alt_t)
        if not r.get('ok'):
            _em(False)
            return False, f'llevando la torre a {t_d}: {r.get("error")}'
        time.sleep(0.2)
        _em(False)
        time.sleep(iman_soltar_s)
        pasos.append(f'torre -> {t_d}')

        if volver_a_home:
            _retornar_home_tras_colocar(pasos, contacto_salida=p_td)
        return True, pasos
    finally:
        _em(False)
        if vision is not None and not globals().get('_fallo_retorno_home'):
            vision.pausar(False)


TOPE_JUGADA_S = 120      # una jugada normal tarda ~27s; una con captura, ~55.
                         # Si pasa de esto, algo se trabo: se avisa fuerte en la
                         # bitacora para que quede registro de cuando y donde.
_jugada_en_curso = None


def _vigilar_jugada(t_ini, etiqueta):
    """Avisa en la bitacora si una jugada se pasa del tope. No la interrumpe
    -cortar el brazo a mitad seria peor- pero deja constancia del momento
    exacto, que es lo que hace falta para diagnosticar un cuelgue."""
    global _jugada_en_curso
    _jugada_en_curso = (t_ini, etiqueta)

    def _mirar():
        time.sleep(TOPE_JUGADA_S)
        actual = _jugada_en_curso
        if actual and actual[0] == t_ini:
            _bit('brazo', f'ATENCION: la jugada {etiqueta} lleva mas de '
                          f'{TOPE_JUGADA_S}s sin terminar',
                 candado_tomado=_lock_partida._is_owned())
    threading.Thread(target=_mirar, daemon=True).start()


@_excluir_movimientos('tupla')
@_informar_fallo_fisico
def ejecutar_jugada_fisica(origen, destino, captura_en=None):
    """Mueve la pieza con el brazo. captura_en = escaque de la pieza comida
    (se retira ANTES). Devuelve (ok, detalle).

    La camara va en la muñeca y mira desde home: mientras el brazo se mueve
    veria su propio recorrido. Se pausa al entrar y se REANUDA SIEMPRE, aunque
    la jugada falle o salte una excepcion: si quedara pausada, la vigilancia
    no vuelve a detectar nada nunca mas.
    """
    if globals().get('_fallo_retorno_home'):
        return False, 'Recuperar HOME; revisar la colocación antes de otra jugada'
    if not SERVOS_OK:
        return False, 'Servos no conectados'
    if transito_pausado:
        # Sin esto, el movimiento entra al bucle de espera de esperar_si_pausado
        # y se cuelga PARA SIEMPRE con el candado de la partida tomado: la
        # interfaz entera deja de responder.
        _bit('brazo', 'jugada rechazada: el transito esta PAUSADO')
        return False, ('El transito esta pausado (boton Parar). '
                       'Reanudalo para que BROKIE vuelva a moverse.')
    if not _preparar_torque_fisico():
        return False, 'No pude retomar torque desde referencia real'
    if vision is not None:
        vision.pausar(True, 'brazo')
    pasos = []
    _bit('brazo', f'jugada fisica {origen}->{destino}', captura=captura_en)
    _t_ini = time.time()
    _vigilar_jugada(_t_ini, f'{origen}->{destino}')
    try:
        def _llevar_a_captura(sq, alt):
            """Levanta la pieza de sq y la suelta sobre la caja de descarte."""
            if punto_captura is None:
                return False, 'No hay punto de captura grabado (/captura/grabar)'
            p = _pos_escaque(sq, alt)
            if not p:
                return False, f'{sq} no tiene altura {alt} calibrada'
            _em(False)
            r = mover_con_transito(p, sq_destino=sq_fisico(sq), altura=alt)
            if not r.get('ok'):
                return False, f'yendo a {sq}: {r.get("error")}'
            _em(True)
            time.sleep(iman_espera_s)
            pasos.append(f'tomo {sq} ({alt})')
            arriba = _subir(punto_captura, captura_altura_mm)
            r = mover_con_transito(
                arriba, sq_origen=sq_fisico(sq), altura=alt)
            if not r.get('ok'):
                return False, f'yendo a la caja: {r.get("error")}'
            _em(False)
            time.sleep(max(0.45, iman_soltar_s))
            pasos.append('soltada en la caja')
            return True, None

        # 1. retirar la pieza capturada, si la hay
        if captura_en:
            ok, err = _llevar_a_captura(captura_en, _altura_de(captura_en))
            if not ok:
                _bit('brazo', f'FALLO retirar la pieza capturada: {err}')
                return False, f'captura: {err}'

        # 2. mover la pieza propia
        alt = _altura_de(origen)
        p_o = _pos_escaque(origen, alt)
        p_d = _pos_escaque(destino, alt)
        if not p_o or not p_d:
            falta = origen if not p_o else destino
            _bit('brazo', f'FALTA CALIBRACION: {falta} en altura {alt}')
            return False, f'falta calibracion: {falta} en {alt}'
        _em(False)
        r = mover_con_transito(p_o, sq_destino=sq_fisico(origen), altura=alt)
        if not r.get('ok'):
            _bit('brazo', f'no pudo ir a {origen}', error=r.get('error'))
            return False, f'yendo a {origen}: {r.get("error")}'
        _em(True)
        time.sleep(iman_espera_s)
        pasos.append(f'tomo {origen} ({alt})')
        r = mover_con_transito(p_d, sq_destino=sq_fisico(destino),
                               sq_origen=sq_fisico(origen), altura=alt)
        if not r.get('ok'):
            _bit('brazo', f'no pudo ir a {destino}', error=r.get('error'))
            return False, f'yendo a {destino}: {r.get("error")}'
        time.sleep(0.2)
        _em(False)
        time.sleep(iman_soltar_s)
        pasos.append(f'soltada en {destino}')

        # 3. replegarse
        if volver_a_home:
            _retornar_home_tras_colocar(pasos, contacto_salida=p_d)
        else:
            try:
                mover_con_transito(_subir(p_d, 35))
            except Exception:
                pass
        _bit('brazo', ('pieza colocada; HOME pendiente'
                      if globals().get('_fallo_retorno_home') else 'jugada COMPLETA'),
             pasos=pasos,
             segundos=round(time.time() - _t_ini, 1))
        return True, pasos
    except Exception as e:
        _bit('brazo', f'EXCEPCION en la jugada: {e}', hechos=pasos)
        return False, f'excepcion: {e}'
    finally:
        global _jugada_en_curso
        _jugada_en_curso = None
        _em(False)                      # el iman NUNCA queda encendido
        if vision is not None:
            # NO se reanuda aca: el brazo acaba de frenar y sigue vibrando.
            # Si la camara volviera a mirar ahora, veria medio tablero corrido
            # y lo tomaria por una mano encima. Se reanuda recien cuando la
            # referencia nueva quedo fijada, tras la espera de estabilizacion.
            if not vision.vigilando and not globals().get('_fallo_retorno_home'):
                vision.pausar(False)


def _cerrar_partida():
    """Al terminar: se apaga la camara y el brazo.

    Si siguiera mirando, cualquier pieza que se acomode al guardar se tomaria
    por una jugada y BROKIE intentaria responder a una partida terminada.
    """
    global vision_activa
    try:
        if vision is not None and vision.vigilando:
            vision.detener_vigilancia()
            vision_activa = False
            _bit('partida', 'partida terminada: apago la camara')
        _em(False)
    except Exception as e:
        _bit('partida', 'no pude cerrar la partida', error=str(e))


def estado_partida():
    """Jaque, mate, tablas y finales manuales."""
    if fin_manual:
        return dict(fin_manual)
    fin = tablero.is_game_over()
    est = {'jaque': tablero.is_check(),
           'fin': fin,
           'turno': 'blancas' if tablero.turn == chess.WHITE else 'negras'}
    if not fin:
        est['aviso'] = 'JAQUE' if est['jaque'] else None
        return est
    if tablero.is_checkmate():
        gana = 'negras' if tablero.turn == chess.WHITE else 'blancas'
        est['resultado'] = 'jaque mate'
        est['gana'] = gana
        est['aviso'] = f'JAQUE MATE - ganan las {gana}'
    elif tablero.is_stalemate():
        est['resultado'] = 'ahogado'
        est['aviso'] = 'TABLAS por rey ahogado'
    elif tablero.is_insufficient_material():
        est['resultado'] = 'material insuficiente'
        est['aviso'] = 'TABLAS por material insuficiente'
    elif tablero.is_fivefold_repetition():
        est['resultado'] = 'repeticion'
        est['aviso'] = 'TABLAS por repeticion'
    elif tablero.is_seventyfive_moves():
        est['resultado'] = '75 movidas'
        est['aviso'] = 'TABLAS por la regla de 75 movidas'
    else:
        est['resultado'] = 'terminada'
        est['aviso'] = 'PARTIDA TERMINADA'
    return est


# Candado de la partida. La camara vigila en su PROPIO HILO y puede empujar
# una jugada justo mientras el jugador toca la pantalla: los dos escribirian
# sobre el mismo tablero y sobre el mismo brazo. Todo lo que cambia el estado
# de la partida o mueve el brazo pasa por aca.
_epoca_partida = 0
_lock_partida = threading.RLock()
if vision is not None:
    vision._lock_estado = _lock_partida
    vision._leer_ambiente_fisico = _ambiente_fisico_actual


def _nueva_sesion_partida():
    global _ancla_vision_fisica, _ambiente_episodio, vision_activa, _epoca_partida
    _epoca_partida += 1
    _ancla_vision_fisica = None
    _ambiente_episodio = None
    vision_activa = False
    for nombre, valor in {
        '_ultima_candidata_vision': None, '_ultima_candidata_ts': 0.0,
        '_firma_notificada_40': None, '_desfase_previo': None,
        '_g472_huerfana_sq': None, '_g472_huerfana_n': 0,
        '_g472_huerfana_ts': 0.0, 'estabilizando_hasta': 0.0,
    }.items():
        globals()[nombre] = valor
    partida_id = bitacora.nueva_partida() if bitacora else f'epoca-{_epoca_partida}'
    if vision is not None:
        rotar = getattr(vision, 'iniciar_auditoria_partida', None)
        if callable(rotar):
            try:
                rotar(partida_id)
            except Exception as exc:
                # La auditoría nunca debe impedir iniciar una partida.
                _bit('vision', 'AUDITORIA FOTOS: no pude rotar',
                     error=str(exc)[:200])


def _bloqueo_jugada_humana():
    """Guardas comunes a touch, endpoint de diagnóstico y callback."""
    if fin_manual or tablero.is_game_over():
        return 'La partida terminó'
    if jugada_brokie_manual:
        return 'primero colocá la jugada de BROKIE'
    if jugada_pendiente:
        return 'hay una jugada de BROKIE pendiente'
    if ilegal_pendiente:
        return 'primero restaurá la jugada inválida'
    if vision is not None and getattr(vision, '_pausada', False):
        return 'primero resolvé la pausa del tablero'
    if time.time() < estabilizando_hasta:
        return 'esperá que termine la estabilización'
    return None


def _aplicar_jugada_humana(movimiento, fuente):
    """Único commit humano. Llamar bajo _lock_partida tras validar evidencia."""
    proveedor = getattr(vision, '_leer_ambiente_fisico', None)
    if fuente != 'touch' and proveedor is not None:
        ambiente = proveedor()
        if not ambiente['disponible'] or ambiente['pendiente']:
            raise ValueError('resolvé el estado del GY-302 antes de aceptar la jugada visual')
    bloqueo = _bloqueo_jugada_humana()
    if bloqueo:
        raise ValueError(bloqueo)
    if movimiento not in tablero.legal_moves:
        raise ValueError('la jugada ya no es legal')
    fen_pre = tablero.fen()
    tablero.push(movimiento)
    _limpiar_falla()
    _limpiar_aviso_ilegal()
    globals()['_firma_notificada_40'] = None
    _fijar_ancla_vision_desde_tablero()
    _bit('partida', 'jugada humana aplicada', jugada=movimiento.uci(),
         fuente=fuente, fen_pre=fen_pre, fen_post=tablero.fen())


def _ocupadas_fisicas():
    """Escaques FISICOS que la partida dice que tienen pieza."""
    return [sq_fisico(chess.square_name(s)) for s in chess.SQUARES
            if tablero.piece_at(s)]



def _uci_logico_desde_fisico(mv_f):
    """Físico -> lógico; sq_fisico es involución con rotación 180."""
    m = str(mv_f or '').lower()
    if len(m) < 4:
        return None
    try:
        return (sq_fisico(m[:2]).lower() +
                sq_fisico(m[2:4]).lower() + m[4:])
    except Exception:
        return None


def _armar_ilegal_pendiente(det):
    global ilegal_pendiente, aviso_ilegal, falla_vision

    mv_f = ((det or {}).get('movimiento_fisico')
            or (det or {}).get('movimiento_fisico_detectado'))
    camb = list((det or {}).get('cambiadas') or [])
    mv_l = _uci_logico_desde_fisico(mv_f)
    origen = str(mv_f or '')[:2].upper() if mv_f else None
    destino = str(mv_f or '')[2:4].upper() if mv_f else None

    casillas_visibles = camb or [x for x in (origen, destino) if x]
    es_enroque_fisico = bool((det or {}).get('enroque_fisico'))

    # BROKIE 4.0G.4.6 — una ilegal con movimiento fisico conocido debe
    # demostrar retorno tanto del ORIGEN como del DESTINO.
    #
    # Antes, si la firma final conservaba solamente el destino, `camb`
    # ocultaba el origen y la recuperacion podia aceptar con la pieza
    # simplemente retirada del destino.
    #
    # Si una rama ya entrega `casillas_recuperacion` explicitas (por ejemplo
    # el fallback amplio 4.0G.4.5 cuando el origen realmente es desconocido),
    # se respetan exactamente.
    _foco_explicito = (det or {}).get('casillas_recuperacion')

    if _foco_explicito:
        casillas_recuperacion = list(_foco_explicito)
    else:
        casillas_recuperacion = sorted({
            str(x).upper()
            for x in (
                list(camb)
                + [x for x in (origen, destino) if x]
            )
            if len(str(x)) == 2
        })

    ilegal_pendiente = {
        'hora': time.strftime('%H:%M:%S'),
        'movimiento_fisico': mv_f,
        'movimiento_logico': mv_l,
        'origen_fisico': origen,
        'destino_fisico': destino,
        'casillas': casillas_visibles,
        'casillas_recuperacion': casillas_recuperacion,
        'motivo': (det or {}).get('motivo') or 'jugada ilegal',
        'fen_pre': tablero.fen(),
    }
    aviso_ilegal = {
        'activo': True,
        'titulo': 'JUGADA INVALIDA',
        'mensaje': ('DEVUELVA REY Y TORRE A SU POSICION'
                    if es_enroque_fisico else
                    'DEVUELVA LA PIEZA A SU POSICION'),
        'movimiento': (mv_l or mv_f or '').upper(),
        'movimiento_fisico': (mv_f or '').upper(),
        'cambiadas': ilegal_pendiente['casillas'],
        'motivo': ilegal_pendiente['motivo'],
        'hora': ilegal_pendiente['hora'],
    }
    falla_vision = {
        'ilegal': True,
        'requiere_restauracion': True,
        'cambiadas': ilegal_pendiente['casillas'],
        'motivo': ilegal_pendiente['motivo'],
        'movimiento': mv_l or mv_f,
        'hora': ilegal_pendiente['hora'],
    }
    try:
        if vision is not None and hasattr(vision, 'brokie40g3_iniciar_recuperacion_ilegal'):
            vision.brokie40g3_iniciar_recuperacion_ilegal(
                ilegal_pendiente.get('casillas_recuperacion')
                or ilegal_pendiente['casillas'])
    except Exception as e:
        _bit('vision', 'fallo activando recuperación ilegal 4.0G.3',
             error=str(e)[:160])

    _diag_vision('ILEGAL_PENDIENTE',
                 movimiento_fisico=mv_f, movimiento_logico=mv_l,
                 cambiadas=ilegal_pendiente['casillas'])
    _bit('partida', 'JUGADA INVALIDA: espero restauracion al PRE',
         movimiento_fisico=mv_f, movimiento_logico=mv_l,
         fen_pre=tablero.fen())


@_serializar_partida
def _comprobar_restauracion_ilegal():
    """ÚNICA salida automática de ILEGAL_PENDIENTE en 4.0G.3."""
    global ilegal_pendiente, aviso_ilegal, falla_vision, _firma_notificada_40

    if not ilegal_pendiente or vision is None:
        return False

    # Primero manda la máquina temporal de vision.py. No lanzamos V11
    # mientras haya mano, pieza en movimiento o menos de 3 PRE consecutivos.
    if hasattr(vision, 'brokie40g3_estado_recuperacion_ilegal'):
        try:
            er = vision.brokie40g3_estado_recuperacion_ilegal()
        except Exception:
            er = {}
        if aviso_ilegal is not None:
            aviso_ilegal['recuperacion'] = er
        if not er.get('lista_v11'):
            return False

    if not hasattr(vision, 'brokie40g3_verificar_restauracion'):
        return False

    try:
        r = vision.brokie40g3_verificar_restauracion(
            ilegal_pendiente.get('casillas_recuperacion')
            or ilegal_pendiente.get('casillas')
            or [])
    except Exception as e:
        _bit('vision', 'fallo comprobando restauracion ilegal',
             error=str(e)[:160])
        return False

    if aviso_ilegal is not None:
        aviso_ilegal['pendientes'] = r.get('pendientes')
        aviso_ilegal['v11'] = {
            'restaurado': bool(r.get('restaurado')),
            'geo_ms': r.get('geo_ms'),
        }

    if not r.get('restaurado'):
        # V11 no confirmó. Reiniciar el consenso temporal para no martillar
        # el verificador en cada polling del táctil.
        try:
            vision.brokie40g3_iniciar_recuperacion_ilegal(
                ilegal_pendiente.get('casillas_recuperacion')
                or ilegal_pendiente.get('casillas')
                or [])
        except Exception:
            pass
        return False

    _bit('partida', 'RESTAURACION ILEGAL CONFIRMADA; continuo',
         movimiento=ilegal_pendiente.get('movimiento_logico'),
         geo_ms=r.get('geo_ms'))

    try:
        if hasattr(vision, 'brokie40g3_finalizar_recuperacion_ilegal'):
            vision.brokie40g3_finalizar_recuperacion_ilegal()
    except Exception:
        pass

    ilegal_pendiente = None
    aviso_ilegal = None
    falla_vision = None
    _firma_notificada_40 = None
    return True



def _limpiar_falla():
    global falla_vision
    falla_vision = None


def _limpiar_aviso_ilegal():
    global aviso_ilegal
    aviso_ilegal = None





@app.route('/vision/ilegal/cancelar', methods=['POST'])
@_serializar_partida
def vision_ilegal_cancelar():
    """Escape seguro de ILEGAL: descarta el expediente sin aceptar jugada.

    NO cambia FEN, turno ni referencia PRE. Se usa desde SALIR y como paso
    previo a ACOMODAR, para que una recuperación ilegal nunca sea una cárcel.
    """
    global aviso_ilegal, ilegal_pendiente, falla_vision, _firma_notificada_40

    if not ilegal_pendiente and not aviso_ilegal:
        return jsonify({'ok': True, 'ya_limpia': True, 'fen': tablero.fen()})

    fen_antes = tablero.fen()
    anterior = ilegal_pendiente

    try:
        if vision is not None and hasattr(vision, 'brokie40g3_finalizar_recuperacion_ilegal'):
            vision.brokie40g3_finalizar_recuperacion_ilegal()
    except Exception as e:
        _bit('vision', 'ESCAPE ILEGAL: fallo limpiando maquina temporal',
             error=str(e)[:160])

    ilegal_pendiente = None
    aviso_ilegal = None
    falla_vision = None
    _firma_notificada_40 = None

    _bit('vision', 'ESCAPE recuperacion ILEGAL: expediente cancelado; FEN/PRE intactos',
         anterior=anterior, fen=fen_antes)

    return jsonify({
        'ok': True,
        'fen': tablero.fen(),
        'fen_intacto': (fen_antes == tablero.fen()),
        'referencia_cambiada': False,
        'detalle': 'recuperacion ilegal cancelada; FEN, turno y PRE intactos',
    })


@app.route('/vision/ilegal/continuar', methods=['POST'])
@_serializar_partida
def vision_ilegal_continuar():
    """Fallback YA CORREGÍ: no cambia FEN; exige mano fuera + escena estable."""
    global aviso_ilegal, ilegal_pendiente, falla_vision, _firma_notificada_40

    if vision is None:
        return jsonify({'ok': False, 'error': 'vision.py no disponible'}), 503
    if not ilegal_pendiente:
        return jsonify({'ok': False, 'error': 'no hay ilegal pendiente'}), 409

    with _lock_partida:
        try:
            if hasattr(vision, 'en_pose') and not vision.en_pose():
                return jsonify({'ok': False,
                                'error': 'BROKIE todavía no está en HOME'}), 409
        except Exception:
            pass

        # El botón NO acepta una foto instantánea. Primero comprobamos
        # varias capturas estables y que la mano haya salido.
        if hasattr(vision, 'brokie40g3_preparar_ya_corregi'):
            chk = vision.brokie40g3_preparar_ya_corregi()
            if not chk.get('ok'):
                _bit('vision', 'YA CORREGI rechazado',
                     detalle=chk)
                return jsonify({'ok': False,
                                'error': chk.get('motivo'),
                                'detalle': chk}), 409
        else:
            chk = {'ok': True, 'motivo': 'sin verificador 4.0G.3'}

        vision.pausar(True, motivo='recuperacion manual ilegal')
        try:
            # El usuario confirma conscientemente que el tablero físico ya
            # corresponde al MISMO FEN pre-ilegal. Se resincroniza imagen,
            # jamás se hace push ni se cambia turno.
            ok, det = vision.tomar_referencia(estable=True)
            if not ok:
                return jsonify({'ok': False,
                                'error': 'no pude fijar una referencia estable',
                                'detalle': det}), 409

            _fijar_ancla_vision_desde_tablero()

            try:
                if hasattr(vision, 'brokie40g3_finalizar_recuperacion_ilegal'):
                    vision.brokie40g3_finalizar_recuperacion_ilegal()
            except Exception:
                pass

            ilegal_pendiente = None
            aviso_ilegal = None
            falla_vision = None
            _firma_notificada_40 = None

            _bit('vision',
                 'YA CORREGI aceptado: FEN intacto + referencia resincronizada',
                 fen=tablero.fen(), chequeo=chk)
            return jsonify({'ok': True,
                            'fen': tablero.fen(),
                            'detalle': 'referencia resincronizada; FEN intacto'})
        finally:
            vision.pausar(False)



def _verificar_tablero_real():
    """Lee el tablero completo y lo compara con la partida.

    Es la DOBLE VERIFICACION: el diferencial ya dedujo y aplico la jugada;
    esto confirma, con metodos independientes, que lo que hay sobre la madera
    es de verdad lo que la app cree. Si no coincide se avisa en el acto, en
    vez de arrastrar el desfase durante toda la partida.
    """
    global desfase_tablero
    if vision is None or not vision.listo():
        return
    if not getattr(vision, 'USAR_ABSOLUTOS', False):
        return          # con un solo metodo no hay con que verificar
    try:
        r, err = vision.consenso(_ocupadas_fisicas())
        if r is None:
            return
        if r.get('coincide'):
            globals()['_desfase_previo'] = None
            if desfase_tablero:
                _bit('vision', 'el tablero volvio a coincidir')
            desfase_tablero = None
            return
        # una casilla dudosa suelta no es un desfase: se avisa solo si hay
        # diferencias claras en las dos direcciones o mas de una
        sobran, faltan = r.get('sobran', []), r.get('faltan', [])
        if len(sobran) + len(faltan) == 0:
            return
        # Un solo desacuerdo NO alcanza para alarmar: los metodos absolutos
        # fallan de a ratos en las casillas de bajo contraste y saltaba el
        # cartel en cada jugada. Se exige que el MISMO desacuerdo aparezca dos
        # veces seguidas antes de molestar al jugador.
        global _desfase_previo
        firma = (tuple(sobran), tuple(faltan))
        if firma != _desfase_previo:
            _desfase_previo = firma
            _bit('vision', 'posible desfase, lo confirmo en la proxima',
                 sobran=sobran, faltan=faltan)
            return
        desfase_tablero = {'sobran': sobran, 'faltan': faltan,
                           'dudosas': r.get('discrepan', []),
                           'hora': time.strftime('%H:%M:%S')}
        _bit('vision', 'EL TABLERO NO COINCIDE con la partida (confirmado)',
             sobran=sobran, faltan=faltan)
    except Exception as e:
        _bit('vision', 'no se pudo verificar el tablero', error=str(e))


def _token_estado_visual():
    return (_epoca_partida, tablero.fen(), _ambiente_episodio,
            getattr(vision, '_referencia_id', None))



@_serializar_partida
def _refrescar_vision(motivo=''):
    """Nueva foto base, EN SEGUNDO PLANO.

    Se llama desde adentro del candado de la partida. Si se hiciera aca
    mismo, el candado quedaria tomado varios segundos -espera al brazo,
    reintentos, timeout de la camara- y la pantalla no responderia a nada
    mientras tanto: se ve igual que un congelamiento.
    """
    if globals().get('_fallo_retorno_home'):
        return
    if vision is None or not vision.vigilando:
        return
    vision.pausar(True, 'refrescando_referencia')
    threading.Thread(target=_refrescar_vision_ahora,
                     args=(motivo, _token_estado_visual()), daemon=True).start()



def _telemetria_pasiva_home(duracion_s, intervalo_s=0.50, fase='estabilizacion',
                            cancelar_si_movimiento=False,
                            generacion_movimiento=None):
    """SOLO LECTURA de la posición física real de servos 1/2/3/4.

    La observación posterior a una referencia se cancela al detectar una orden
    de movimiento. El candado ambiental cubre cada lote completo de cuatro
    lecturas: un movimiento comienza antes del lote o después de él, nunca
    entre las órdenes UART de dos articulaciones.
    """
    if not SERVOS_OK:
        time.sleep(max(0.0, float(duracion_s)))
        return
    duracion_s = max(0.0, float(duracion_s))
    intervalo_s = max(0.20, float(intervalo_s))
    t0 = time.time()
    primera = None
    anterior = None
    muestra = 0
    cancelada_por_movimiento = False
    if cancelar_si_movimiento and generacion_movimiento is None:
        with _gy302_lock:
            generacion_movimiento = _luz_generacion
    while True:
        ahora = time.time()
        if ahora - t0 > duracion_s:
            break
        if cancelar_si_movimiento:
            with _gy302_lock:
                if (_luz_movimientos or
                        _luz_generacion != generacion_movimiento):
                    cancelada_por_movimiento = True
                    break
                pos = {}
                for sid in (1,2,3,4):
                    s = servos.get(sid)
                    pos[sid] = (_leer_servo_robusto(s, intentos=2)
                                if s is not None else None)
        else:
            pos = {}
            for sid in (1,2,3,4):
                s = servos.get(sid)
                pos[sid] = (_leer_servo_robusto(s, intentos=2)
                            if s is not None else None)
        muestra += 1
        if primera is None:
            primera = dict(pos)
            anterior = dict(pos)
            _bit('brazo', 'TELEMETRIA HOME inicio', fase=fase, muestra=muestra,
                 desde_home_s=round(ahora-t0,2), posicion=pos,
                 home={sid:servo_home.get(sid) for sid in (1,2,3,4)})
        else:
            da, di, movidos = {}, {}, []
            for sid in (1,2,3,4):
                p, pa, pi = pos.get(sid), anterior.get(sid), primera.get(sid)
                da[sid] = None if p is None or pa is None else p-pa
                di[sid] = None if p is None or pi is None else p-pi
                if da[sid] not in (None,0):
                    movidos.append(sid)
            if movidos or muestra % 4 == 0:
                _bit('brazo',
                     'TELEMETRIA HOME CAMBIO' if movidos else 'TELEMETRIA HOME muestra',
                     fase=fase, muestra=muestra, desde_home_s=round(ahora-t0,2),
                     posicion=pos, delta_anterior=da, delta_inicio=di,
                     servos_movidos=movidos)
            anterior = dict(pos)
        restante = duracion_s - (time.time()-t0)
        if restante <= 0:
            break
        time.sleep(min(intervalo_s, restante))
    final = anterior or primera or {}
    if cancelada_por_movimiento:
        _bit('brazo', 'TELEMETRIA HOME cancelada por movimiento',
             fase=fase, muestras=muestra)
    _bit('brazo', 'TELEMETRIA HOME fin', fase=fase,
         duracion_s=round(time.time()-t0,2), posicion_final=final,
         cancelada_por_movimiento=cancelada_por_movimiento,
         delta_total={sid:(None if primera is None or primera.get(sid) is None
                           or final.get(sid) is None else final[sid]-primera[sid])
                      for sid in (1,2,3,4)})


def _telemetria_pasiva_post_referencia(duracion_s=15.0, intervalo_s=0.50,
                                        generacion_movimiento=None):
    try:
        _telemetria_pasiva_home(duracion_s, intervalo_s,
                                fase='post_referencia_vision_activa',
                                cancelar_si_movimiento=True,
                                generacion_movimiento=generacion_movimiento)
    except Exception as e:
        _bit('brazo', 'TELEMETRIA HOME error post referencia', error=str(e)[:160])


@_serializar_partida
def _refrescar_vision_ahora(motivo='', token=None):
    """Nueva foto base para la camara, despues de que el tablero cambio.

    Sin esto, una jugada hecha a mano (tablero tactil) deja la referencia
    vieja: la camara ve el cambio que produjo esa misma jugada y la detecta
    otra vez. Solo se hace si esta vigilando y el brazo esta en home.
    """
    if token is not None and token != _token_estado_visual():
        return
    if vision is None or not vision.vigilando:
        return
    try:
        # El brazo puede estar todavia llegando a home: la referencia exige
        # que este en pose, asi que se espera un poco y se reintenta. Si igual
        # falla, el propio ciclo de vigilancia la rehace solo.
        # El brazo VIBRA al frenar. Con la camara en la muñeca, una foto
        # tomada antes de que se aquiete queda desde otra posicion y todas
        # las casillas se leen corridas. Mientras dura esta espera la pantalla
        # avisa que no hay que mover todavia.
        global estabilizando_hasta
        estabilizando_hasta = time.time() + espera_home_s
        # Silencio total durante el asentamiento: no cámara, no GY-302 y
        # tampoco la antigua telemetría UART de servos cada 500 ms.
        _bloquear_mediciones_estabilizacion(espera_home_s)
        time.sleep(espera_home_s)
        estabilizando_hasta = 0.0

        # El torque permanece activo durante toda la partida. Liberarlo entre
        # jugadas obligaba a resincronizar y rehabilitar los cuatro servos, y
        # además permitía que HOME cediera mecánicamente. La liberación queda
        # sólo como acción manual explícita desde el panel técnico.

        # V02: mantener la vision PAUSADA mientras se fija la referencia nueva.
        # Antes se reanudaba aca y el hilo de vigilancia podia comparar contra
        # la referencia vieja al mismo tiempo que tomar_referencia() generaba
        # la nueva, produciendo estados como "saca la mano", "confirmando" o
        # "esperando" de forma intermitente.
        for intento in range(6):
            ok, det = vision.tomar_referencia()
            if ok:
                _fijar_ancla_vision_desde_tablero()
                _verificar_tablero_real()      # doble verificacion
                # V03.8.25: desde este punto la vision entra en IDLE. Este flujo
                # NO envia ninguna orden a servos; cualquier movimiento fisico
                # posterior es asentamiento/holding del propio servo o proviene
                # de otra accion explicita, nunca de la recuperacion NO-MOVE.
                _bit('brazo', 'IDLE post-HOME: referencia fijada con torque activo',
                     espera_home_s=espera_home_s,
                     torque_liberado=_torque_liberado_idle,
                     home={sid: servo_home.get(sid) for sid in (1,2,3,4)})
                _armar_traza_servo_idle()
                vision.pausar(False)           # recien ahora vuelve a mirar
                # V33: 15 s adicionales de lectura pasiva ya con visión activa.
                with _gy302_lock:
                    generacion_telemetria = _luz_generacion
                threading.Thread(
                    target=_telemetria_pasiva_post_referencia,
                    args=(15.0, 0.50, generacion_telemetria), daemon=True).start()
                return
            time.sleep(0.5)
        globals()['falla_vision'] = {'motivo': 'no pude fijar referencia; revisá el tablero y usá Acomodar',
                                    'requiere_confirmacion': True}
        vision.pausar(True, 'referencia_fallida')
        print(f"[vision] no se pudo refrescar la referencia {motivo}: {det}"
              f" (el ciclo la va a reintentar solo)")
    except Exception as e:
        globals()['falla_vision'] = {'motivo': 'falló la referencia: '+str(e), 'requiere_confirmacion': True}
        vision.pausar(True, 'referencia_fallida')
        _bit('vision', 'referencia fallida; mantengo pausa', error=str(e))



def _marcar_brokie_para_colocacion_manual(mv, captura=None, enroque=False, promocion=False):
    """Modo prueba: FEN avanza, pero la jugada de BROKIE se hace a mano.

    La referencia PRE/POST NO se renueva hasta que el usuario pulse LISTO.
    Así las casillas movidas por BROKIE no contaminan la siguiente jugada humana.
    """
    global jugada_brokie_manual
    uci = mv.uci()
    jugada_brokie_manual = {
        'jugada': uci,
        'jugada_fisica': _uci_fisico(uci),
        'captura': captura,
        'enroque': bool(enroque),
        'promocion': bool(promocion),
        'hora': time.strftime('%H:%M:%S'),
        'fen_post': tablero.fen(),
    }
    # Guardar la posición ANTERIOR a la respuesta ya aplicada al FEN. El PRE
    # óptico puede seguir siendo el de antes de la jugada humana: para esta
    # comprobación sólo se usa ocupación absoluta de las casillas de la respuesta.
    anterior = tablero.copy(stack=True)
    if anterior.move_stack and anterior.peek() == mv:
        anterior.pop()
        jugada_brokie_manual['fen_pre'] = anterior.fen()
    if vision is not None and getattr(vision, 'vigilando', False):
        try:
            vision.pausar(True, 'esperando movimiento manual BROKIE')
        except Exception:
            pass
    _bit('partida', 'MODO PRUEBA: BROKIE espera colocacion manual',
         jugada=uci, fisica=jugada_brokie_manual['jugada_fisica'],
         fen=tablero.fen())


@_excluir_movimientos()
def _jugar_motor(con_brazo):
    """Pide la jugada al motor y la empuja al tablero.

    Sin brazo, el usuario reproduce la jugada de BROKIE y confirma LISTO antes
    de renovar la referencia. El bloqueo maestro siempre tiene prioridad.
    """
    if MODO_PRUEBA_SIN_BRAZO:
        con_brazo = False
    con_brazo = bool(con_brazo and SERVOS_OK)
    if con_brazo and _fallo_retorno_home:
        return {'ok': False, 'error': 'Recuperar HOME antes de continuar',
                'recuperar_home': True}
    if tablero.is_game_over() or not engine:
        return {'ok': True, 'fin': tablero.is_game_over()}
    mv_sel = elegir_jugada()
    mv = mv_sel
    o, d = mv.uci()[:2], mv.uci()[2:4]
    cap = None
    if tablero.is_capture(mv):
        cap = d if not tablero.is_en_passant(mv) else \
              chess.square_name(chess.square(chess.square_file(mv.to_square),
                                             chess.square_rank(mv.from_square)))
    enroque = tablero.is_castling(mv)
    promo = mv.promotion is not None
    out = {'ok': True}
    if con_brazo and SERVOS_OK:
        # V34/V28: la jugada YA está definida. Antes de cualquier trayectoria,
        # tomar referencia física REAL con torque aún OFF y retomar exactamente ahí.
        # La ejecución física común prepara el torque también cuando se
        # llega desde confirmación manual o Reintentar.
        if enroque:
            ok, det = ejecutar_enroque(mv.uci())
            out['brazo'] = {'ok': ok, 'detalle': det, 'enroque': True}
        else:
            ok, det = ejecutar_jugada_fisica(o, d, captura_en=cap)
            out['brazo'] = {'ok': ok, 'detalle': det, 'captura': cap}
            if enroque:
                out['brazo']['aviso'] = ('ENROQUE: mover la torre a mano '
                                         '(falta grabar el punto de espera)')
        if promo:
            pieza = {chess.QUEEN: 'DAMA', chess.ROOK: 'TORRE',
                     chess.BISHOP: 'ALFIL', chess.KNIGHT: 'CABALLO'}.get(
                         mv.promotion, 'DAMA')
            out['brazo']['aviso'] = (f'BROKIE corono en {d.upper()}: cambia ese '
                                     f'peon por una {pieza}')
            out['brazo']['cambiar_pieza'] = {'escaque': d, 'pieza': pieza}
            _bit('partida', f'BROKIE corono en {d}: hay que poner una {pieza}')
        if not ok:
            # El brazo NO pudo ejecutar: si igual se empujara la jugada, el
            # tablero de la app quedaria un movimiento adelante del de madera
            # y a partir de ahi todo se desincroniza. Se deshace y se avisa.
            _em(False)
            _bit('brazo', 'la jugada del motor NO se ejecuto: no la aplico '
                          'para no desincronizar', jugada=mv.uci(), detalle=det)
            global jugada_pendiente
            jugada_pendiente = {'jugada': mv.uci(), 'motivo': str(det)[:120],
                                'solo_manual': bool(_fallo_retorno_home),
                                'hora': time.strftime('%H:%M:%S')}
            out['ok'] = False
            out['error'] = (f'BROKIE no pudo completar el movimiento: {det}. Toca Reintentar '
                            'cuando el brazo este libre.')
            out['no_aplicada'] = mv.uci()
            return out
    tablero.push(mv)
    _bit('partida', f'BROKIE responde {mv.uci()}',
         captura=cap, enroque=enroque or None, promocion=promo or None)
    out['respuesta_engine'] = mv.uci()
    if con_brazo and _fallo_retorno_home:
        out.update(ok=False, recuperar_home=True, jugada_aplicada=True,
                   error='Pieza colocada. Recuperar HOME; no repetir la jugada.')
    if not con_brazo:
        _marcar_brokie_para_colocacion_manual(
            mv, captura=cap, enroque=enroque, promocion=promo)
        out['requiere_colocacion_manual'] = True
        out['jugada_fisica'] = _uci_fisico(mv.uci())
    out['estado'] = estado_partida()
    out['fin'] = tablero.is_game_over()
    if out['fin']:
        _cerrar_partida()
    elif con_brazo:
        _refrescar_vision('tras jugada del motor')
    return out

def _uci_fisico(uci):
    """Jugada UCI logica -> UCI en escaques FISICOS del tablero calibrado."""
    extra = uci[4:]
    return sq_fisico(uci[:2]).lower() + sq_fisico(uci[2:4]).lower() + extra



def _movimientos_naturales_fisicos():
    """Geometría de la pieza del turno, IGNORANDO legalidad/jaque/bloqueos.

    Se usa sólo como prioridad suave contra una señal débil de sombra.
    Nunca reemplaza la evidencia física ni la detección de ilegales.
    """
    naturales = set()

    def agregar(fr, nf, nr):
        if 0 <= nf < 8 and 0 <= nr < 8:
            to = chess.square(nf, nr)
            u = chess.square_name(fr) + chess.square_name(to)
            naturales.add(_uci_fisico(u)[:4].lower())

    for fr in chess.SQUARES:
        p = tablero.piece_at(fr)
        if p is None or p.color != tablero.turn:
            continue

        f = chess.square_file(fr)
        r = chess.square_rank(fr)

        if p.piece_type == chess.KNIGHT:
            for df, dr in ((1,2),(2,1),(2,-1),(1,-2),
                           (-1,-2),(-2,-1),(-2,1),(-1,2)):
                agregar(fr, f+df, r+dr)

        elif p.piece_type == chess.KING:
            for df in (-1,0,1):
                for dr in (-1,0,1):
                    if df or dr:
                        agregar(fr, f+df, r+dr)
            agregar(fr, f-2, r)
            agregar(fr, f+2, r)

        elif p.piece_type == chess.PAWN:
            dr = 1 if p.color == chess.WHITE else -1
            agregar(fr, f, r+dr)
            agregar(fr, f, r+2*dr)
            agregar(fr, f-1, r+dr)
            agregar(fr, f+1, r+dr)

        else:
            dirs = []
            if p.piece_type in (chess.BISHOP, chess.QUEEN):
                dirs += [(1,1),(1,-1),(-1,1),(-1,-1)]
            if p.piece_type in (chess.ROOK, chess.QUEEN):
                dirs += [(1,0),(-1,0),(0,1),(0,-1)]

            # Rayos completos: deliberadamente ignoramos bloqueos.
            for df, dr in dirs:
                nf, nr = f+df, r+dr
                while 0 <= nf < 8 and 0 <= nr < 8:
                    agregar(fr, nf, nr)
                    nf += df
                    nr += dr

    return sorted(naturales)



def _deducir_con_camara():
    """Pregunta a la camara que jugo el humano, en coordenadas LOGICAS.

    La camara ve escaques FISICOS (la grilla calibrada no se mueve). Si el
    brazo juega negras, el tablero logico esta rotado 180, asi que hay que
    traducir en los dos sentidos: las jugadas legales se pasan a fisico para
    comparar, y la que devuelve se vuelve a logico.
    """
    ancla_evento = {'fen': tablero.fen(),
                    'referencia_id': getattr(vision, '_referencia_id', None)}
    legales = [m.uci() for m in tablero.legal_moves]
    fis = {_uci_fisico(u): u for u in legales}
    ocupadas = [sq_fisico(chess.square_name(sq)).lower()
                for sq in chess.SQUARES if tablero.piece_at(sq)]
    enroques = [f for f, u in fis.items()
                if tablero.is_castling(chess.Move.from_uci(u))]
    color_humano = 'blanca' if tablero.turn == chess.WHITE else 'negra'
    origenes_turno = [sq_fisico(chess.square_name(sq)).lower()
                     for sq, pieza in tablero.piece_map().items()
                     if pieza.color == tablero.turn]
    naturales = _movimientos_naturales_fisicos()
    mv_f, det = vision.deducir_jugada(
        list(fis.keys()),
        ocupadas=ocupadas,
        enroques=enroques,
        color_pieza=color_humano,
        naturales=naturales,
        origenes_turno=origenes_turno)
    det = dict(det) if isinstance(det, dict) else {'detalle': det}
    det['ancla_evento'] = ancla_evento
    det['anclas_turno'] = {'origenes': sorted(origenes_turno),
                           'turno': color_humano,
                           'revisar_extras': True}
    _diag_vision('deduccion',
                 mv_fisica=mv_f,
                 mv_logica=fis.get(mv_f) if mv_f else None,
                 cambiadas=det.get('cambiadas'),
                 motivo=det.get('motivo'),
                 candidatas_fisicas=det.get('candidatas'),
                 origenes_turno=sorted(origenes_turno),
                 ocupadas_fisicas=ocupadas)
    if mv_f is not None and det.get('promocion'):
        # la camara ve el peon en el fondo pero no puede saber en que pieza se
        # convierte: se avisa para que el jugador elija en la pantalla
        candidatos = [u for u in fis.values() if u[:4] == fis.get(mv_f + 'q', '')[:4]]
        base = None
        for f, u in fis.items():
            if f[:4] == mv_f[:4]:
                base = u[:4]
                break
        det['pide_promocion'] = base
        return None, det
    if mv_f is None:
        if det.get('candidatas'):
            # Todas las alternativas comparten coordenadas, incluso ilegales.
            # Antes sólo se traducían las legales y el touch mezclaba tableros.
            candidatas = list(det['candidatas'])
            det['candidatas_fisicas'] = candidatas
            det['candidatas'] = [_uci_fisico(m) for m in candidatas]
            legales_observadas = sorted({fis[m] for m in candidatas if m in fis})
            if (len(legales_observadas) == 1
                    and det.get('estado_40') == 'DUDOSO'
                    and not det.get('ilegal_fisica')):
                # Sugerencia al humano, NUNCA ganador automático.
                det['sugerencia_humana'] = legales_observadas[0]
                det['fen_sugerencia'] = tablero.fen()
        # BROKIE 4.0: una ilegal física se conserva como HECHO OBSERVADO.
        # No se traduce a una jugada legal cercana.
        if det.get('ilegal_fisica'):
            det['movimiento_fisico_detectado'] = det.get('movimiento_fisico')
        return None, det
    det['fisico'] = mv_f
    return fis[mv_f], det


def _fisicas_de_tablero(board):
    """Ocupacion FISICA esperada para un tablero logico dado."""
    return sorted(sq_fisico(chess.square_name(s)).lower()
                  for s in chess.SQUARES if board.piece_at(s))


def _confirmar_enroque_atomico_con_origen_proyectado(det_evento,
                                                       resultado_post,
                                                       foco_post,
                                                       ocupadas_esperadas,
                                                       ocupadas_antes=None):
    """Revisa un origen proyectado del enroque en el perímetro.

    El detector temporal ya exige una firma exacta de cuatro casillas y un
    único enroque legal. Aquí no se deduce ninguna jugada: sólo se permite que
    una de las dos casillas que deben quedar vacías siga pareciendo ocupada por
    la proyección de la pieza vecina. Las otras tres lecturas deben coincidir,
    incluidos los dos destinos ocupados. V43 añade el caso inconcluso con
    cuatro o cinco casillas: dos POST, evidencia local de vacío y vecina
    anclada compatible. No modifica la decisión visual de otras jugadas.
    """
    atomico = (det_evento or {}).get('deteccion_enroque_atomico') or {}
    foco = {str(x).upper() for x in (foco_post or [])}
    firma = {
        str(x).upper()
        for x in (atomico.get('firma_exacta') or [])
    }
    esperadas_atomicas = {
        str(x).upper()
        for x in (atomico.get('esperadas') or [])
    }
    ocupadas = {
        str(x).upper()
        for x in (ocupadas_esperadas or [])
    }

    # V43: revisión contextual de una DUDA, sin modificar el clasificador.
    # El camino histórico de contradicción de cuatro casillas queda intacto.
    if resultado_post.get('inconcluso') and not resultado_post.get('contradiccion'):
        observada = {str(s).upper() for s in atomico.get('firma_observada', [])}
        compatibles = atomico.get('enroques_compatibles') or []
        extras = foco - firma
        if not (atomico.get('aplicado') and len(firma) == 4
                and esperadas_atomicas == firma and firma <= foco
                and observada == foco and len(compatibles) == 1
                and len(firma & ocupadas) == 2):
            return False, {'motivo': 'firma atomica incompleta o ambigua'}
        if extras:
            extra = atomico.get('extra_proyectada') or {}
            if not (len(extras) == 1 and atomico.get('modo') == 'quinta_vecina_sin_aro'
                    and extra.get('casilla') in extras):
                return False, {'motivo': 'extra sin evidencia atomica'}
        elif atomico.get('modo') != 'firma_exacta':
            return False, {'motivo': 'modo atomico incompatible'}
        historial = resultado_post.get('historial') or []
        if len(historial) < 2:
            return False, {'motivo': 'faltan dos capturas POST'}
        previas = {str(s).upper() for s in (ocupadas_antes or [])}
        anclas = (previas & ocupadas) - foco
        origen = None
        vecinas = []
        for lectura in historial[-2:]:
            detalle = lectura.get('detalle') or {}
            dudas = lectura.get('dudosas') or []
            if (lectura.get('contradicciones') or len(dudas) != 1
                    or set(detalle) != foco):
                return False, {'motivo': 'POST con otras alteraciones o incompleto'}
            sq = dudas[0]
            if sq not in (firma & previas) - ocupadas or (origen and origen != sq):
                return False, {'motivo': 'duda fuera del mismo origen'}
            for casilla, datos in detalle.items():
                esperado = 'ocupada' if casilla in ocupadas else 'vacia'
                if (datos.get('esperado') != esperado or
                        datos.get('observado') != ('dudosa' if casilla == sq else esperado)):
                    return False, {'motivo': 'otra transicion no confirmada'}
            local = (lectura.get('clasificacion_local') or {}).get('estados') or {}
            m = local.get(sq) or {}
            aro = m.get('aro_base') or {}
            if not (m.get('banda_paralaje') and aro.get('presente') is False
                    and aro.get('soporte_centros') == 0
                    and 0 <= float(aro.get('gradiente_mediano', 999)) < 15
                    and 0 <= float(aro.get('arco_continuo', 999)) < .35
                    and abs(float(m.get('delta_centro_vacio', 999))) <= 16
                    and abs(float(m.get('delta_borde_vacio', 999))) <= 20):
                return False, {'motivo': 'origen sin evidencia suficiente de vacio'}
            # Una vecina anclada hacia el centro del tablero puede proyectarse
            # hacia este origen periférico. No se presume movimiento de ella.
            x, y = ord(sq[0])-65, int(sq[1])-1
            vecinas = [a for a in sorted(anclas)
                       if max(abs(ord(a[0])-65-x), abs(int(a[1])-1-y)) == 1
                       and (ord(a[0])-65-3.5)**2 + (int(a[1])-1-3.5)**2
                       < (x-3.5)**2 + (y-3.5)**2]
            if not vecinas:
                return False, {'motivo': 'sin vecina anclada compatible'}
            origen = sq
        return True, {'motivo': 'origen dudoso con vacio y ancla en dos POST',
                      'origen_proyectado': origen, 'anclas_compatibles': vecinas,
                      'firma': sorted(firma), 'extras_confirmadas': sorted(extras),
                      'lecturas': 2}

    if not (atomico.get('aplicado') and len(foco) == 4
            and firma == foco and esperadas_atomicas == foco):
        return False, {'motivo': 'firma atomica ausente o distinta'}

    historial = (resultado_post or {}).get('historial') or []
    ultimo = historial[-1] if historial else {}
    contradicciones = {
        str(x).upper()
        for x in (ultimo.get('contradicciones') or [])
    }
    detalle = {
        str(k).upper(): v
        for k, v in (ultimo.get('detalle') or {}).items()
        if isinstance(v, dict)
    }

    if len(contradicciones) != 1 or set(detalle) != foco:
        return False, {
            'motivo': 'POST no tiene una unica contradiccion completa',
            'contradicciones': sorted(contradicciones),
        }

    falsa = next(iter(contradicciones))
    if falsa in ocupadas:
        return False, {
            'motivo': 'la contradiccion esta en un destino ocupado',
            'casilla': falsa,
        }

    for sq in sorted(foco):
        esperado = 'ocupada' if sq in ocupadas else 'vacia'
        observado = str((detalle.get(sq) or {}).get('observado') or '').lower()
        if sq == falsa:
            if esperado != 'vacia' or observado != 'ocupada':
                return False, {'motivo': 'el falso no es un origen proyectado'}
        elif observado != esperado:
            return False, {
                'motivo': 'otra casilla POST no coincide',
                'casilla': sq,
                'esperado': esperado,
                'observado': observado,
            }

    # Un enroque debe dejar exactamente dos destinos ocupados dentro del foco.
    if len(foco & ocupadas) != 2:
        return False, {'motivo': 'destinos ocupados distintos de dos'}

    return True, {
        'motivo': 'firma atomica exacta y tres de cuatro POST coinciden',
        'origen_proyectado': falsa,
        'firma': sorted(firma),
    }


def _confirmar_enroque_con_destino_parcial(det_evento,
                                            resultado_post,
                                            foco_post,
                                            ocupadas_esperadas,
                                            origen_rey_fisico,
                                            destino_rey_fisico):
    """Confirma un enroque completo con un único destino de aro recortado.

    La maniobra ya debe haber sido identificada como el único enroque que
    explica sus cuatro transiciones físicas. El POST tiene que confirmar los
    dos orígenes vacíos y uno de los destinos con aro fuerte. El otro destino
    puede quedar falsamente vacío sólo si conserva simultáneamente textura,
    borde y un fragmento circular. No se usa para ninguna otra jugada.
    """
    foco = {str(x).upper() for x in (foco_post or [])}
    ocupadas = {str(x).upper() for x in (ocupadas_esperadas or [])}
    movimiento_rey = (
        str(origen_rey_fisico).upper() + str(destino_rey_fisico).upper()
    )

    firma_observada = set()
    firma_enroque = set()
    modo = None

    atomico = (det_evento or {}).get('deteccion_enroque_atomico') or {}
    if atomico.get('aplicado'):
        firma_enroque = {
            str(x).upper() for x in (atomico.get('esperadas') or [])
        }
        firma_observada = {
            str(x).upper()
            for x in (atomico.get('firma_observada')
                      or atomico.get('firma_exacta') or [])
        }
        compatibles = {
            str(x)[:4].upper()
            for x in (atomico.get('enroques_compatibles') or [])
        }
        if movimiento_rey in compatibles:
            modo = 'atomico'

    if modo is None:
        completo = (
            (det_evento or {}).get('deteccion_enroque_completo') or {}
        )
        compatibles = completo.get('compatibles_con_firma') or []
        compatibles_mov = [
            x for x in compatibles
            if isinstance(x, dict)
            and str(x.get('movimiento') or '')[:4].upper()
            == movimiento_rey
        ]
        if len(compatibles) == 1 and len(compatibles_mov) == 1:
            firma_enroque = {
                str(x).upper()
                for x in (compatibles_mov[0].get('esperadas') or [])
            }
            firma_observada = {
                str(x).upper() for x in (completo.get('firma') or [])
            }
            modo = 'completo'

    if not (modo and len(foco) == 4 and firma_enroque == foco
            and firma_enroque.issubset(firma_observada)):
        return False, {'motivo': 'sin enroque completo unico para el foco'}

    extras = firma_observada - firma_enroque
    if len(extras) > 1:
        return False, {'motivo': 'firma con mas de una casilla extra'}
    if extras:
        extra = next(iter(extras))
        try:
            adyacente = any(
                max(abs(ord(extra[0]) - ord(sq[0])),
                    abs(int(extra[1]) - int(sq[1]))) == 1
                for sq in (foco & ocupadas)
            )
        except (IndexError, TypeError, ValueError):
            adyacente = False
        if not adyacente:
            return False, {'motivo': 'la casilla extra no es vecina de destino'}

    historial = (resultado_post or {}).get('historial') or []
    ultimo = historial[-1] if historial else {}
    contradicciones = {
        str(x).upper() for x in (ultimo.get('contradicciones') or [])
    }
    detalle = {
        str(k).upper(): v
        for k, v in (ultimo.get('detalle') or {}).items()
        if isinstance(v, dict)
    }
    locales = (
        (ultimo.get('clasificacion_local') or {}).get('estados') or {}
    )
    locales = {str(k).upper(): v for k, v in locales.items()
               if isinstance(v, dict)}

    if len(contradicciones) != 1 or set(detalle) != foco:
        return False, {
            'motivo': 'POST no tiene una unica contradiccion completa',
            'contradicciones': sorted(contradicciones),
        }
    debil = next(iter(contradicciones))
    if debil not in ocupadas:
        return False, {'motivo': 'la contradiccion no es un destino ocupado'}

    for sq in foco:
        esperado = 'ocupada' if sq in ocupadas else 'vacia'
        observado = str((detalle.get(sq) or {}).get('observado') or '').lower()
        if sq == debil:
            if esperado != 'ocupada' or observado not in ('vacia', 'dudosa'):
                return False, {'motivo': 'el destino debil no es falso negativo'}
        elif observado != esperado:
            return False, {
                'motivo': 'otra casilla POST no coincide',
                'casilla': sq,
            }

    if len(foco & ocupadas) != 2:
        return False, {'motivo': 'destinos ocupados distintos de dos'}
    fuerte = next(iter((foco & ocupadas) - {debil}))
    aro_fuerte = (locales.get(fuerte) or {}).get('aro_base') or {}
    if not (aro_fuerte.get('presente')
            and int(aro_fuerte.get('soporte_centros', 0)) >= 3):
        return False, {'motivo': 'el otro destino no tiene aro fuerte'}

    local_debil = locales.get(debil) or {}
    aro_debil = local_debil.get('aro_base') or {}
    evidencia_parcial = bool(
        not aro_debil.get('presente')
        and float(aro_debil.get('mejor_arco_continuo', 0.0)) >= 0.35
        and float(aro_debil.get('mejor_gradiente_mediano', 0.0)) >= 20.0
        and float(local_debil.get('delta_textura_centro', 0.0)) >= 25.0
        and float(local_debil.get('abs_delta_borde', 0.0)) >= 20.0
    )
    if not evidencia_parcial:
        return False, {'motivo': 'el destino debil no aporta evidencia parcial'}

    for origen in foco - ocupadas:
        local_origen = locales.get(origen) or {}
        aro_origen = local_origen.get('aro_base') or {}
        if (aro_origen.get('presente')
                or int(aro_origen.get('soporte_centros', 0)) >= 3
                or str((detalle.get(origen) or {}).get('observado')).lower()
                != 'vacia'):
            return False, {
                'motivo': 'un origen no quedo limpiamente vacio',
                'casilla': origen,
            }

    return True, {
        'motivo': 'enroque completo con un destino de aro parcial',
        'modo_deteccion': modo,
        'destino_parcial': debil,
        'destino_fuerte': fuerte,
        'firma': sorted(firma_observada),
        'extras': sorted(extras),
        'mejor_arco': float(aro_debil.get('mejor_arco_continuo', 0.0)),
        'mejor_gradiente': float(
            aro_debil.get('mejor_gradiente_mediano', 0.0)),
    }


def _confirmar_destino_con_vecina_proyectada(det_evento,
                                              resultado_post,
                                              foco_post,
                                              ocupadas_esperadas,
                                              origen_fisico,
                                              destino_fisico):
    """Tolera una única proyección sobre un destino alternativo descartado.

    La geometría puede conservar destinos vecinos porque una pieza alta invade
    sus ROI. Esta salida sólo actúa si el movimiento verdadero ya dejó origen y
    destino en el estado esperado, el destino muestra un aro propio fuerte y la
    única contradicción es otro destino de la misma pieza, adyacente al real y
    sin ningún grupo de aros. No deduce ni elige la jugada.
    """
    conflicto = (det_evento or {}).get('conflicto_patron_fisico') or {}
    alternativas = {
        str(x)[:4].upper()
        for x in (conflicto.get('alternativas_no_naturales') or [])
        if len(str(x)) >= 4
    }
    firma = {
        str(x).upper()
        for x in (conflicto.get('firma_a_confirmar') or [])
    }
    foco = {str(x).upper() for x in (foco_post or [])}
    ocupadas = {str(x).upper() for x in (ocupadas_esperadas or [])}
    origen = str(origen_fisico).upper()
    destino = str(destino_fisico).upper()

    if not (alternativas and firma and firma == foco
            and origen in foco and destino in foco):
        return False, {'motivo': 'sin conflicto fisico exacto de destinos'}

    historial = (resultado_post or {}).get('historial') or []
    ultimo = historial[-1] if historial else {}
    contradicciones = {
        str(x).upper()
        for x in (ultimo.get('contradicciones') or [])
    }
    detalle = {
        str(k).upper(): v
        for k, v in (ultimo.get('detalle') or {}).items()
        if isinstance(v, dict)
    }
    locales = (
        (ultimo.get('clasificacion_local') or {}).get('estados') or {}
    )
    locales = {str(k).upper(): v for k, v in locales.items()
               if isinstance(v, dict)}

    if len(contradicciones) != 1 or set(detalle) != foco:
        return False, {
            'motivo': 'POST no tiene una unica contradiccion completa',
            'contradicciones': sorted(contradicciones),
        }

    vecina = next(iter(contradicciones))
    if vecina in ocupadas or vecina in (origen, destino):
        return False, {'motivo': 'la contradiccion no es una vecina vacia'}

    # Debe ser exactamente un destino alternativo de la misma pieza/origen.
    alternativas_vecina = {
        m for m in alternativas if m[:2] == origen and m[2:4] == vecina
    }
    if not alternativas_vecina:
        return False, {'motivo': 'la vecina no es un destino alternativo'}

    try:
        distancia = max(abs(ord(vecina[0]) - ord(destino[0])),
                        abs(int(vecina[1]) - int(destino[1])))
    except (IndexError, TypeError, ValueError):
        return False, {'motivo': 'coordenadas fisicas invalidas'}
    if distancia != 1:
        return False, {'motivo': 'el destino alternativo no es adyacente'}

    if (detalle.get(origen) or {}).get('observado') != 'vacia':
        return False, {'motivo': 'el origen no quedo confirmado vacio'}
    if (detalle.get(destino) or {}).get('observado') != 'ocupada':
        return False, {'motivo': 'el destino real no quedo confirmado ocupado'}

    for sq in foco - {vecina}:
        esperado = 'ocupada' if sq in ocupadas else 'vacia'
        observado = str((detalle.get(sq) or {}).get('observado') or '').lower()
        if observado != esperado:
            return False, {
                'motivo': 'otra casilla POST no coincide',
                'casilla': sq,
                'esperado': esperado,
                'observado': observado,
            }

    aro_destino = (locales.get(destino) or {}).get('aro_base') or {}
    aro_vecina = (locales.get(vecina) or {}).get('aro_base') or {}
    if not (aro_destino.get('presente')
            and int(aro_destino.get('soporte_centros', 0)) >= 3):
        return False, {'motivo': 'el destino real no tiene aro fuerte'}
    # ``presente`` exige un grupo de al menos 3 centros compatibles. Uno o
    # dos máximos aislados no forman un aro: es justamente el ruido medido en
    # D8 cuando el caballo quedó en D7. La condición anterior exigía soporte
    # exactamente cero y contradecía el criterio geométrico del detector.
    if (aro_vecina.get('presente')
            or int(aro_vecina.get('soporte_centros', 0)) >= 3):
        return False, {'motivo': 'la vecina tiene un grupo de aro propio'}

    return True, {
        'motivo': 'destino con aro fuerte y alternativa vecina sin grupo de aro',
        'origen': origen,
        'destino': destino,
        'vecina_proyectada': vecina,
        'alternativa_descartada': sorted(alternativas_vecina),
        'firma': sorted(firma),
    }


def _confirmar_origen_proyectado_por_destino(det_evento,
                                              resultado_post,
                                              foco_post,
                                              ocupadas_esperadas,
                                              origen_fisico,
                                              destino_fisico):
    """Tolera la proyección del destino sobre el origen recién vaciado.

    Sólo cubre un movimiento simple entre casillas adyacentes cuya firma
    temporal contiene exactamente origen y destino. El POST debe confirmar el
    destino con aro fuerte y contradecir únicamente el origen, donde no puede
    existir un grupo de aro. No deduce ni elige la jugada.
    """
    firma = {
        str(x).upper()
        for x in ((det_evento or {}).get('firma_temporal')
                  or (det_evento or {}).get('cambiadas') or [])
    }
    foco = {str(x).upper() for x in (foco_post or [])}
    ocupadas = {str(x).upper() for x in (ocupadas_esperadas or [])}
    origen = str(origen_fisico).upper()
    destino = str(destino_fisico).upper()
    pareja = {origen, destino}

    if not (firma == pareja and foco == pareja
            and origen not in ocupadas and destino in ocupadas):
        return False, {'motivo': 'sin firma simple exacta origen-destino'}

    try:
        distancia = max(abs(ord(origen[0]) - ord(destino[0])),
                        abs(int(origen[1]) - int(destino[1])))
    except (IndexError, TypeError, ValueError):
        return False, {'motivo': 'coordenadas fisicas invalidas'}
    if distancia != 1:
        return False, {'motivo': 'origen y destino no son adyacentes'}

    historial = (resultado_post or {}).get('historial') or []
    ultimo = historial[-1] if historial else {}
    contradicciones = {
        str(x).upper()
        for x in (ultimo.get('contradicciones') or [])
    }
    detalle = {
        str(k).upper(): v
        for k, v in (ultimo.get('detalle') or {}).items()
        if isinstance(v, dict)
    }
    locales = (
        (ultimo.get('clasificacion_local') or {}).get('estados') or {}
    )
    locales = {str(k).upper(): v for k, v in locales.items()
               if isinstance(v, dict)}

    if contradicciones != {origen} or set(detalle) != pareja:
        return False, {
            'motivo': 'POST no contradice unicamente el origen',
            'contradicciones': sorted(contradicciones),
        }
    if str((detalle.get(origen) or {}).get('observado') or '').lower() != 'ocupada':
        return False, {'motivo': 'el origen no aparece falsamente ocupado'}
    if str((detalle.get(destino) or {}).get('observado') or '').lower() != 'ocupada':
        return False, {'motivo': 'el destino no quedo confirmado ocupado'}

    aro_destino = (locales.get(destino) or {}).get('aro_base') or {}
    aro_origen = (locales.get(origen) or {}).get('aro_base') or {}
    if not (aro_destino.get('presente')
            and int(aro_destino.get('soporte_centros', 0)) >= 3):
        return False, {'motivo': 'el destino real no tiene aro fuerte'}
    if (aro_origen.get('presente')
            or int(aro_origen.get('soporte_centros', 0)) >= 3):
        return False, {'motivo': 'el origen conserva un grupo de aro propio'}

    return True, {
        'motivo': 'destino con aro fuerte proyectado sobre origen sin grupo de aro',
        'origen_proyectado': origen,
        'destino': destino,
        'firma': sorted(firma),
        'soporte_aro_origen': int(aro_origen.get('soporte_centros', 0)),
        'soporte_aro_destino': int(aro_destino.get('soporte_centros', 0)),
    }


def _confirmar_destino_por_firma_exacta_y_aro_parcial(det_evento,
                                                       resultado_post,
                                                       foco_post,
                                                       ocupadas_esperadas,
                                                       origen_fisico,
                                                       destino_fisico,
                                                       umbral_arco=0.35,
                                                       umbral_gradiente=17.0,
                                                       umbral_textura=15.0,
                                                       umbral_borde=15.0,
                                                       permitir_aro_fuerte_sin_borde=False):
    """Confirma un destino de perímetro cuyo aro quedó parcialmente cortado.

    No baja el umbral global del detector. Sólo actúa cuando el evento temporal
    contiene exactamente origen+destino, el origen quedó vacío y es la única
    lectura POST correcta, y el destino aporta simultáneamente textura fuerte,
    cambio de borde y un fragmento de aro. Así no se aplica a las firmas con
    casillas extras que producen las proyecciones vecinas conocidas.
    """
    firma = {
        str(x).upper()
        for x in ((det_evento or {}).get('firma_temporal')
                  or (det_evento or {}).get('cambiadas') or [])
    }
    foco = {str(x).upper() for x in (foco_post or [])}
    ocupadas = {str(x).upper() for x in (ocupadas_esperadas or [])}
    origen = str(origen_fisico).upper()
    destino = str(destino_fisico).upper()
    pareja = {origen, destino}

    if not (firma == pareja and foco == pareja
            and origen not in ocupadas and destino in ocupadas):
        return False, {'motivo': 'sin firma simple exacta origen-destino'}

    historial = (resultado_post or {}).get('historial') or []
    ultimo = historial[-1] if historial else {}
    contradicciones = {
        str(x).upper()
        for x in (ultimo.get('contradicciones') or [])
    }
    detalle = {
        str(k).upper(): v
        for k, v in (ultimo.get('detalle') or {}).items()
        if isinstance(v, dict)
    }
    locales = (
        (ultimo.get('clasificacion_local') or {}).get('estados') or {}
    )
    locales = {str(k).upper(): v for k, v in locales.items()
               if isinstance(v, dict)}

    if contradicciones != {destino} or set(detalle) != pareja:
        return False, {
            'motivo': 'POST no contradice unicamente el destino',
            'contradicciones': sorted(contradicciones),
        }
    if str((detalle.get(origen) or {}).get('observado') or '').lower() != 'vacia':
        return False, {'motivo': 'el origen no quedo confirmado vacio'}
    if str((detalle.get(destino) or {}).get('observado') or '').lower() not in (
            'vacia', 'dudosa'):
        return False, {'motivo': 'el destino no es el unico falso negativo'}

    local_origen = locales.get(origen) or {}
    local_destino = locales.get(destino) or {}
    aro_origen = local_origen.get('aro_base') or {}
    aro_destino = local_destino.get('aro_base') or {}

    origen_limpio = bool(
        local_origen.get('vacia_por_centro_limpio_sin_aro')
        or local_origen.get('vacia_por_aro_ausente')
    )
    if not origen_limpio:
        return False, {'motivo': 'el origen no tiene evidencia local de vacio'}
    if (aro_origen.get('presente')
            or int(aro_origen.get('soporte_centros', 0)) >= 3):
        return False, {'motivo': 'el origen conserva un grupo de aro'}

    mejor_arco = float(aro_destino.get('mejor_arco_continuo') or 0.0)
    mejor_gradiente = float(
        aro_destino.get('mejor_gradiente_mediano') or 0.0
    )
    soporte_centros = int(aro_destino.get('soporte_centros') or 0)
    delta_textura = float(local_destino.get('delta_textura_centro') or 0.0)
    delta_borde = float(local_destino.get('abs_delta_borde') or 0.0)

    evidencia_parcial = bool(
        mejor_arco >= float(umbral_arco)
        and mejor_gradiente >= float(umbral_gradiente)
        and delta_textura >= float(umbral_textura)
        and delta_borde >= float(umbral_borde)
    )
    # Caso real D1->A4 (físico E8->H5): el borde exterior corta parte
    # de la base y reduce el delta de borde, aunque el arco aparece fuerte,
    # con alto gradiente y repetido en dos centros próximos. Esta alternativa
    # sólo se habilita desde la rama de bandas exteriores.
    aro_fuerte_repetido = bool(
        permitir_aro_fuerte_sin_borde
        and mejor_arco >= 0.50
        and mejor_gradiente >= 30.0
        and delta_textura >= float(umbral_textura)
        and soporte_centros >= 2
    )

    if not (evidencia_parcial or aro_fuerte_repetido):
        return False, {
            'motivo': 'el destino no tiene evidencia parcial conjunta suficiente',
            'mejor_arco': mejor_arco,
            'mejor_gradiente': mejor_gradiente,
            'soporte_centros': soporte_centros,
            'delta_textura': delta_textura,
            'delta_borde': delta_borde,
        }

    return True, {
        'motivo': 'firma exacta con origen vacio y aro parcial fuerte en destino',
        'origen': origen,
        'destino': destino,
        'firma': sorted(firma),
        'mejor_arco': mejor_arco,
        'mejor_gradiente': mejor_gradiente,
        'soporte_centros': soporte_centros,
        'delta_textura': delta_textura,
        'delta_borde': delta_borde,
        'aro_fuerte_sin_borde': aro_fuerte_repetido,
    }


def _confirmar_destino_banda_recortado_en_tres_post(det_evento,
                                                      resultado_post,
                                                      foco_post,
                                                      ocupadas_esperadas,
                                                      origen_fisico,
                                                      destino_fisico):
    """Rescata un destino exterior recortado sólo con tres POST concordantes.

    Este camino cubre el caso real C8->D8 (lógico F1->E1) en el que la pieza
    queda cortada por el borde superior: el evento temporal identifica con
    exactitud origen y destino, pero el clasificador absoluto deja el destino
    ``dudoso``. No se relaja ningún umbral global. Para aceptar se exigen tres
    capturas consecutivas con el origen limpiamente vacío y una señal fuerte,
    centrada y estable en el destino. La relación centro/borde evita rescatar
    la proyección lateral histórica de una pieza vecina sobre D8.
    """
    firma = {
        str(x).upper()
        for x in ((det_evento or {}).get('firma_temporal')
                  or (det_evento or {}).get('cambiadas') or [])
    }
    foco = {str(x).upper() for x in (foco_post or [])}
    ocupadas = {str(x).upper() for x in (ocupadas_esperadas or [])}
    origen = str(origen_fisico).upper()
    destino = str(destino_fisico).upper()
    pareja = {origen, destino}

    destino_en_banda = bool(
        len(destino) == 2
        and (destino[0] in ('A', 'B', 'G', 'H')
             or destino[1] in ('1', '2', '7', '8'))
    )
    if not (destino_en_banda
            and firma == pareja and foco == pareja
            and origen not in ocupadas and destino in ocupadas):
        return False, {'motivo': 'sin pareja exacta en banda exterior'}

    historial = list((resultado_post or {}).get('historial') or [])
    if len(historial) < 3:
        return False, {
            'motivo': 'faltan tres lecturas POST independientes',
            'lecturas': len(historial),
        }

    muestras = []
    for intento in historial[-3:]:
        contradicciones = {
            str(x).upper() for x in (intento.get('contradicciones') or [])
        }
        dudosas = {str(x).upper() for x in (intento.get('dudosas') or [])}
        detalle = {
            str(k).upper(): v
            for k, v in (intento.get('detalle') or {}).items()
            if isinstance(v, dict)
        }
        locales = (
            (intento.get('clasificacion_local') or {}).get('estados') or {}
        )
        locales = {
            str(k).upper(): v for k, v in locales.items()
            if isinstance(v, dict)
        }

        if (contradicciones or dudosas != {destino}
                or set(detalle) != pareja):
            return False, {
                'motivo': 'las tres lecturas no dejan sólo el destino dudoso',
                'contradicciones': sorted(contradicciones),
                'dudosas': sorted(dudosas),
            }
        if str((detalle.get(origen) or {}).get('observado') or '').lower() != 'vacia':
            return False, {'motivo': 'el origen no quedó vacío en las tres lecturas'}
        if str((detalle.get(destino) or {}).get('observado') or '').lower() != 'dudosa':
            return False, {'motivo': 'el destino no quedó dudoso de forma repetida'}

        local_origen = locales.get(origen) or {}
        local_destino = locales.get(destino) or {}
        aro_origen = local_origen.get('aro_base') or {}
        aro_destino = local_destino.get('aro_base') or {}
        origen_limpio = bool(
            local_origen.get('vacia_por_centro_limpio_sin_aro')
            or local_origen.get('vacia_por_aro_ausente')
        )
        if (not origen_limpio or aro_origen.get('presente')
                or int(aro_origen.get('soporte_centros') or 0) >= 3):
            return False, {'motivo': 'el origen conserva evidencia de pieza'}

        textura = float(local_destino.get('delta_textura_centro') or 0.0)
        borde = float(local_destino.get('abs_delta_borde') or 0.0)
        centro = float(local_destino.get('abs_delta_centro') or 0.0)
        arco = float(aro_destino.get('mejor_arco_continuo') or 0.0)
        gradiente = float(aro_destino.get('mejor_gradiente_mediano') or 0.0)
        soporte = int(aro_destino.get('soporte_centros') or 0)

        # El destino real de este patrón concentra la señal en el centro
        # (textura/borde > 3 en el caso observado). La invasión vecina D8
        # histórica era difusa (aprox. 1,29), por eso se exige margen 2,5.
        centro_sobre_borde = centro / max(borde, 0.01)
        textura_sobre_borde = textura / max(borde, 0.01)
        evidencia_recortada = bool(
            not aro_destino.get('presente')
            and soporte < 3
            and arco >= 0.24
            and gradiente >= 16.0
            and textura >= 40.0
            and borde >= 12.0
            and centro >= 25.0
            and textura_sobre_borde >= 2.5
            and centro_sobre_borde >= 1.7
        )
        if not evidencia_recortada:
            return False, {
                'motivo': 'una lectura no tiene señal central recortada suficiente',
                'arco': arco,
                'gradiente': gradiente,
                'textura': textura,
                'borde': borde,
                'centro': centro,
                'textura_sobre_borde': round(textura_sobre_borde, 3),
                'centro_sobre_borde': round(centro_sobre_borde, 3),
            }
        muestras.append({
            'arco': arco,
            'gradiente': gradiente,
            'textura': textura,
            'borde': borde,
            'centro': centro,
            'textura_sobre_borde': textura_sobre_borde,
            'centro_sobre_borde': centro_sobre_borde,
        })

    # Rechaza un máximo fugaz: las magnitudes principales deben mantenerse
    # dentro de un 20 % durante las tres capturas POST.
    for clave in ('textura', 'borde', 'centro'):
        valores = [m[clave] for m in muestras]
        if max(valores) / max(min(valores), 0.01) > 1.20:
            return False, {
                'motivo': 'la señal del destino no es estable en tres POST',
                'metrica': clave,
                'valores': [round(v, 2) for v in valores],
            }

    return True, {
        'motivo': 'tres POST confirman señal central fuerte en destino recortado',
        'origen': origen,
        'destino': destino,
        'firma': sorted(firma),
        'lecturas': len(muestras),
        'min_textura': round(min(m['textura'] for m in muestras), 2),
        'min_gradiente': round(min(m['gradiente'] for m in muestras), 2),
        'min_arco': round(min(m['arco'] for m in muestras), 3),
        'min_textura_sobre_borde': round(
            min(m['textura_sobre_borde'] for m in muestras), 3),
    }


def _confirmar_destino_banda_con_extras_limpias(det_evento,
                                                 resultado_post,
                                                 foco_post,
                                                 ocupadas_esperadas,
                                                 origen_fisico,
                                                 destino_fisico):
    """Confirma una pieza recortada si sus proyecciones quedaron vacías.

    Se usa únicamente desde la banda exterior. La firma temporal debe coincidir
    con todo el foco y contener origen, destino y como máximo dos vecinas del
    destino. El POST debe dejar sólo el destino dudoso; origen y extras tienen
    que estar vacíos, localmente limpios y sin grupo de aro.

    También cubre el falso negativo concluyente observado en C8->G4: la firma
    contiene una alternativa vecina H4 por la proyección del alfil, el global
    declara vacíos ambos destinos, pero G4 conserva un arco parcial fuerte y
    H4 queda ópticamente limpia. Ese segundo camino exige que la extra sea una
    alternativa física explícita del mismo origen y compara ambas casillas;
    no baja ningún umbral global ni decide por legalidad.
    """
    firma = {
        str(x).upper()
        for x in ((det_evento or {}).get('firma_temporal')
                  or (det_evento or {}).get('cambiadas') or [])
    }
    foco = {str(x).upper() for x in (foco_post or [])}
    ocupadas = {str(x).upper() for x in (ocupadas_esperadas or [])}
    origen = str(origen_fisico).upper()
    destino = str(destino_fisico).upper()
    pareja = {origen, destino}

    if not (firma == foco and pareja.issubset(foco)
            and 3 <= len(foco) <= 4
            and (foco & ocupadas) == {destino}):
        return False, {'motivo': 'firma expandida no coincide con el foco'}

    extras = foco - pareja
    try:
        if not all(
            max(abs(ord(sq[0]) - ord(destino[0])),
                abs(int(sq[1]) - int(destino[1]))) == 1
            for sq in extras
        ):
            return False, {'motivo': 'una extra no es vecina del destino'}
    except (IndexError, TypeError, ValueError):
        return False, {'motivo': 'coordenadas de extras invalidas'}

    conflicto = (det_evento or {}).get('conflicto_patron_fisico') or {}
    alternativas = {
        str(x)[:4].upper()
        for x in (conflicto.get('alternativas_no_naturales') or [])
        if len(str(x)) >= 4
    }

    historial = (resultado_post or {}).get('historial') or []
    ultimo = historial[-1] if historial else {}
    contradicciones = {
        str(x).upper() for x in (ultimo.get('contradicciones') or [])
    }
    dudosas = {str(x).upper() for x in (ultimo.get('dudosas') or [])}
    detalle = {
        str(k).upper(): v
        for k, v in (ultimo.get('detalle') or {}).items()
        if isinstance(v, dict)
    }
    locales = (
        (ultimo.get('clasificacion_local') or {}).get('estados') or {}
    )
    locales = {str(k).upper(): v for k, v in locales.items()
               if isinstance(v, dict)}

    destino_observado = str(
        (detalle.get(destino) or {}).get('observado') or ''
    ).lower()
    destino_dudoso = bool(
        not contradicciones
        and dudosas == {destino}
        and destino_observado == 'dudosa'
    )
    destino_falso_vacio = bool(
        contradicciones == {destino}
        and not dudosas
        and destino_observado == 'vacia'
    )
    if not ((destino_dudoso or destino_falso_vacio)
            and set(detalle) == foco):
        return False, {
            'motivo': 'POST no deja unicamente el destino dudoso o falso vacio',
            'contradicciones': sorted(contradicciones),
            'dudosas': sorted(dudosas),
        }

    for sq in foco - {destino}:
        local = locales.get(sq) or {}
        aro = local.get('aro_base') or {}
        limpio = bool(
            local.get('vacia_por_centro_limpio_sin_aro')
            or local.get('vacia_por_aro_ausente')
        )
        if (str((detalle.get(sq) or {}).get('observado') or '').lower()
                != 'vacia' or not limpio or aro.get('presente')
                or int(aro.get('soporte_centros', 0)) >= 3):
            return False, {
                'motivo': 'origen o extra no esta limpiamente vacia',
                'casilla': sq,
            }

    local_destino = locales.get(destino) or {}
    aro_destino = local_destino.get('aro_base') or {}
    evidencia = {
        'mejor_arco': float(aro_destino.get('mejor_arco_continuo') or 0.0),
        'mejor_gradiente': float(
            aro_destino.get('mejor_gradiente_mediano') or 0.0),
        'delta_textura': float(
            local_destino.get('delta_textura_centro') or 0.0),
        'delta_borde': float(local_destino.get('abs_delta_borde') or 0.0),
        'delta_centro': float(local_destino.get('abs_delta_centro') or 0.0),
    }

    if destino_dudoso:
        evidencia_suficiente = bool(
            not aro_destino.get('presente')
            and int(aro_destino.get('soporte_centros', 0)) < 3
            and evidencia['mejor_arco'] >= 0.43
            and evidencia['mejor_gradiente'] >= 12.5
            and evidencia['delta_textura'] >= 22.0
            and evidencia['delta_borde'] >= 21.0
        )
        modo = 'dudoso_con_evidencia_conjunta'
    else:
        # Para revertir un falso VACIO hace falta evidencia comparativa mucho
        # más fuerte que para completar una duda. Se admite una sola extra y
        # debe ser exactamente la alternativa física del mismo origen.
        if (len(extras) != 1
                or not all(origen + sq in alternativas for sq in extras)):
            return False, {
                'motivo': 'el falso vacio no tiene una alternativa fisica exacta',
                'alternativas': sorted(alternativas),
                'extras': sorted(extras),
            }

        extra = next(iter(extras))
        local_extra = locales.get(extra) or {}
        aro_extra = local_extra.get('aro_base') or {}
        extra_arco = float(aro_extra.get('mejor_arco_continuo') or 0.0)
        extra_gradiente = float(
            aro_extra.get('mejor_gradiente_mediano') or 0.0
        )
        evidencia.update({
            'extra': extra,
            'extra_mejor_arco': extra_arco,
            'extra_mejor_gradiente': extra_gradiente,
        })
        evidencia_suficiente = bool(
            not aro_destino.get('presente')
            and int(aro_destino.get('soporte_centros', 0)) < 3
            and evidencia['mejor_arco'] >= 0.55
            and evidencia['mejor_gradiente'] >= 25.0
            and evidencia['delta_textura'] >= 8.0
            and evidencia['delta_borde'] >= 8.0
            and evidencia['delta_centro'] >= 8.0
            and not aro_extra.get('presente')
            and int(aro_extra.get('soporte_centros', 0)) < 3
            and extra_arco < 0.35
            and extra_gradiente < 15.0
            and evidencia['mejor_arco'] >= 1.5 * max(extra_arco, 0.01)
            and evidencia['mejor_gradiente'] >= 2.0 * max(extra_gradiente, 0.01)
        )
        modo = 'falso_vacio_con_aro_relativo'

    if not evidencia_suficiente:
        return False, {
            'motivo': 'destino sin evidencia parcial comparativa suficiente',
            'modo': modo,
            **evidencia,
        }

    return True, {
        'motivo': 'destino de banda confirmado con extras vecinas limpias',
        'modo': modo,
        'origen': origen,
        'destino': destino,
        'extras_limpias': sorted(extras),
        **evidencia,
    }


def _confirmar_captura_con_aro_parcial(det_evento, resultado_post,
                                      foco_post, ocupadas_antes,
                                      ocupadas_esperadas, origen_fisico,
                                      destino_fisico):
    """Evidencia de una captura de bajo contraste, aún sin aceptar la jugada.

    Exige origen y destino ocupados PRE, firma completa y extras sólo junto
    a origen/destino. En POST queda una única contradicción en destino; todas
    las otras casillas deben estar localmente limpias. El llamador exige una
    segunda captura fresca. No depende del tipo de pieza ni del perímetro.
    """
    origen, destino = str(origen_fisico).upper(), str(destino_fisico).upper()
    pareja = {origen, destino}
    firma = {str(s).upper() for s in (
        (det_evento or {}).get('firma_temporal')
        or (det_evento or {}).get('cambiadas') or [])}
    foco = {str(s).upper() for s in foco_post}
    pre = {str(s).upper() for s in ocupadas_antes}
    post = {str(s).upper() for s in ocupadas_esperadas}
    if not (len(pareja) == 2 and firma == foco and pareja <= foco
            and 2 <= len(foco) <= 4 and pareja <= pre
            and foco & pre == pareja and foco & post == {destino}):
        return False, {'motivo': 'sin firma completa de captura aislada'}
    if any(len(s) != 2 or s[0] not in 'ABCDEFGH' or s[1] not in '12345678'
           for s in foco):
        return False, {'motivo': 'coordenadas invalidas'}
    extras = foco - pareja
    if any(not any(max(abs(ord(s[0]) - ord(p[0])),
                       abs(int(s[1]) - int(p[1]))) == 1 for p in pareja)
           for s in extras):
        return False, {'motivo': 'extra distante de la captura'}
    historial = (resultado_post or {}).get('historial') or []
    ultimo = historial[-1] if historial else {}
    detalle = ultimo.get('detalle') or {}
    local = (ultimo.get('clasificacion_local') or {}).get('estados') or {}
    if (set(ultimo.get('contradicciones') or []) != {destino}
            or ultimo.get('dudosas') or set(detalle) != foco
            or set(local) != foco
            or (detalle.get(destino) or {}).get('observado') != 'vacia'):
        return False, {'motivo': 'POST no tiene unicamente el destino falso vacio'}
    for sq in foco - {destino}:
        d = local[sq]
        aro = d.get('aro_base') or {}
        # Ausencia nominal de aro sola no basta: el centro también tiene
        # que conservar brillo/textura de vacío y la búsqueda no mostrar arco.
        if not (detalle[sq].get('observado') == 'vacia'
                and d.get('vacia_por_centro_limpio_sin_aro')
                and not aro.get('presente')
                and aro.get('soporte_centros') == 0
                and float(aro.get('mejor_arco_continuo', 1)) < 0.35
                and float(aro.get('mejor_gradiente_mediano', 999)) < 15):
            return False, {'motivo': 'origen o extra no esta limpia', 'casilla': sq}
    d = local[destino]
    aro = d.get('aro_base') or {}
    medidas = {
        'arco': float(aro.get('mejor_arco_continuo') or 0),
        'gradiente': float(aro.get('mejor_gradiente_mediano') or 0),
        'textura': float(d.get('delta_textura_centro') or 0),
        'borde': float(d.get('abs_delta_borde') or 0),
    }
    # Los máximos de arco y gradiente provienen del mismo centro medido.
    # Límites superiores rechazan datos ausentes/infinito además del mínimo.
    evidencia = bool(
        not d.get('vacia_por_centro_limpio_sin_aro')
        and 0.50 <= medidas['arco'] <= 1.0
        and 25 <= medidas['gradiente'] <= 255
        and 15 <= medidas['textura'] <= 255
        and 10 <= medidas['borde'] <= 255)
    return evidencia, {
        'motivo': ('captura con evidencia parcial conjunta' if evidencia
                   else 'destino sin evidencia parcial suficiente'),
        'origen': origen, 'destino': destino,
        'extras_limpias': sorted(extras), **medidas}


def _confirmar_jugada_vision(mv, det_evento=None):
    """Valida una jugada detectada contra un ANCLA fisico.

    Regla importante: la vision puede detectar un cambio por una mano que
    pasa, pero eso no cambia el ancla. Solo aceptamos la jugada si el tablero
    observado coincide con el estado que produciria esa jugada.

    Con vision.consenso() (metodo absoluto) se comprueba directamente el
    estado posterior. Sin absolutos hacemos doble lectura de la misma jugada
    separada por un pequeño tiempo: una mano pasajera no deberia producir dos
    lecturas identicas y legales.
    """
    global _ultima_candidata_vision, _ultima_candidata_ts

    if vision is None:
        return False, 'vision no disponible'

    ancla_evento = (det_evento or {}).get('ancla_evento')
    if ancla_evento is not None:
        if (ancla_evento.get('fen') != tablero.fen()
                or ancla_evento.get('referencia_id') != getattr(vision, '_referencia_id', None)):
            return False, 'el FEN o el PRE cambiaron desde la deduccion'
        if set(_ancla_vision_fisica or []) != set(_fisicas_de_tablero(tablero)):
            return False, 'el ancla fisica no corresponde al FEN del evento'

    # El ancla siempre representa la posicion que la app cree que esta sobre
    # la madera ANTES de aceptar esta jugada.
    if _ancla_vision_fisica is None:
        _diag_vision('confirmacion_falla', jugada=mv, motivo='sin ancla fisica')
        return False, 'sin ancla fisica; se ignora hasta fijar referencia'

    try:
        m = chess.Move.from_uci(mv)
    except Exception:
        return False, 'jugada invalida'

    if m not in tablero.legal_moves:
        return False, 'la jugada ya no es legal'

    # BROKIE 4.0G.4:
    # La confirmación FINAL debe demostrar el ESTADO POST de ESTA jugada.
    #
    # No alcanza con preguntar si origen y destino "cambiaron", porque esa
    # pregunta es simétrica y no distingue A6->B7 de B7->A6 en una captura.
    esperado = tablero.copy(stack=False)
    esperado.push(m)

    ocupadas_esperadas = _fisicas_de_tablero(esperado)

    pre_fis = {
        str(x).lower()
        for x in (_ancla_vision_fisica or [])
    }
    post_fis = {
        str(x).lower()
        for x in ocupadas_esperadas
    }

    o_log = chess.square_name(m.from_square)
    d_log = chess.square_name(m.to_square)
    o_fis = sq_fisico(o_log).lower()
    d_fis = sq_fisico(d_log).lower()

    # Diferencia PRE/POST captura automáticamente:
    # - movimiento normal: origen + destino
    # - en passant: origen + destino + peón capturado
    # - enroque: las 4 casillas de rey/torre
    #
    # En una captura normal el destino está ocupado PRE y POST, por eso
    # lo agregamos explícitamente junto al origen.
    foco_post = sorted(
        (pre_fis ^ post_fis) |
        {o_fis, d_fis}
    )
    casillas_movimiento = list(foco_post)
    opciones_blancas = ({'color_movimiento': 'blanca'}
                        if tablero.turn == chess.WHITE
                        and getattr(vision, 'PRUEBA_BLANCAS_NUEVAS', False) else {})

    # V9: si el patrón de la pieza intentó descartar otro destino físico,
    # comprobar también dónde quedó esa alternativa. No basta confirmar la
    # proyección de una pieza sobre el destino legal. No ampliar por cualquier
    # extra: preserva el tratamiento existente del paralaje y los enroques.
    conflicto_patron = (det_evento or {}).get('conflicto_patron_fisico') or {}
    if ((det_evento or {}).get('anclas_turno') or {}).get('revisar_extras'):
        # La firma ya no genera orígenes rivales, pero sus casillas NO se
        # ocultan: se comprueban aparte como posibles alteraciones físicas.
        firma = ((det_evento or {}).get('firma_temporal')
                 or (det_evento or {}).get('cambiadas') or [])
        foco_post = sorted(set(foco_post) | {
            str(s).lower() for s in firma
            if len(str(s)) == 2 and str(s)[0].lower() in 'abcdefgh'
            and str(s)[1] in '12345678'})
    if ((det_evento or {}).get('preservacion_destino_estructural') or {}).get('aplicado'):
        # Una candidata recuperada frente a otro destino requiere comprobar
        # también las extras: no basta ocupar el destino elegido.
        foco_post = sorted(set(foco_post) | {
            str(sq).lower() for sq in (det_evento or {}).get('firma_temporal', [])
            if len(str(sq)) == 2 and str(sq)[0].lower() in 'abcdefgh'
            and str(sq)[1] in '12345678'
        })
    if conflicto_patron and not tablero.is_castling(m):
        foco_post = sorted(set(foco_post) | {
            str(sq).lower() for sq in conflicto_patron.get('firma_a_confirmar', [])
            if len(str(sq)) == 2 and str(sq)[0].lower() in 'abcdefgh'
            and str(sq)[1] in '12345678'
        })

    if hasattr(vision, 'brokie45_confirmar_estado_post'):
        try:
            r45 = vision.brokie45_confirmar_estado_post(
                list(pre_fis),
                list(post_fis),
                foco_post,
                intentos=3,
                pausa_s=0.25,
                casillas_movimiento=casillas_movimiento,
                **opciones_blancas,
            )

            if r45.get('ok'):
                _ultima_candidata_vision = None
                _ultima_candidata_ts = 0.0
                _diag_vision(
                    'confirmacion_ok',
                    jugada=mv,
                    metodo='estado POST absoluto 4.0G.4',
                    foco=foco_post,
                    detalle=r45,
                )
                return True, 'estado POST físico coincide con la jugada'

            _diag_vision(
                'confirmacion_falla',
                jugada=mv,
                motivo=r45.get('motivo'),
                foco=foco_post,
                detalle=r45,
            )

            # El enroque ya fue deducido por la firma temporal exacta de sus
            # cuatro casillas. En el perímetro, una pieza recién colocada puede
            # proyectarse sobre uno de los orígenes y hacer que el POST lo vea
            # ocupado. Se tolera exclusivamente ese patrón: una sola casilla
            # de origen falsa y las otras tres casillas concluyentes.
            if tablero.is_castling(m) and (r45.get('contradiccion') or r45.get('inconcluso')):
                acepta_atomico, detalle_atomico = (
                    _confirmar_enroque_atomico_con_origen_proyectado(
                        det_evento,
                        r45,
                        foco_post,
                        post_fis,
                        pre_fis,
                    )
                )
                if acepta_atomico:
                    _ultima_candidata_vision = None
                    _ultima_candidata_ts = 0.0
                    _diag_vision(
                        'confirmacion_ok',
                        jugada=mv,
                        metodo='enroque atomico con origen proyectado',
                        foco=foco_post,
                        detalle=detalle_atomico,
                    )
                    return True, (
                        'enroque confirmado por firma exacta y POST parcial'
                    )

            if tablero.is_castling(m) and r45.get('contradiccion'):
                acepta_destino, detalle_destino = (
                    _confirmar_enroque_con_destino_parcial(
                        det_evento,
                        r45,
                        foco_post,
                        post_fis,
                        o_fis,
                        d_fis,
                    )
                )
                if acepta_destino:
                    _ultima_candidata_vision = None
                    _ultima_candidata_ts = 0.0
                    _diag_vision(
                        'confirmacion_ok',
                        jugada=mv,
                        metodo='enroque completo con destino de aro parcial',
                        foco=foco_post,
                        detalle=detalle_destino,
                    )
                    return True, (
                        'enroque confirmado con un destino de aro parcial'
                    )

            # Caso real H5->F7/F8 y D7->B5/A5: una pieza alta ocupa su destino
            # pero invade visualmente otro destino alternativo adyacente. La
            # excepción exige evidencia positiva en el aro del destino real y
            # ausencia total de grupo de aros en la vecina; nunca se aplica a
            # capturas, enroques, en-passant ni promociones.
            jugada_simple = (
                not tablero.is_capture(m)
                and not tablero.is_castling(m)
                and not tablero.is_en_passant(m)
                and m.promotion is None
            )
            if jugada_simple and r45.get('contradiccion'):
                acepta_vecina, detalle_vecina = (
                    _confirmar_destino_con_vecina_proyectada(
                        det_evento,
                        r45,
                        foco_post,
                        post_fis,
                        o_fis,
                        d_fis,
                    )
                )
                if acepta_vecina:
                    _ultima_candidata_vision = None
                    _ultima_candidata_ts = 0.0
                    _diag_vision(
                        'confirmacion_ok',
                        jugada=mv,
                        metodo='destino con aro y vecina proyectada sin aro',
                        foco=foco_post,
                        detalle=detalle_vecina,
                    )
                    return True, (
                        'destino confirmado; vecina proyectada descartada'
                    )

                acepta_origen, detalle_origen = (
                    _confirmar_origen_proyectado_por_destino(
                        det_evento,
                        r45,
                        foco_post,
                        post_fis,
                        o_fis,
                        d_fis,
                    )
                )
                if acepta_origen:
                    _ultima_candidata_vision = None
                    _ultima_candidata_ts = 0.0
                    _diag_vision(
                        'confirmacion_ok',
                        jugada=mv,
                        metodo='destino con aro proyectado sobre origen sin aro',
                        foco=foco_post,
                        detalle=detalle_origen,
                    )
                    return True, (
                        'destino confirmado; origen proyectado descartado'
                    )

                acepta_parcial, detalle_parcial = (
                    _confirmar_destino_por_firma_exacta_y_aro_parcial(
                        det_evento,
                        r45,
                        foco_post,
                        post_fis,
                        o_fis,
                        d_fis,
                    )
                )
                if acepta_parcial:
                    _ultima_candidata_vision = None
                    _ultima_candidata_ts = 0.0
                    _diag_vision(
                        'confirmacion_ok',
                        jugada=mv,
                        metodo='firma exacta con aro parcial en destino',
                        foco=foco_post,
                        detalle=detalle_parcial,
                    )
                    return True, (
                        'destino confirmado por firma exacta y aro parcial'
                    )

            # En las dos bandas exteriores cualquier pieza puede quedar
            # recortada. No se decide por tipo de pieza sino por evidencia:
            # firma exacta, origen vacío, una sola contradicción y señales
            # parciales conjuntas en el destino.
            destino_banda_exterior = bool(
                len(d_fis) == 2
                and (d_fis[0] in ('a', 'b', 'g', 'h')
                     or d_fis[1] in ('1', '2', '7', '8'))
            )
            movimiento_banda_exterior = bool(
                not tablero.is_castling(m)
                and not tablero.is_en_passant(m)
                and m.promotion is None
                and destino_banda_exterior
            )
            if movimiento_banda_exterior and r45.get('contradiccion'):
                acepta_banda, detalle_banda = (
                    _confirmar_destino_por_firma_exacta_y_aro_parcial(
                        det_evento,
                        r45,
                        foco_post,
                        post_fis,
                        o_fis,
                        d_fis,
                        umbral_arco=0.44,
                        umbral_gradiente=16.0,
                        umbral_textura=17.0,
                        umbral_borde=12.0,
                        permitir_aro_fuerte_sin_borde=True,
                    )
                )
                if acepta_banda:
                    _ultima_candidata_vision = None
                    _ultima_candidata_ts = 0.0
                    _diag_vision(
                        'confirmacion_ok',
                        jugada=mv,
                        metodo='destino de banda exterior con aro parcial',
                        foco=foco_post,
                        detalle=detalle_banda,
                    )
                    return True, (
                        'destino de banda confirmado por firma exacta y '
                        'evidencia parcial'
                    )

            # Caso real A6->B7: la base del rey activó dos vecinas y el POST
            # dejó sólo el destino G2 dudoso. Se acepta el mismo patrón para
            # cualquier pieza, siempre que todas las extras estén limpias.
            if movimiento_banda_exterior and r45.get('inconcluso'):
                acepta_recorte, detalle_recorte = (
                    _confirmar_destino_banda_recortado_en_tres_post(
                        det_evento,
                        r45,
                        foco_post,
                        post_fis,
                        o_fis,
                        d_fis,
                    )
                )
                if acepta_recorte:
                    _ultima_candidata_vision = None
                    _ultima_candidata_ts = 0.0
                    _diag_vision(
                        'confirmacion_ok',
                        jugada=mv,
                        metodo='destino de banda recortado en tres POST',
                        foco=foco_post,
                        detalle=detalle_recorte,
                    )
                    return True, (
                        'destino de banda confirmado por tres lecturas POST'
                    )

            if (movimiento_banda_exterior
                    and (r45.get('contradiccion') or r45.get('inconcluso'))):
                acepta_extras, detalle_extras = (
                    _confirmar_destino_banda_con_extras_limpias(
                        det_evento,
                        r45,
                        foco_post,
                        post_fis,
                        o_fis,
                        d_fis,
                    )
                )
                if (acepta_extras and detalle_extras.get('modo')
                        == 'falso_vacio_con_aro_relativo'):
                    # V29: un máximo parcial aislado no autoriza la jugada.
                    # Pedir otra captura real y exigir el mismo contraste
                    # entre destino y alternativa. Nunca reutilizar r45.
                    segunda_post = vision.brokie45_confirmar_estado_post(
                        list(pre_fis), list(post_fis), foco_post,
                        intentos=3, pausa_s=0.25,
                        casillas_movimiento=casillas_movimiento,
                        **opciones_blancas,
                    )
                    segunda_ok, segunda_evidencia = (
                        _confirmar_destino_banda_con_extras_limpias(
                            det_evento, segunda_post, foco_post, post_fis,
                            o_fis, d_fis,
                        )
                    )
                    acepta_extras = bool(
                        segunda_post.get('ok') or (
                            segunda_ok and segunda_evidencia.get('modo')
                            == 'falso_vacio_con_aro_relativo')
                    )
                    _diag_vision(
                        'revalidacion_aro_relativo', jugada=mv,
                        aceptada=acepta_extras, detalle=segunda_evidencia,
                        post=segunda_post,
                    )
                    if acepta_extras:
                        detalle_extras = dict(
                            detalle_extras, lecturas_minimas=2,
                            segunda_evidencia=segunda_evidencia,
                        )
                if acepta_extras:
                    _ultima_candidata_vision = None
                    _ultima_candidata_ts = 0.0
                    _diag_vision(
                        'confirmacion_ok',
                        jugada=mv,
                        metodo='destino de banda con extras limpias',
                        foco=foco_post,
                        detalle=detalle_extras,
                    )
                    return True, (
                        'destino de banda confirmado; proyecciones limpias'
                    )

            if (tablero.is_capture(m) and not tablero.is_en_passant(m)
                    and m.promotion is None and r45.get('contradiccion')):
                argumentos = (foco_post, pre_fis, post_fis, o_fis, d_fis)
                parcial, evidencia = _confirmar_captura_con_aro_parcial(
                    det_evento, r45, *argumentos)
                if parcial:
                    segunda = vision.brokie45_confirmar_estado_post(
                        list(pre_fis), list(post_fis), foco_post,
                        intentos=3, pausa_s=0.25,
                        casillas_movimiento=casillas_movimiento, **opciones_blancas)
                    repite, evidencia_segunda = _confirmar_captura_con_aro_parcial(
                        det_evento, segunda, *argumentos)
                    acepta = bool(segunda.get('ok') or repite)
                    _diag_vision(
                        'revalidacion_captura_aro_parcial', jugada=mv,
                        aceptada=acepta, primera=evidencia,
                        segunda=evidencia_segunda, post=segunda)
                    if acepta:
                        _ultima_candidata_vision = None
                        _ultima_candidata_ts = 0.0
                        _diag_vision(
                            'confirmacion_ok', jugada=mv,
                            metodo='captura con aro parcial revalidada',
                            foco=foco_post, detalle={
                                'primera': evidencia, 'segunda': evidencia_segunda})
                        return True, 'captura confirmada con evidencia parcial revalidada'

            _ultima_candidata_vision = None
            _ultima_candidata_ts = 0.0
            if r45.get('contradiccion'):
                return False, 'estado POST contradice la jugada'
            return False, 'estado POST inconcluso; conservo PRE y vuelvo a mirar'

        except Exception as e:
            _bit(
                'vision',
                'fallo confirmacion estado POST 4.0G.4',
                error=str(e)[:180]
            )
            # Un fallo del verificador no equivale a una segunda evidencia.
            # Se conserva PRE y se exige un evento nuevo.
            return False, 'falló la confirmación POST; conservo PRE y vuelvo a mirar'

    # Metodo fuerte: leer el tablero completo y exigir coincidencia con la
    # posicion POST-jugada. Esto mata el caso "paso la mano y adelanta" porque
    # la mano no cambia las piezas que el consenso ve en forma estable.
    if getattr(vision, 'USAR_ABSOLUTOS', False):
        try:
            r, err = vision.consenso(ocupadas_esperadas)
            if r is not None:
                if r.get('coincide'):
                    _ultima_candidata_vision = None
                    _ultima_candidata_ts = 0.0
                    _diag_vision('confirmacion_ok', jugada=mv,
                                 metodo='consenso absoluto',
                                 esperado=ocupadas_esperadas)
                    return True, 'consenso absoluto coincide con estado posterior'
                _diag_vision('confirmacion_falla', jugada=mv,
                             motivo='consenso no coincide',
                             esperado=ocupadas_esperadas,
                             consenso=r)
                return False, 'consenso no coincide con estado posterior'
        except Exception as e:
            _bit('vision', 'fallo consenso durante confirmacion', error=str(e))

    return False, 'sin confirmación física independiente; conservo PRE'


def _fijar_ancla_vision_desde_tablero():
    """Actualiza el ancla solo cuando sabemos que el tablero esta estable."""
    global _ancla_vision_fisica
    _ancla_vision_fisica = _fisicas_de_tablero(tablero)


@_serializar_partida
def _al_detectar_jugada():
    """Procesa un cambio de vision como jugada SOLO si cuadra con el ancla.

    Antes el disparador de vision podia llegar por una mano que simplemente
    pasaba por encima. Ahora el orden es:
      1) detectar candidata;
      2) tomar el candado de partida;
      3) comprobar que sigue siendo legal;
      4) comprobar el ESTADO POST-JUGADA contra el ancla fisica;
      5) recien ahi cambiar el tablero logico y dejar que BROKIE responda.
    """
    global falla_vision, aviso_ilegal, _ancla_vision_fisica, _firma_notificada_40
    global ilegal_pendiente

    if ilegal_pendiente:
        _comprobar_restauracion_ilegal()
        return

    if jugada_brokie_manual:
        _bit('vision', 'ignoro callback: espero colocacion manual de BROKIE',
             jugada=jugada_brokie_manual.get('jugada'))
        return

    if _bloqueo_jugada_humana():
        return
    mv, det = _deducir_con_camara()

    if not mv and (det or {}).get('reintento_pose'):
        # La vigilancia ya quedó rearmada y verificará HOME nuevamente.
        # No presentar esta falta de lectura como una jugada fallida.
        falla_vision = None
        _firma_notificada_40 = None
        return

    # BROKIE 4.0G.4.7.2.1:
    # cualquier jugada física reconstruida corta la secuencia de
    # eventos huérfanos unitarios. Así una anomalía vieja no puede
    # contaminar un evento posterior.
    if mv:
        globals()['_g472_huerfana_sq'] = None
        globals()['_g472_huerfana_n'] = 0
        globals()['_g472_huerfana_ts'] = 0.0

    # BROKIE 4.0 — retorno ILEGAL/DUDOSO siempre vuelve a MIRANDO.
    # La misma firma se avisa UNA sola vez. No se renueva referencia y no
    # volvemos a molestar cada 3 s hasta que cambie el conjunto observado.
    firma40 = frozenset(
        str(x).upper() for x in ((det or {}).get('cambiadas') or [])
    )
    estado40 = (det or {}).get('estado_40')
    if not mv and estado40 in ('ILEGAL', 'DUDOSO', 'VOLVER_A_MIRAR'):
        if firma40 and firma40 == _firma_notificada_40:
            _bit('vision', 'BROKIE 4.0G: misma firma pendiente; sigo mirando en silencio',
                 estado=estado40, casillas=sorted(firma40))
            return
        _firma_notificada_40 = firma40 if firma40 else None
    elif firma40 != (_firma_notificada_40 or frozenset()):
        # Cualquier cambio real de firma habilita un nuevo aviso/evaluación.
        _firma_notificada_40 = None

    if not mv:
        if (det or {}).get('estado_40') == 'REFERENCIA_GEOMETRICA_INVALIDA':
            _bit('vision',
                 'BROKIE 4.1.0: referencia geometrica INVALIDA; no comparo',
                 detalle=(det or {}).get('geometria'))
        # V03.8: vision ya comprobo con evidencia fuerte que no hubo cambio
        # de ocupacion y renovo LOCALMENTE la referencia. No es error, no es
        # ilegal y el HTML no debe enterarse.
        if (det or {}).get('autoreferencia'):
            _limpiar_falla()
            _limpiar_aviso_ilegal()
            _bit('vision',
                 'variacion interna de pieza absorbida sin cambiar FEN',
                 cambiadas=(det or {}).get('cambiadas'),
                 fen=tablero.fen())
            return

        if (det or {}).get('promocion'):
            base = det.get('pide_promocion')
            falla_vision = {'promocion': base, 'hora': time.strftime('%H:%M:%S'),
                            'cambiadas': det.get('cambiadas'),
                            'motivo': 'el peon corona: elegi la pieza'}
            _bit('partida', f'peon corona en {base}: espero que elija la pieza')
            return

        if (det or {}).get('estado_40') == 'ILEGAL' or (det or {}).get('ilegal_fisica'):
            _armar_ilegal_pendiente(det)
            return

        # BROKIE 4.0G.4.5 — SALIDA SEGURA PARA EVENTO SIN ORIGEN.
        #
        # Caso real observado: una jugada fisicamente invalida puede dejar
        # una sola casilla persistente en la firma final. La geometria detecta
        # que hubo un cambio, pero no puede reconstruir un origen completo.
        # Antes este caso caia en falla_vision generica y quedaba eternamente
        # en "esperando".
        #
        # No inventamos ninguna jugada ni origen/destino. Conservamos solamente
        # las casillas observadas y abrimos la recuperacion al PRE.
        _mot_sin = str((det or {}).get('motivo') or '').lower()
        _camb_sin = list((det or {}).get('cambiadas') or [])

        if (
            _camb_sin
            and 'el evento no permite reconstruir un origen físico' in _mot_sin
        ):
            det_rec = dict(det or {})
            det_rec['motivo'] = (
                'cambio fisico incompleto: no se pudo reconstruir el origen; '
                'restaure la posicion PRE'
            )
            det_rec['movimiento_fisico'] = None
            det_rec['movimiento_fisico_detectado'] = None

            # BROKIE 4.0G.4.7.2 — EVENTO HUERFANO UNITARIO.
            #
            # Una firma final de UNA sola casilla, sin origen físico
            # reconstruible, no tiene evidencia suficiente para abrir de
            # inmediato una recuperación ilegal sobre todo el PRE.
            #
            # Seguridad:
            # - NO acepta jugada;
            # - NO cambia FEN;
            # - NO cambia ancla;
            # - NO toma referencia;
            # - descarta solamente este evento incompleto.
            #
            # Si el cambio físico es real y persiste, la vigilancia contra el
            # mismo PRE lo volverá a observar.
            if len(_camb_sin) == 1:
                # BROKIE 4.0G.4.7.2.1
                #
                # Una aparición aislada obtiene UNA sola oportunidad de
                # desaparecer como ruido. Si la MISMA casilla vuelve como
                # evento huérfano dentro de 20 s, ya es persistente y cae
                # al flujo G4.5 seguro que está debajo.
                _sq472 = str(_camb_sin[0]).upper()
                _ahora472 = time.time()

                _prev_sq472 = globals().get('_g472_huerfana_sq')
                _prev_n472 = int(globals().get('_g472_huerfana_n', 0) or 0)
                _prev_ts472 = float(
                    globals().get('_g472_huerfana_ts', 0.0) or 0.0
                )

                _misma472 = (
                    _prev_sq472 == _sq472
                    and (_ahora472 - _prev_ts472) <= 20.0
                )

                if _misma472:
                    _n472 = _prev_n472 + 1
                else:
                    _n472 = 1

                globals()['_g472_huerfana_sq'] = _sq472
                globals()['_g472_huerfana_n'] = _n472
                globals()['_g472_huerfana_ts'] = _ahora472

                if _n472 == 1:
                    _bit(
                        'vision',
                        'BROKIE 4.0G.4.7.2.1: primer evento huerfano '
                        'unitario; conservo PRE y vuelvo a mirar',
                        casilla=_sq472,
                        ventana_s=20.0,
                    )

                    try:
                        if hasattr(vision, 'brokie42_limpiar_evento'):
                            vision.brokie42_limpiar_evento()
                    except Exception:
                        pass

                    falla_vision = None
                    aviso_ilegal = None
                    _firma_notificada_40 = None
                    return

                # Segunda aparición consecutiva: NO ocultarla.
                # Dejamos continuar hacia el G4.5 existente.
                _bit(
                    'vision',
                    'BROKIE 4.0G.4.7.2.1: evento huerfano unitario '
                    'PERSISTENTE; escalo a recuperacion segura',
                    casilla=_sq472,
                    repeticiones=_n472,
                )

                globals()['_g472_huerfana_sq'] = None
                globals()['_g472_huerfana_n'] = 0
                globals()['_g472_huerfana_ts'] = 0.0

            # Firma sin origen de DOS O MAS casillas, o huérfana unitaria
            # confirmada por repetición:
            # conserva el comportamiento seguro G4.5 anterior.
            #
            # No conocemos el origen perdido. Para demostrar restauración
            # usamos todas las casillas que estaban OCUPADAS en el PRE
            # más las casillas realmente observadas en el evento.
            # Así no alcanza con retirar la pieza del destino: también debe
            # reaparecer correctamente en su posición PRE.
            foco_rec = sorted({
                str(x).upper()
                for x in (
                    list(_ancla_vision_fisica or [])
                    + list(_camb_sin)
                )
                if len(str(x)) == 2
            })

            det_rec['casillas_recuperacion'] = foco_rec

            _bit(
                'vision',
                'BROKIE 4.0G.4.5: evento sin origen pasa a recuperacion ilegal',
                cambiadas=_camb_sin,
            )

            _armar_ilegal_pendiente(det_rec)
            return

        falla_vision = {
            'sugerencia_humana': (det or {}).get('sugerencia_humana'),
            'fen_sugerencia': (det or {}).get('fen_sugerencia'),
            'cambiadas': (det or {}).get('cambiadas'),
            'motivo': (det or {}).get('motivo'),
            'filtro_ocupacion_post': (det or {}).get('filtro_ocupacion_post'),
            'mapa_camara_touch': {
                sq: sq_fisico(sq) for sq in
                (((det or {}).get('filtro_ocupacion_post') or {}).get('estados') or {})
            },
            'candidatas': ((det or {}).get('candidatas')
                           or (det or {}).get('candidatas_fisicas')),
            'requiere_confirmacion': bool(
                (det or {}).get('intervencion_requerida')
                or (det or {}).get('estado_40') == 'DUDOSO'),
            'hora': time.strftime('%H:%M:%S')}
        _diag_vision('sin_jugada',
                     cambiadas=(det or {}).get('cambiadas'),
                     motivo=(det or {}).get('motivo'),
                     candidatas=(det or {}).get('candidatas'))

        # V03.6: esto SOLO alimenta el cartel del tactil. No pausa, no bloquea,
        # no toma referencia y no crea una maquina de recuperacion paralela.
        _mot = str((det or {}).get('motivo') or '').lower()
        _camb = (det or {}).get('cambiadas') or []
        if _camb and (
                (det or {}).get('estado_40') == 'ILEGAL'
                or 'transicion fisica incompatible' in _mot
                or 'no corresponden a la transicion de ninguna candidata' in _mot):
            aviso_ilegal = {
                'hora': time.strftime('%H:%M:%S'),
                'cambiadas': list(_camb),
                'motivo': (det or {}).get('motivo')}

        _bit('vision', 'cambio detectado pero NO se pudo deducir la jugada',
             cambiadas=(det or {}).get('cambiadas'),
             motivo=(det or {}).get('motivo'),
             candidatas=(det or {}).get('candidatas'),
             juegan=('blancas' if tablero.turn == chess.WHITE else 'negras'),
             fen=tablero.board_fen())
        return

    with _lock_partida:
        try:
            jugada = chess.Move.from_uci(mv)
        except Exception as e:
            _bit('vision', f'jugada mal formada {mv}: {e}')
            return

        # Carrera con la pantalla tactil: la jugada ya no pertenece al estado
        # actual. No se acepta ni se usa para mover el brazo.
        if jugada not in tablero.legal_moves:
            _bit('vision', f'{mv} ya no es legal, la descarto '
                  '(el jugador movio desde la pantalla)')
            # BROKIE 4.0: una deducción descartada NO concede permiso
            # para renovar referencia. Se conserva el PRE y se vuelve a mirar.
            return

        # BROKIE 4.0G.4.7.1 — el confirmador necesita también la
        # evidencia/firma del evento que produjo esta candidata.
        ok_conf, motivo_conf = _confirmar_jugada_vision(mv, det)
        if not ok_conf:
            # CLAVE: no hacemos push, no respondemos y NO actualizamos el ancla.
            # El siguiente cambio se seguira comparando contra la misma
            # posicion conocida. Una mano que paso no puede adelantar la partida.
            # Confirmación humana explícita: la candidata sigue siendo legal,
            # pero el POST visual no la respalda. Reusar el botón del touch;
            # no aceptar automáticamente ni ofrecerlo ante PRE/FEN caducado,
            # falta de ancla, error de cámara o excepción del verificador.
            sugerir_post = motivo_conf in (
                'estado POST contradice la jugada',
                'estado POST inconcluso; conservo PRE y vuelvo a mirar',
            )
            falla_vision = {
                'candidatas': [mv],
                'sugerencia_humana': mv if sugerir_post else None,
                'fen_sugerencia': tablero.fen() if sugerir_post else None,
                'motivo': 'cambio no confirmado contra el estado del tablero',
                'detalle': motivo_conf,
                'requiere_confirmacion': bool(sugerir_post or
                    (det or {}).get('conflicto_patron_fisico')),
                'hora': time.strftime('%H:%M:%S')}
            if sugerir_post:
                _bit('vision', 'POST: candidata ofrecida a confirmacion humana',
                     jugada=mv, motivo=motivo_conf, fen=tablero.fen())
            _diag_vision('candidata_rechazada',
                         jugada=mv,
                         motivo=motivo_conf,
                         ancla=_ancla_vision_fisica)
            _bit('vision', 'candidata IGNORADA: no coincide con el ancla',
                 jugada=mv, motivo=motivo_conf,
                 ancla=_ancla_vision_fisica)
            return

        try:
            _aplicar_jugada_humana(jugada, 'camara')
            _firma_notificada_40 = None
            _limpiar_falla()
            _limpiar_aviso_ilegal()
            # Desde este instante la posicion aceptada pasa a ser el ancla.
            # BROKIE luego respondera y _refrescar_vision la volvera a fijar
            # despues de que el brazo llegue a home.
            _fijar_ancla_vision_desde_tablero()
            _bit('partida', f'jugada del humano por camara: {mv}',
                 fisico=(det or {}).get('fisico'))
            r = _jugar_motor(vision_con_brazo)
            b = (r or {}).get('brazo') or {}
            if b and not b.get('ok'):
                _bit('brazo', 'ATENCION: el brazo no pudo ejecutar la respuesta '
                     f"{r.get('respuesta_engine')}", detalle=b.get('detalle'))
        except Exception as e:
            _bit('vision', f'error aplicando {mv}', error=str(e))


@app.route('/vision/vigilar', methods=['POST'])
@_serializar_partida
def vision_vigilar():
    """Modo automatico: la camara mira el tablero y detecta sola cuando el
    humano termino de mover. POST {'activo': true, 'brazo': true}."""
    if vision is None:
        return jsonify({'ok': False, 'error': 'vision.py no esta instalado'})
    global vision_con_brazo
    data = request.get_json(silent=True) or {}
    if 'brazo' in data:
        vision_con_brazo = False if MODO_PRUEBA_SIN_BRAZO else bool(data['brazo'])
    global vision_activa
    if data.get('activo'):
        # Iniciar una partida tiene prioridad absoluta sobre una pestaña de
        # encuadre que hubiera quedado abierta. Evita que su concesión breve
        # de mantenimiento bloquee la primera jugada física.
        _cerrar_ajuste_home()
        ok, det = vision.tomar_referencia()
        if not ok:
            return jsonify({'ok': False, 'error': det})
        _fijar_ancla_vision_desde_tablero()
        ok, det = vision.iniciar_vigilancia(callback=_al_detectar_jugada)
        if ok:
            vision_activa = True
            guardar_calibracion()
        return jsonify({'ok': ok, 'detalle': det, 'brazo': vision_con_brazo})
    vision.detener_vigilancia()
    vision_activa = False
    guardar_calibracion()
    return jsonify({'ok': True, 'detalle': 'vigilancia detenida'})


@app.route('/log')
def ver_log():
    """Eventos registrados. ?n= cuantos  ?cat=vision,brazo  ?desde=n"""
    if bitacora is None:
        return jsonify({'ok': False, 'error': 'bitacora.py no esta instalado'})
    try:
        n = int(request.args.get('n', 120))
    except ValueError:
        n = 120
    desde = request.args.get('desde')
    try:
        desde = int(desde) if desde else None
    except ValueError:
        return jsonify({'ok': False, 'error': 'desde debe ser un entero'}), 400
    return jsonify({'ok': True,
                    'eventos': bitacora.leer(n=n, cat=request.args.get('cat'),
                                             desde=desde, partida=request.args.get('partida')),
                    'estado': bitacora.estado()})


@app.route('/log/resumen')
def ver_log_resumen():
    if bitacora is None:
        return jsonify({'ok': False, 'error': 'bitacora.py no esta instalado'})
    return jsonify({'ok': True, 'resumen': bitacora.resumen()})


@app.route('/log/limpiar', methods=['POST'])
def limpiar_log():
    if bitacora is None:
        return jsonify({'ok': False, 'error': 'bitacora.py no esta instalado'})
    bitacora.limpiar()
    return jsonify({'ok': True})


@app.route('/log/ver')
def pagina_log():
    if bitacora is None:
        return 'bitacora.py no esta instalado', 503
    from flask import render_template_string
    return render_template_string(bitacora.PAGINA)


@app.route('/tactil')
def pagina_tactil():
    """Interfaz compacta para la pantalla tactil de 3.5 pulgadas (480x320).
    Solo lo que necesita el jugador: tablero, nivel, color y partida."""
    return render_template('tactil.html')


def _bloqueo_camara_web():
    """Impide que una pestaña de mantenimiento saltee la pausa física."""
    permitida, motivo, restante = _mediciones_permitidas()
    ajuste_home = bool(getattr(_captura_mantenimiento_ctx,
                               'ajuste_home', False))
    if permitida and vision is not None and not ajuste_home:
        pausa = getattr(vision, '_motivo_pausa', None)
        if pausa in ('brazo', 'enroque', 'refrescando_referencia'):
            permitida, motivo = False, pausa
    if permitida:
        return None
    return (jsonify({
        'ok': False,
        'error': 'captura suspendida mientras BROKIE mueve o estabiliza',
        'motivo': motivo,
        'reintentar_en_s': round(restante, 2),
    }), 423)


@app.route('/vision/foto_cruda')
def vision_foto_cruda():
    if vision is None:
        return jsonify({'ok': False, 'error': 'vision no disponible'}), 503
    ajuste_home = request.args.get('ajuste_home') in ('1', 'true', 'si')
    if ajuste_home and not _ajuste_home_activo():
        # Una pestaña en segundo plano puede sufrir throttling del navegador y
        # dejar vencer la concesión aunque siga abierta. Se recupera sola sólo
        # si no existe vigilancia de partida ni un movimiento físico en curso.
        if vision.vigilando:
            return jsonify({'ok': False,
                            'error': 'la cámara de partida está activa'}), 409
        with _gy302_lock:
            if _luz_movimientos:
                return jsonify({'ok': False,
                                'error': 'brazo en movimiento'}), 423
        _renovar_ajuste_home()
    if ajuste_home:
        _renovar_ajuste_home()
        _captura_mantenimiento_ctx.ajuste_home = True
    try:
        bloqueo = _bloqueo_camara_web()
        if bloqueo is not None:
            return bloqueo
        datos, err = vision.foto_cruda_jpeg()
        if datos is None:
            return jsonify({'ok': False, 'error': err}), 503
        return Response(datos, mimetype='image/jpeg',
                        headers={'Cache-Control': 'no-store'})
    finally:
        if ajuste_home:
            _captura_mantenimiento_ctx.ajuste_home = False


@app.route('/vision/ajuste_home', methods=['GET', 'POST'])
def vision_ajuste_home():
    """Concesión breve para ver imagen cruda mientras se redefine HOME."""
    if request.method == 'GET':
        return jsonify({'ok': True, 'activo': _ajuste_home_activo()})
    data = request.get_json(silent=True) or {}
    activo = bool(data.get('activo', True))
    if not activo:
        _cerrar_ajuste_home()
        return jsonify({'ok': True, 'activo': False})
    if vision is not None and vision.vigilando:
        return jsonify({
            'ok': False,
            'error': ('Desactivá la cámara de partida antes de ajustar HOME; '
                      'la vista cruda no puede convivir con la vigilancia.'),
        }), 409
    with _gy302_lock:
        if _luz_movimientos:
            return jsonify({'ok': False,
                            'error': 'Esperá a que termine el movimiento'}), 409
    _renovar_ajuste_home()
    return jsonify({'ok': True, 'activo': True,
                    'vence_sin_actividad_s': 60.0})


@app.route('/vision/encuadre')
def vision_encuadre():
    """Mantenimiento: imagen anterior a la geometría, sin iniciar vigilancia."""
    from flask import render_template_string
    return render_template_string('''<!doctype html>
<html lang="es"><meta charset="utf-8"><meta name="viewport" content="width=device-width">
<title>Encuadre de cámara</title>
<style>body{background:#111;color:#eee;font:18px sans-serif;text-align:center}
img{max-width:100%;max-height:78vh}button{padding:12px;margin:8px}</style>
<h2>Encuadre de cámara</h2>
<p>Vista sin calibración para ajustar la cámara y redefinir HOME.</p>
<button id="capturar">Actualizar imagen</button>
<label><input id="auto" type="checkbox" checked>Actualizar automáticamente</label>
<p id="estado" role="status"></p><img id="foto" alt="Imagen de la cámara">
<script>
let ocupada=false, urlAnterior=null, modoHome=false;
async function iniciar(){
 try{
  const r=await fetch('/vision/ajuste_home',{method:'POST',headers:{'Content-Type':'application/json'},body:'{"activo":true}'});
  const d=await r.json();
  if(!r.ok||!d.ok)throw new Error(d.error||'No se pudo iniciar');
  modoHome=true; actualizar();
 }catch(e){document.getElementById('estado').textContent=e.message;}
}
async function actualizar(){
 if(ocupada||!modoHome)return; ocupada=true;
 const estado=document.getElementById('estado');
 estado.textContent='Capturando…';
 try{
  const r=await fetch('/vision/foto_cruda?ajuste_home=1&t='+Date.now(),{cache:'no-store'});
  if(!r.ok){const d=await r.json();throw new Error(d.error||'Error de captura');}
  const url=URL.createObjectURL(await r.blob());
  document.getElementById('foto').src=url;
  if(urlAnterior)URL.revokeObjectURL(urlAnterior); urlAnterior=url;
  estado.textContent='Imagen actualizada. Esta vista no modifica la calibración.';
 }catch(e){estado.textContent='No se pudo obtener imagen: '+e.message;}
 finally{ocupada=false;}
}
document.getElementById('capturar').onclick=actualizar;
setInterval(()=>{if(document.getElementById('auto').checked)actualizar();},1500);
addEventListener('beforeunload',()=>{navigator.sendBeacon('/vision/ajuste_home',new Blob(['{"activo":false}'],{type:'application/json'}));});
iniciar();
</script></html>''')


@app.route('/vision/foto')
def vision_foto():
    """Imagen en vivo de la camara. ?grilla=1 dibuja las 64 casillas encima,
    para verificar el encuadre y la calibracion a ojo."""
    if vision is None:
        return jsonify({'ok': False, 'error': 'vision.py no esta instalado'}), 503
    bloqueo = _bloqueo_camara_web()
    if bloqueo is not None:
        return bloqueo
    con_grilla = request.args.get('grilla') in ('1', 'true', 'si')
    datos, err = vision.foto_jpeg(con_grilla=con_grilla)
    if datos is None:
        return jsonify({'ok': False, 'error': err}), 503
    return Response(datos, mimetype='image/jpeg',
                    headers={'Cache-Control': 'no-store'})


@app.route('/vision/ver')
def vision_ver():
    """Pagina para encuadrar y calibrar la camara a mano."""
    from flask import render_template_string
    return render_template_string("""
<!DOCTYPE html><html><head><meta charset="utf-8"><title>Camara BROKIE</title>
<meta name="viewport" content="width=device-width, initial-scale=1">
<style>
body{background:#111;color:#ddd;font-family:Arial;text-align:center;margin:0;padding:10px}
#wrap{position:relative;display:inline-block;max-width:100%}
img{max-width:100%;display:block;border:2px solid #444;border-radius:6px}
#wrap.marcando img{cursor:crosshair;border-color:#f59e0b}
button{padding:8px 14px;margin:3px;border:none;border-radius:5px;cursor:pointer;font-weight:bold}
.v{background:#44cf6c}.g{background:#2563eb;color:#fff}.r{background:#374151;color:#fff}
.o{background:#f59e0b;color:#000}.a{background:#7c3aed;color:#fff}
#ctrl{display:flex;gap:14px;flex-wrap:wrap;justify-content:center;margin:10px 0;
      background:#181828;border-radius:8px;padding:10px 14px}
.sl{display:flex;flex-direction:column;align-items:center;font-size:11px;color:#9aa}
.sl input{width:130px;accent-color:#44cf6c}
.sl b{color:#ddd;font-size:13px}
.sl .val{color:#44cf6c;font-weight:bold}
#wrap.ajustando img{cursor:crosshair;border-color:#7c3aed}
#ctrl{display:none;max-width:520px;margin:10px auto;background:#1a1a2e;
      border-radius:8px;padding:10px 14px;text-align:left}
#ctrl.v{display:block}
.cf{display:flex;align-items:center;gap:8px;margin:6px 0}
.cf label{width:80px;font-size:.8rem;color:#aab}
.cf input[type=range]{flex:1}
.cf span{width:38px;text-align:right;font-size:.8rem;color:#fde68a;font-weight:bold}
.cf button{padding:3px 8px;font-size:.7rem;margin:0}
.ay{font-size:.72rem;color:#889;margin-top:8px;line-height:1.35}
#info{font-size:.82rem;color:#aaa;margin-top:10px;min-height:2.4em;line-height:1.4}
#paso{font-size:1.1rem;font-weight:bold;color:#fde68a;margin:8px 0;min-height:1.3em}
.pt{position:absolute;width:14px;height:14px;margin:-7px 0 0 -7px;border-radius:50%;
    background:#f59e0b;border:2px solid #fff;pointer-events:none}
.pt span{position:absolute;top:14px;left:-6px;font-size:.75rem;color:#fde68a;font-weight:bold}
</style></head><body>
<h3>Camara BROKIE</h3>
<p><a href="/vision/encuadre" style="color:#44cf6c">Ajustar encuadre sin calibración</a></p>
<div>
 <button class="v" onclick="grilla=0;ver()">Imagen</button>
 <button class="g" onclick="grilla=1;ver()">Con grilla</button>
 <button class="r" onclick="auto=!auto;document.getElementById('a').textContent=auto?'ON':'OFF'">
   Auto: <span id="a">OFF</span></button>
 <button class="r" onclick="calibrar()">Autocalibrar</button>
 <button class="o" onclick="marcar()">Marcar esquinas a mano</button>
 <button class="v" onclick="testLateralesNegros()">TEST laterales negros</button>
 <button class="v" onclick="test4BordesNegros('blancas_arriba')">TEST 4 bordes negros, blancas arriba</button>
 <button class="v" onclick="test4BordesNegros('blancas_abajo')">TEST 4 bordes negros, blancas abajo</button>
 <button class="a" onclick="ajustar()">Acomodar casillas</button>
 <button class="v" onclick="roiSimetricas()">ROI simétricas</button>
 <button class="r" onclick="cambiarVentana(-0.03)">Casillas +</button>
 <button class="r" onclick="cambiarVentana(0.03)">Casillas &minus;</button>
 <button class="r" onclick="verCtrl()">Imagen de la c&#225;mara</button>
</div>
<div id="ctrl">
  <div class="cf"><label>Brillo</label><input type="range" id="c-brillo" min="0" max="100"
      oninput="mostrar('brillo')" onchange="aplicar('brillo')"><span id="v-brillo">--</span>
      <button class="r" onclick="reset('brillo')">auto</button></div>
  <div class="cf"><label>Contraste</label><input type="range" id="c-contraste" min="0" max="100"
      oninput="mostrar('contraste')" onchange="aplicar('contraste')"><span id="v-contraste">--</span>
      <button class="r" onclick="reset('contraste')">auto</button></div>
  <div class="cf"><label>Gamma</label><input type="range" id="c-gamma" min="0" max="100"
      oninput="mostrar('gamma')" onchange="aplicar('gamma')"><span id="v-gamma">--</span>
      <button class="r" onclick="reset('gamma')">auto</button></div>
  <div class="cf"><label>Ganancia</label><input type="range" id="c-ganancia" min="0" max="100"
      oninput="mostrar('ganancia')" onchange="aplicar('ganancia')"><span id="v-ganancia">--</span>
      <button class="r" onclick="reset('ganancia')">auto</button></div>
  <div class="cf"><label>Nitidez</label><input type="range" id="c-nitidez" min="0" max="100"
      oninput="mostrar('nitidez')" onchange="aplicar('nitidez')"><span id="v-nitidez">--</span>
      <button class="r" onclick="reset('nitidez')">auto</button></div>
  <div class="ay">Cada cambio se aplica en la c&#225;mara y refresca la imagen.
   <b>auto</b> devuelve ese control al valor de f&#225;brica.</div>
</div>
<div id="ctrl">
  <div class="sl"><b>Brillo</b>
    <input type="range" id="s-brillo" min="0" max="100" value="50"
           oninput="verVal('brillo',this.value)" onchange="setCam('brillo',this.value)">
    <span class="val" id="v-brillo">fábrica</span></div>
  <div class="sl"><b>Contraste</b>
    <input type="range" id="s-contraste" min="0" max="100" value="50"
           oninput="verVal('contraste',this.value)" onchange="setCam('contraste',this.value)">
    <span class="val" id="v-contraste">fábrica</span></div>
  <div class="sl"><b>Gamma</b>
    <input type="range" id="s-gamma" min="0" max="100" value="50"
           oninput="verVal('gamma',this.value)" onchange="setCam('gamma',this.value)">
    <span class="val" id="v-gamma">fábrica</span></div>
  <div class="sl"><b>Ganancia</b>
    <input type="range" id="s-ganancia" min="0" max="100" value="50"
           oninput="verVal('ganancia',this.value)" onchange="setCam('ganancia',this.value)">
    <span class="val" id="v-ganancia">fábrica</span></div>
  <div class="sl"><b>&nbsp;</b>
    <button class="r" onclick="camFabrica()">Volver a fábrica</button>
    <span class="val" id="v-cam"></span></div>
</div>
<div id="paso"></div>
<div id="wrap"><img id="im" src="/vision/foto"></div>
<div id="info">Si la grilla no cae en el centro de las casillas, usa
 <b>Marcar esquinas a mano</b>: se tocan las 4 esquinas del area de juego.</div>
<script>
let grilla=0, auto=false, marcando=false, pts=[], orden=['A1','H1','A8','H8'];
let ajustando=false, sqSel=null;
const guia={A1:'esquina de A1 (cerca del brazo, izquierda)',
            H1:'esquina de H1 (cerca del brazo, derecha)',
            A8:'esquina de A8 (lejos, izquierda)',
            H8:'esquina de H8 (lejos, derecha)'};
const im=document.getElementById('im'), wrap=document.getElementById('wrap');
function ver(){ im.src='/vision/foto?grilla='+grilla+'&t='+Date.now(); }
/* Controles de camara. Con iluminacion infrarroja la escena puede quedar
   quemada: bajando brillo y ganancia, y subiendo contraste y gamma, se
   recupera el detalle sin tocar el hardware. */
function verVal(k,v){ document.getElementById('v-'+k).textContent=v+'%'; }
function setCam(k,v){
  const b={}; b[k]=parseInt(v);
  fetch('/vision/ajustes',{method:'POST',headers:{'Content-Type':'application/json'},
    body:JSON.stringify(b)}).then(r=>r.json()).then(d=>{
      if(!d.ok){ info('<b style="color:#f87171">'+d.error+'</b>'); return; }
      document.getElementById('v-cam').textContent='aplicado';
      setTimeout(ver,350); }); }
function camFabrica(){
  fetch('/vision/ajustes',{method:'POST',headers:{'Content-Type':'application/json'},
    body:JSON.stringify({brillo:null,contraste:null,gamma:null,ganancia:null})})
  .then(r=>r.json()).then(()=>{
    ['brillo','contraste','gamma','ganancia'].forEach(k=>{
      document.getElementById('v-'+k).textContent='fábrica';
      document.getElementById('s-'+k).value=50; });
    document.getElementById('v-cam').textContent='';
    setTimeout(ver,350); }); }
fetch('/vision/ajustes').then(r=>r.json()).then(d=>{
  const c=d.controles||{};
  Object.keys(c).forEach(k=>{
    if(c[k]!=null){ document.getElementById('s-'+k).value=c[k];
                    document.getElementById('v-'+k).textContent=c[k]+'%'; } }); });
function test4BordesNegros(orientacion){
  const etiqueta = orientacion==='blancas_arriba' ? 'BLANCAS ARRIBA' : 'BLANCAS ABAJO';
  grilla=0;
  im.src='/vision/4-bordes-negros-debug?orientacion='+encodeURIComponent(orientacion)+'&t='+Date.now();
  info('<b>TEST 4 BORDES NEGROS — '+etiqueta+'</b>: rojo=izq, verde=der, '
      +'cyan=superior, magenta=inferior, blanco=esquinas, amarillo=geometría actual. '
      +'NO cambia calibración.');
  fetch('/vision/4-bordes-negros-info?orientacion='+encodeURIComponent(orientacion)+'&t='+Date.now())
    .then(r=>r.json()).then(d=>{
      if(d.ok){
        const x=d.detalle||{};
        info('<b>TEST 4 BORDES — '+etiqueta+'</b> — '
            +'4 bordes OK: '+(x.cuatro_bordes_ok?'SÍ':'NO')
            +' — '+JSON.stringify(x.fusion||{})
            +' — esquinas: '+JSON.stringify(x.esquinas_detectadas||null)
            +'. NO modifica calibración.');
      }
    }).catch(()=>{});
}

function testLateralesNegros(){
  grilla=0;
  im.src='/vision/laterales-negros-debug?t='+Date.now();
  info('<b>TEST LATERALES NEGROS</b>: rojo = borde interior izquierdo; '
      +'verde = borde interior derecho; amarillo = geometría actual. '
      +'NO cambia la calibración.');
  fetch('/vision/laterales-negros-info?t='+Date.now()).then(r=>r.json()).then(d=>{
    if(d.ok){
      const x=d.detalle||{};
      info('<b>TEST LATERALES NEGROS</b> — '
          +'IZQ '+JSON.stringify(x.izquierda)+' / DER '+JSON.stringify(x.derecha)
          +'. NO modifica calibración.');
    }
  }).catch(()=>{});
}

function info(t){ document.getElementById('info').innerHTML=t; }
function paso(t){ document.getElementById('paso').textContent=t; }
function limpiar(){ wrap.querySelectorAll('.pt').forEach(e=>e.remove()); }
function ajustar(){
  ajustando=true; marcando=false; auto=false; sqSel=null; grilla=1; limpiar(); ver();
  wrap.classList.add('ajustando');
  paso('Toca la casilla que esta corrida');
  info('Primero tocas la casilla mal ubicada, despues el lugar donde deberia '
      +'estar su centro. Se puede repetir en cuantas casillas haga falta. '
      +'<button class="r" onclick="limpiarAjustes()">Borrar todos los ajustes</button>'); }
const CTRLS=['brillo','contraste','gamma','ganancia','nitidez'];
function verCtrl(){
  const e=document.getElementById('ctrl');
  e.classList.toggle('v');
  if(e.classList.contains('v')) leerCtrl(); }
function leerCtrl(){
  fetch('/vision/ajustes').then(r=>r.json()).then(d=>{
    const c=d.camara||{};
    const map={brillo:'Brightness',contraste:'Contrast',gamma:'Gamma',
               ganancia:'Gain',nitidez:'Sharpness'};
    CTRLS.forEach(k=>{
      const v=c[map[k]];
      document.getElementById('c-'+k).value = (v==null? 50 : v);
      document.getElementById('v-'+k).textContent = (v==null? 'auto' : v); }); }); }
function mostrar(k){
  document.getElementById('v-'+k).textContent=document.getElementById('c-'+k).value; }
function aplicar(k){
  const v=parseInt(document.getElementById('c-'+k).value);
  const b={}; b[k]=v;
  fetch('/vision/ajustes',{method:'POST',headers:{'Content-Type':'application/json'},
    body:JSON.stringify(b)}).then(r=>r.json()).then(d=>{
      if(!d.ok){ info('<b style="color:#f87171">'+d.error+'</b>'); return; }
      info(k+' = '+v+'%. La imagen se actualiza con el valor nuevo.');
      ver(); }); }
function reset(k){
  const b={}; b[k]=null;
  fetch('/vision/ajustes',{method:'POST',headers:{'Content-Type':'application/json'},
    body:JSON.stringify(b)}).then(()=>{ leerCtrl(); info(k+' al valor de fabrica.'); ver(); }); }

function cambiarVentana(d){
  fetch('/vision/ajustes').then(r=>r.json()).then(a=>{
    const m=Math.max(0.02,Math.min(0.40,(a.margen||0.22)+d));
    fetch('/vision/ajustes',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({margen:m})}).then(r=>r.json()).then(x=>{
        if(!x.ok){ info('<b style="color:#f87171">'+x.error+'</b>'); return; }
        info('Ventana de muestreo: '+x.ventana_pct+'% de la casilla ('
            +x.ventana_px+' px). Mas grande = mas señal, pero mas riesgo de '
            +'tomar la sombra de la casilla vecina.');
        grilla=1; ver(); }); }); }
function limpiarAjustes(){
  fetch('/vision/casilla',{method:'POST',headers:{'Content-Type':'application/json'},
    body:JSON.stringify({limpiar:'todo'})}).then(r=>r.json()).then(()=>{
      info('Ajustes borrados.'); ver(); }); }

function roiSimetricas(){
  if(!confirm('Esto borrará TODOS los ajustes individuales de casillas y pondrá las 64 ROI simétricamente desde las 4 esquinas, conservando el tamaño actual. ¿Continuar?'))
    return;
  info('Rehaciendo 64 ROI desde las 4 esquinas...');
  fetch('/vision/roi-simetricas',{method:'POST'})
    .then(r=>r.json()).then(d=>{
      if(!d.ok){
        info('<b style="color:#f87171">FALLO:</b> '+(d.error||'?'));
        return;
      }
      const x=d.detalle||{};
      info('<b style="color:#44cf6c">ROI SIMÉTRICAS ✓</b> '
          +'64 centros rehechos desde A1/H1/A8/H8. '
          +'Tamaño actual: '+(x.diametro_roi_px||'?')+' px de diámetro '
          +'(radio '+(x.radio_px||'?')+' px). '
          +'Ajustes individuales: 0.');
      grilla=1; ver();
    }).catch(()=>{
      info('<b style="color:#f87171">Error de conexión al rehacer ROI.</b>');
    });
}
function nombreDeXY(x,y){
  // pide al servidor que resuelva cual es la casilla mas cercana
  return fetch('/vision/estado').then(r=>r.json()).then(d=>{
    const e=d.esquinas; if(!e||!e.A1) return null;
    // interpolacion inversa aproximada sobre las 4 esquinas
    const a1=e.A1,h1=e.H1,a8=e.A8,h8=e.H8;
    let mej=null,dm=1e9;
    for(let f=0;f<8;f++) for(let c=0;c<8;c++){
      const u=(c+0.5)/8, vv=(f+0.5)/8;
      const px=(1-u)*(1-vv)*a1[0]+u*(1-vv)*h1[0]+(1-u)*vv*a8[0]+u*vv*h8[0];
      const py=(1-u)*(1-vv)*a1[1]+u*(1-vv)*h1[1]+(1-u)*vv*a8[1]+u*vv*h8[1];
      const d2=(px-x)**2+(py-y)**2;
      if(d2<dm){ dm=d2; mej='ABCDEFGH'[c]+(f+1); } }
    return mej; }); }

function marcar(){
  marcando=true; ajustando=false; auto=false; pts=[]; grilla=0; limpiar(); ver();
  wrap.classList.remove('ajustando');
  wrap.classList.add('marcando');
  paso('Toca la '+guia[orden[0]]);
  info('Marca las 4 esquinas del AREA DE JUEGO (el borde de las casillas, '
      +'no el marco de madera). Se puede repetir las veces que haga falta.'); }
wrap.addEventListener('click', ev=>{
  const r0=im.getBoundingClientRect();
  const X=Math.round((ev.clientX-r0.left)*im.naturalWidth/r0.width);
  const Y=Math.round((ev.clientY-r0.top)*im.naturalHeight/r0.height);
  if(ajustando){
    if(!sqSel){
      nombreDeXY(X,Y).then(sq=>{ if(!sq){ info('No hay calibracion.'); return; }
        sqSel=sq; paso('Toca donde deberia estar el centro de '+sq); });
      return; }
    const sq=sqSel; sqSel=null;
    fetch('/vision/casilla',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({sq:sq,x:X,y:Y})}).then(r=>r.json()).then(d=>{
        if(!d.ok){ info('<b style="color:#f87171">'+d.error+'</b>'); }
        else info(sq+' corrida a ['+d.detalle.ajuste.join(', ')+'] px. '
                 +'Toca otra casilla o pasa a Imagen.');
        paso('Toca la casilla que esta corrida'); ver(); });
    return; }
  if(!marcando) return;
  const r=im.getBoundingClientRect();
  const x=Math.round((ev.clientX-r.left)*im.naturalWidth/r.width);
  const y=Math.round((ev.clientY-r.top)*im.naturalHeight/r.height);
  pts.push([x,y]);
  const d=document.createElement('div'); d.className='pt';
  d.style.left=(ev.clientX-r.left+im.offsetLeft)+'px';
  d.style.top=(ev.clientY-r.top+im.offsetTop)+'px';
  d.innerHTML='<span>'+orden[pts.length-1]+'</span>';
  wrap.appendChild(d);
  if(pts.length<4){ paso('Toca la '+guia[orden[pts.length]]); return; }
  marcando=false; wrap.classList.remove('marcando'); paso('');
  const body={}; orden.forEach((k,i)=>body[k]=pts[i]);
  fetch('/vision/esquinas',{method:'POST',headers:{'Content-Type':'application/json'},
        body:JSON.stringify(body)}).then(r=>r.json()).then(d=>{
    if(!d.ok){ info('<b style="color:#f87171">'+d.error+'</b>'); return; }
    info('Esquinas guardadas. Casilla de '+(d.casilla_px||'?')+' px. '
        +'Verifica que los recuadros verdes caigan en el centro.');
    limpiar(); grilla=1; ver(); }); });
function calibrar(){
  info('calibrando...');
  fetch('/vision/autocalibrar',{method:'POST'}).then(r=>r.json()).then(d=>{
    if(d.ok){
      const x=d.detalle||{};
      info('<b style="color:#44cf6c">AUTO CUADRADO ✓</b> '+x.metodo
          +' — 49 cruces internos ajustan UNA homografía global. '
          +'Malla deformable: NO. '
          +'RMS '+(x.rms_49_px??'?')+' px / P95 '+(x.p95_49_px??'?')+' px. '
          +'Ajustes individuales: '+(x.ajustes_individuales??0)+'.');
    }else{
      info('<b style="color:#f87171">FALLO:</b> '+JSON.stringify(d.detalle));
    }
    grilla=1; ver(); }); }
setInterval(()=>{ if(auto && !marcando) ver(); }, 1500);
</script></body></html>""")



@app.route('/vision/roi-simetricas', methods=['POST'])
def vision_roi_simetricas():
    """Rehace las 64 ROI desde las 4 esquinas con el tamaño actual."""
    if vision is None:
        return jsonify({'ok': False, 'error': 'vision.py no esta instalado'})
    if not hasattr(vision, 'roi_simetricas_desde_esquinas'):
        return jsonify({'ok': False,
                        'error': 'vision.py no tiene roi_simetricas_desde_esquinas'}), 409

    ok, det = vision.roi_simetricas_desde_esquinas()
    if not ok:
        return jsonify({'ok': False, 'error': det}), 409

    _bit('vision', '64 ROI rehechas simetricamente desde 4 esquinas',
         radio=det.get('radio_px'),
         margen=det.get('margen'),
         ajustes=det.get('ajustes_individuales'))
    return jsonify({'ok': True, 'detalle': det})



@app.route('/vision/casilla', methods=['POST'])
def vision_casilla():
    """Corre el centro de UNA casilla, sin rehacer toda la calibracion.
    POST {'sq':'E4','x':600,'y':500}   posicion absoluta en pixeles
    POST {'sq':'E4','dx':6,'dy':-3}    corrimiento relativo
    POST {'limpiar':'E4'} | {'limpiar':'todo'}
    """
    if vision is None:
        return jsonify({'ok': False, 'error': 'vision.py no esta instalado'})
    data = request.get_json(silent=True) or {}
    lim = data.get('limpiar')
    if lim:
        ok, det = vision.limpiar_ajustes(None if lim == 'todo' else lim)
        _bit('vision', f'ajuste de casilla borrado: {lim}')
        return jsonify({'ok': ok, 'detalle': det})
    sq = (data.get('sq') or '').strip()
    if not sq:
        return jsonify({'ok': False, 'error': 'falta sq'})
    ok, det = vision.mover_casilla(sq, x=data.get('x'), y=data.get('y'),
                                   dx=data.get('dx'), dy=data.get('dy'))
    if ok:
        _bit('vision', f'casilla {sq} corrida', ajuste=det.get('ajuste'))
    return jsonify({'ok': ok, 'detalle': det} if ok else {'ok': False, 'error': det})


@app.route('/vision/ocupacion', methods=['GET', 'POST'])
def vision_ocupacion():
    """Segundo metodo: OCUPACION ABSOLUTA por la arandela.

    No compara con una foto anterior: mira cada casilla en si misma. Sirve
    para VERIFICAR el tablero entero -que es lo que el diferencial no puede
    hacer- y detectar desincronizacion apenas aparece.

    POST {'aprender': true} con el tablero acomodado segun la partida:
      aprende el corte entre casilla vacia y ocupada de ESTE tablero y ESTA luz.
    GET: lee la ocupacion y la compara con lo que la partida dice.
    """
    if vision is None:
        return jsonify({'ok': False, 'error': 'vision.py no esta instalado'})
    if request.method == 'POST' and (request.get_json(silent=True) or {}).get('aprender'):
        ok, det = vision.calibrar_ocupacion(_ocupadas_fisicas())
        _bit('vision', 'ocupacion calibrada' if ok else f'no se pudo calibrar: {det}',
             detalle=det if ok else None)
        return jsonify({'ok': ok, 'detalle': det})
    r, det = vision.verificar_tablero(_ocupadas_fisicas())
    if r is None:
        return jsonify({'ok': False, 'error': det})
    return jsonify({'ok': True, **r,
                    'umbral': det.get('umbral'),
                    'ayuda': ('sobran = hay pieza y la app no la espera | '
                              'faltan = la app cree que hay pieza y no se ve')})


@app.route('/vision/consenso')
def vision_consenso():
    """Lectura del tablero juntando los metodos disponibles.

    Ninguno es perfecto solo: el diferencial no ve las capturas, la ocupacion
    depende de un umbral aprendido y el de pares necesita casillas vacias.
    Cuando coinciden, la lectura es confiable; donde discrepan, se avisa.
    """
    if vision is None:
        return jsonify({'ok': False, 'error': 'vision.py no esta instalado'})
    r, err = vision.consenso(_ocupadas_fisicas())
    if r is None:
        return jsonify({'ok': False, 'error': err})
    return jsonify({'ok': True, **r})


@app.route('/vision/vacias')
def vision_vacias():
    """Tercer metodo solo: compara cada casilla con las otras del mismo color
    en la misma foto. No necesita referencia ni calibracion, y un cambio de
    luz no lo afecta porque la referencia sale de la propia imagen."""
    if vision is None:
        return jsonify({'ok': False, 'error': 'vision.py no esta instalado'})
    vac, ocu, det = vision.leer_vacias()
    if vac is None:
        return jsonify({'ok': False, 'error': det})
    esp = {s.upper() for s in _ocupadas_fisicas()}
    return jsonify({'ok': True, 'vacias': vac, 'ocupadas': ocu,
                    'corte': det['corte'],
                    'sobran': sorted(set(ocu) - esp),
                    'faltan': sorted(esp - set(ocu))})


@app.route('/vision/comparar')
def vision_comparar():
    """Compara lo que la camara ve con lo que la app cree que hay.

    Sirve cuando la deteccion 'no encuentra jugada legal': casi siempre es
    que el tablero de madera y el de la app se desincronizaron.
    """
    if vision is None or not vision.listo():
        return jsonify({'ok': False, 'error': 'la camara no esta calibrada'})
    img = vision.capturar()
    if img is None:
        return jsonify({'ok': False, 'error': 'no se pudo capturar'})
    med = vision.medir(img)
    # una casilla ocupada tiene mas estructura (bordes, sombra, brillo) que
    # una vacia: sirve para estimar donde hay piezas sin reconocerlas
    est = med[:, 1]
    corte = float(_np_mediana(est))
    filas = []
    for f in range(7, -1, -1):
        fila = ''
        for c in range(8):
            i = f * 8 + c
            sq_fis = 'ABCDEFGH'[c] + str(f + 1)
            # que dice la app para ese escaque fisico
            log_sq = sq_fisico(sq_fis)      # rotacion es su propia inversa
            p = tablero.piece_at(chess.parse_square(log_sq.lower()))
            fila += (p.symbol() if p else '.')
        filas.append(f"{f+1} {fila}")
    return jsonify({'ok': True,
                    'app_cree': filas,
                    'nota': 'filas y columnas en coordenadas FISICAS del tablero',
                    'juegan': 'blancas' if tablero.turn == chess.WHITE else 'negras',
                    'color_brazo': color_brazo,
                    'estructura_mediana': round(corte, 1),
                    'ayuda': ('Compara app_cree con el tablero real. Si no '
                              'coinciden, toca Nueva partida y acomoda todo '
                              'en la posicion inicial.')})


def _np_mediana(v):
    import numpy as _np
    return float(_np.median(v))


@app.route('/vision/ajustes', methods=['GET', 'POST'])
def vision_ajustes():
    """Ajustes finos de la deteccion.
    POST {'quieto': 3.0}   segundos que el tablero debe quedarse igual antes
                           de dar la jugada por hecha (subilo si dispara
                           mientras todavia estas moviendo)
    POST {'intervalo': 1.5}  segundos entre fotos
    POST {'umbral': 18}      señal minima para dar una casilla por cambiada
    POST {'max_cambiadas': 6} mas casillas que esto = mano o sombra, no jugada
    """
    if vision is None:
        return jsonify({'ok': False, 'error': 'vision.py no esta instalado'})
    global vision_con_brazo
    data = request.get_json(silent=True) or {}
    if 'brazo' in data:
        vision_con_brazo = False if MODO_PRUEBA_SIN_BRAZO else bool(data['brazo'])
        guardar_calibracion()
        _bit('brazo', f'mover el brazo = {vision_con_brazo}')
    # controles de la camara: contraste, brillo, ganancia, nitidez (0-100%)
    for ctrl in ('contraste', 'brillo', 'saturacion', 'ganancia', 'nitidez', 'gamma'):
        if ctrl not in data:
            continue
        nombre = {'contraste': 'Contrast', 'brillo': 'Brightness',
                  'saturacion': 'Saturation', 'ganancia': 'Gain',
                  'nitidez': 'Sharpness', 'gamma': 'Gamma'}[ctrl]
        v = data[ctrl]
        if v is None or v == '':
            vision.CONTROLES[nombre] = None
            _bit('vision', f'{ctrl} de camara: al valor de fabrica')
            continue
        try:
            v = int(v)
        except (TypeError, ValueError):
            return jsonify({'ok': False, 'error': f'{ctrl} invalido'})
        if not (0 <= v <= 100):
            return jsonify({'ok': False, 'error': f'{ctrl} fuera de rango (0 a 100)'})
        vision.CONTROLES[nombre] = v
        _bit('vision', f'{ctrl} de camara = {v}%')
    global espera_home_s
    if data.get('espera_home') is not None:
        try:
            eh = float(data['espera_home'])
        except (TypeError, ValueError):
            return jsonify({'ok': False, 'error': 'espera_home invalida'})
        if not (0.0 <= eh <= 30.0):
            return jsonify({'ok': False, 'error': 'espera_home fuera de rango (0 a 30 s)'})
        espera_home_s = eh
        guardar_calibracion()
        _bit('brazo', f'espera de estabilizacion en home = {eh}s')
    if data.get('margen') is not None:
        try:
            m = float(data['margen'])
        except (TypeError, ValueError):
            return jsonify({'ok': False, 'error': 'margen invalido'})
        if not (0.02 <= m <= 0.40):
            return jsonify({'ok': False,
                            'error': 'margen fuera de rango (0.02 a 0.40)'})
        vision.MARGEN = m
        vision._rehacer_geometria()      # el radio de la ventana depende de esto
        _bit('vision', f'margen = {m} (ventana {round((1-2*m)*100)}% de la casilla)')
    lim = {'quieto': ('ESPERA_QUIETO', float, 0.5, 15.0),
           'intervalo': ('INTERVALO', float, 0.3, 10.0),
           'umbral': ('UMBRAL', float, 3.0, 120.0),
           'max_cambiadas': ('MAX_CAMBIADAS', int, 2, 64)}
    for clave, (attr, tipo, lo, hi) in lim.items():
        if data.get(clave) is None:
            continue
        try:
            v = tipo(data[clave])
        except (TypeError, ValueError):
            return jsonify({'ok': False, 'error': f'{clave} invalido'})
        if not (lo <= v <= hi):
            return jsonify({'ok': False,
                            'error': f'{clave} fuera de rango ({lo} a {hi})'})
        setattr(vision, attr, v)
        _bit('vision', f'ajuste {clave} = {v}')
    vision.guardar()          # que sobrevivan al reinicio
    return jsonify({'ok': True,
                    'quieto': vision.ESPERA_QUIETO,
                    'intervalo': vision.INTERVALO,
                    'umbral': vision.UMBRAL,
                    'max_cambiadas': vision.MAX_CAMBIADAS,
                    'margen': vision.MARGEN,
                    'ventana_pct': round((1 - 2 * vision.MARGEN) * 100),
                    'ventana_px': vision._radio * 2,
                    'brazo': vision_con_brazo,
                    'espera_home': espera_home_s,
                    'camara': {k: v for k, v in vision.CONTROLES.items()
                               if v is not None},
                    'controles': {'contraste': vision.CONTROLES.get('Contrast'),
                                  'brillo': vision.CONTROLES.get('Brightness'),
                                  'gamma': vision.CONTROLES.get('Gamma'),
                                  'ganancia': vision.CONTROLES.get('Gain')}})


@app.route('/vision/estado')
def vision_estado():
    if vision is None:
        return jsonify({'ok': False, 'error': 'vision.py no esta instalado'})
    return jsonify({'ok': True, **vision.diagnostico()})





@app.route('/vision/test-marco-vs-manual')
def vision_test_marco_vs_manual():
    orientacion = request.args.get('orientacion','blancas_abajo')
    if orientacion not in ('blancas_abajo','blancas_arriba'):
        orientacion = 'blancas_abajo'
    try:
        ok, detalle = vision.test_marco_vs_manual(orientacion)
        return jsonify({'ok':bool(ok), **(detalle if isinstance(detalle,dict)
                                          else {'detalle':detalle})})
    except Exception as e:
        app.logger.exception("TEST MARCO VS MANUAL")
        return jsonify({'ok':False,'error':str(e),
                        'vision_json_modificado':False}), 500


@app.route('/vision/test-autocalibracion-seguro')
def vision_test_autocalibracion_seguro():
    try:
        ok, detalle = vision.test_autocalibracion_seguro()
        return jsonify({'ok':bool(ok), **(detalle if isinstance(detalle,dict)
                                          else {'detalle':detalle})})
    except Exception as e:
        app.logger.exception("TEST AUTOCALIBRACION SEGURO")
        return jsonify({'ok':False,'error':str(e)}), 500


@app.route('/vision/4-bordes-negros-debug')
def vision_4_bordes_negros_debug():
    if vision is None or not hasattr(vision,'debug_4_bordes_negros'):
        return Response('TEST 4 bordes negros no disponible',status=409)
    orientacion=request.args.get('orientacion','blancas_arriba')
    ok,img,det=vision.debug_4_bordes_negros(orientacion=orientacion)
    if not ok or img is None:
        return Response(str(det),status=409,mimetype='text/plain')
    data=vision.jpeg_rgb(img,92)
    if not data:
        return Response('no pude codificar debug',status=500)
    return Response(data,mimetype='image/jpeg',
                    headers={'Cache-Control':'no-store'})


@app.route('/vision/4-bordes-negros-info')
def vision_4_bordes_negros_info():
    if vision is None or not hasattr(vision,'debug_4_bordes_negros'):
        return jsonify({'ok':False,'error':'TEST 4 bordes no disponible'}),409
    orientacion=request.args.get('orientacion','blancas_arriba')
    ok,img,det=vision.debug_4_bordes_negros(orientacion=orientacion)
    return jsonify({'ok':bool(ok),'detalle':det})



@app.route('/vision/laterales-negros-debug')
def vision_laterales_negros_debug():
    if vision is None or not hasattr(vision,'debug_laterales_negros'):
        return Response('TEST laterales negros no disponible',status=409)
    ok,img,det=vision.debug_laterales_negros()
    if not ok or img is None:
        return Response(str(det),status=409,mimetype='text/plain')
    data=vision.jpeg_rgb(img,92)
    if not data:
        return Response('no pude codificar debug',status=500)
    return Response(data,mimetype='image/jpeg',
                    headers={'Cache-Control':'no-store'})


@app.route('/vision/laterales-negros-info')
def vision_laterales_negros_info():
    if vision is None or not hasattr(vision,'debug_laterales_negros'):
        return jsonify({'ok':False,'error':'TEST no disponible'}),409
    ok,img,det=vision.debug_laterales_negros()
    return jsonify({'ok':bool(ok),'detalle':det})



@app.route('/vision/autocalibrar', methods=['POST'])
@_serializar_partida
def vision_autocalibrar():
    """Busca el tablero en la imagen y calcula las 4 esquinas solo.
    Sirve al arrancar o si se movio el soporte de la camara."""
    if vision is None:
        return jsonify({'ok': False, 'error': 'vision.py no esta instalado'})
    ok, det = vision.detectar_tablero()
    if ok:
        okr, detr = vision.tomar_referencia()
        if okr:
            _fijar_ancla_vision_desde_tablero()
    return jsonify({'ok': ok, 'detalle': det})


@app.route('/vision/esquinas', methods=['POST'])
def vision_esquinas():
    """Calibra donde cae el tablero en la imagen.
    POST {'A1':[x,y],'H1':[x,y],'A8':[x,y],'H8':[x,y]} en pixeles de 640x480."""
    if vision is None:
        return jsonify({'ok': False, 'error': 'vision.py no esta instalado'})
    data = request.get_json(silent=True) or {}
    faltan = [k for k in ('A1', 'H1', 'A8', 'H8') if k not in data]
    if faltan:
        return jsonify({'ok': False, 'error': 'faltan esquinas: ' + ', '.join(faltan)})
    try:
        # BROKIE 4.0G.3.5:
        # una calibración MANUAL de 4 esquinas debe mandar sobre cualquier
        # malla 9x9 que haya quedado de una autocalibración anterior.
        vision._malla = None
        for k in ('A1', 'H1', 'A8', 'H8'):
            x, y = int(data[k][0]), int(data[k][1])
            if not (0 <= x < vision.ANCHO and 0 <= y < vision.ALTO):
                return jsonify({'ok': False,
                                'error': f'{k} fuera de la imagen '
                                         f'({vision.ANCHO}x{vision.ALTO})'})
            vision.esquinas[k] = [x, y]
    except (TypeError, ValueError, IndexError):
        return jsonify({'ok': False, 'error': 'formato invalido: {"A1":[x,y],...}'})
    if not vision._rehacer_geometria():
        return jsonify({'ok': False, 'error': 'esas esquinas no son utilizables'})
    vision.guardar()
    import numpy as _np
    lado = _np.linalg.norm(_np.array(vision.esquinas['H1'])
                           - _np.array(vision.esquinas['A1'])) / 8
    return jsonify({'ok': True, 'casilla_px': round(float(lado), 1),
                    **vision.diagnostico()})

@app.route('/vision/referencia', methods=['POST'])
@_serializar_partida
def vision_referencia():
    """Referencia visual + ancla física del FEN confirmado.

    BROKIE 4.1 conserva el fix 4.0.3:
    una referencia válida también inicializa el ancla física.
    """
    if vision is None:
        return jsonify({'ok': False, 'error': 'vision.py no esta instalado'})
    ok, det = vision.tomar_referencia()
    if ok:
        _fijar_ancla_vision_desde_tablero()
        _bit('vision',
             'BROKIE 4.0G.3: referencia + ancla fisica fijadas',
             ancla=_ancla_vision_fisica,
             fen=tablero.fen())
    return jsonify({'ok': ok, 'detalle': det,
                    'ancla_fisica': _ancla_vision_fisica if ok else None,
                    'fen': tablero.fen()})

@app.route('/vision/detectar', methods=['POST'])
@_serializar_partida
def vision_detectar():
    """Mira el tablero y deduce que jugo el humano.
    POST {'aplicar': true} ademas la ejecuta (y responde el motor)."""
    if vision is None:
        return jsonify({'ok': False, 'error': 'vision.py no esta instalado'})
    if (request.get_json(silent=True) or {}).get('aplicar'):
        bloqueo = _bloqueo_jugada_humana()
        if bloqueo:
            return jsonify({'ok': False, 'error': bloqueo, 'aplicada': False}), 409
    mv, det = _deducir_con_camara()
    out = {'ok': True, 'jugada': mv, 'detalle': det}
    if mv and (request.get_json(silent=True) or {}).get('aplicar'):
      with _lock_partida:
        try:
            if chess.Move.from_uci(mv) not in tablero.legal_moves:
                out['ok'] = False
                out['error'] = f'{mv} ya no es legal (el tablero cambio)'
                return jsonify(out)
            ok_conf, motivo_conf = _confirmar_jugada_vision(mv, det)
            if not ok_conf:
                out['ok'] = False
                out['error'] = motivo_conf
                out['aplicada'] = False
                return jsonify(out), 409
            bloqueo = _bloqueo_jugada_humana()
            if bloqueo:
                return jsonify({'ok': False, 'error': bloqueo, 'aplicada': False}), 409
            _aplicar_jugada_humana(chess.Move.from_uci(mv), 'vision/detectar')
            out['aplicada'] = True
            r = _jugar_motor(bool((request.get_json(silent=True) or {}).get('brazo')))
            out['respuesta'] = r
            if not jugada_brokie_manual:
                _refrescar_vision('tras aplicar deteccion manual')
        except Exception as e:
            out['ok'] = False
            out['error'] = str(e)
    return jsonify(out)

@app.route('/nivel', methods=['GET', 'POST'])
def config_nivel():
    """Nivel de juego. GET lista los 12. POST {'nivel': 1..12}."""
    if request.method == 'POST':
        data = request.get_json(silent=True) or {}
        try:
            n = int(data.get('nivel'))
        except (TypeError, ValueError):
            return jsonify({'ok': False, 'error': 'nivel invalido (1 a 10)'})
        if not (1 <= n <= len(NIVELES)):
            return jsonify({'ok': False, 'error': f'nivel fuera de rango (1 a {len(NIVELES)})'})
        ok, det = aplicar_nivel(n)
        if not ok:
            return jsonify({'ok': False, 'error': det})
        guardar_calibracion()
        return jsonify({'ok': True, 'nivel': nivel_actual,
                        'nombre': NIVELES[nivel_actual - 1][0], 'detalle': det})
    return jsonify({'ok': True, 'nivel': nivel_actual,
                    'nombre': NIVELES[nivel_actual - 1][0],
                    'niveles': [{'nivel': i + 1, 'nombre': v[0],
                                 'perdida_max_cp': v[5]}
                                for i, v in enumerate(NIVELES)]})

@app.route('/color', methods=['GET', 'POST'])
def config_color():
    """Color de la partida.

    API nueva:
      POST {'color_jugador': 'blancas'|'negras'}
    calcula automaticamente el color opuesto para BROKIE.

    Compatibilidad:
      POST {'color': 'blancas'|'negras'}
    conserva el significado historico: COLOR DE BROKIE.

    POST {'abrir': true, 'brazo': true}
    hace la primera jugada solo si BROKIE lleva blancas.
    """
    global color_brazo
    if request.method == 'POST':
        data = request.get_json(silent=True) or {}

        cj = data.get('color_jugador')
        if cj is not None:
            cj = str(cj).lower()
            if cj not in ('blancas', 'negras'):
                return jsonify({'ok': False,
                                'error': "color_jugador debe ser 'blancas' o 'negras'"})
            c = 'negras' if cj == 'blancas' else 'blancas'
        else:
            c = data.get('color')
            if c is not None:
                c = str(c).lower()
                if c not in ('blancas', 'negras'):
                    return jsonify({'ok': False,
                                    'error': "color debe ser 'blancas' o 'negras'"})

        if c:
            color_anterior = color_brazo
            color_brazo = c
            guardar_calibracion()
            _diag_vision('cambio_color',
                         color_anterior=color_anterior,
                         color_nuevo=color_brazo,
                         color_jugador=('negras' if color_brazo == 'blancas' else 'blancas'),
                         ancla=_ancla_vision_fisica)

        if data.get('abrir'):
            if color_brazo != 'blancas':
                return jsonify({'ok': False,
                                'error': 'BROKIE juega negras: mueve despues del jugador'})
            if tablero.turn != chess.WHITE:
                return jsonify({'ok': False, 'error': 'No es turno de las blancas'})
            with _lock_partida:
                if tablero.turn != chess.WHITE:
                    return jsonify({'ok': False, 'error': 'No es turno de las blancas'})
                r = _jugar_motor(bool(data.get('brazo', vision_con_brazo)))
            r['color_brazo'] = color_brazo
            r['color_jugador'] = 'negras'
            return jsonify(r)

    color_jugador = 'negras' if color_brazo == 'blancas' else 'blancas'
    return jsonify({'ok': True,
                    'color_brazo': color_brazo,
                    'color_jugador': color_jugador,
                    'rota_tablero': color_brazo == 'negras',
                    'turno': 'blancas' if tablero.turn == chess.WHITE else 'negras',
                    'le_toca_al_brazo':
                        (tablero.turn == chess.WHITE) == (color_brazo == 'blancas')})

@app.route('/espera/grabar', methods=['POST'])
def espera_grabar():
    """Graba la posicion ACTUAL como punto de maniobra fuera del tablero.
    Ahi va la torre mientras se mueve el rey en el enroque."""
    global punto_espera
    if not SERVOS_OK:
        return jsonify({'ok': False, 'error': 'Servos no conectados'})
    pos, _s = leer_posiciones_robusta()
    if any(pos.get(s) is None for s in (1, 2, 3, 4)):
        return jsonify({'ok': False, 'error': 'Sin lectura confiable. Sincronizar real.'})
    punto_espera = {s: pos[s] for s in (1, 2, 3, 4)}
    guardar_calibracion()
    return jsonify({'ok': True, 'punto_espera': punto_espera})


@app.route('/espera', methods=['GET', 'POST'])
def espera_config():
    """GET estado. POST {'ir': true} va al punto.
    POST {'por_afuera': true} usa el punto en el enroque (por defecto NO:
    el enroque se hace con dos movimientos normales, sin punto intermedio)."""
    global enroque_por_afuera
    if request.method == 'POST':
        data = request.get_json(silent=True) or {}
        if 'por_afuera' in data:
            if data['por_afuera'] and punto_espera is None:
                return jsonify({'ok': False,
                                'error': 'Primero grabar el punto de maniobra'})
            enroque_por_afuera = bool(data['por_afuera'])
            guardar_calibracion()
        if data.get('ir'):
            if punto_espera is None:
                return jsonify({'ok': False, 'error': 'No hay punto de espera grabado'})
            r = mover_con_transito(dict(punto_espera))
            if not r.get('ok'):
                return jsonify({'ok': False, 'error': r.get('error')})
    return jsonify({'ok': True, 'punto_espera': punto_espera,
                    'listo': punto_espera is not None,
                    'enroque_por_afuera': enroque_por_afuera,
                    'modo': ('la torre pasa por el punto de afuera'
                             if enroque_por_afuera
                             else 'rey y torre directo, sin punto intermedio')})


@app.route('/iman/tiempos', methods=['GET', 'POST'])
def iman_tiempos():
    """Tiempos del electroiman.
    POST {'espera': 1.0, 'soltar': 0.3}
    espera = segundos con el iman encendido ANTES de levantar la pieza."""
    global iman_espera_s, iman_soltar_s
    if request.method == 'POST':
        data = request.get_json(silent=True) or {}
        if data.get('espera') is not None:
            try:
                v = float(data['espera'])
            except (TypeError, ValueError):
                return jsonify({'ok': False, 'error': 'espera invalida'})
            if not (0.1 <= v <= 5.0):
                return jsonify({'ok': False, 'error': 'espera fuera de rango (0.1 a 5.0 s)'})
            iman_espera_s = v
        if data.get('soltar') is not None:
            try:
                v = float(data['soltar'])
            except (TypeError, ValueError):
                return jsonify({'ok': False, 'error': 'soltar invalido'})
            if not (0.1 <= v <= 3.0):
                return jsonify({'ok': False, 'error': 'soltar fuera de rango (0.1 a 3.0 s)'})
            iman_soltar_s = v
        guardar_calibracion()
    return jsonify({'ok': True, 'iman_espera_s': iman_espera_s,
                    'iman_soltar_s': iman_soltar_s})

@app.route('/captura/grabar', methods=['POST'])
def captura_grabar():
    """Graba la posicion ACTUAL como punto de la caja de descarte.
    POST {} con el brazo puesto a mano sobre la caja."""
    global punto_captura
    if not SERVOS_OK:
        return jsonify({'ok': False, 'error': 'Servos no conectados'})
    pos, sosp = leer_posiciones_robusta()
    if any(pos.get(s) is None for s in (1, 2, 3, 4)):
        return jsonify({'ok': False, 'error': 'Sin lectura confiable. Sincronizar real.'})
    punto_captura = {s: pos[s] for s in (1, 2, 3, 4)}
    guardar_calibracion()
    return jsonify({'ok': True, 'punto_captura': punto_captura,
                    'suelta_mm_arriba': captura_altura_mm})

@app.route('/captura', methods=['GET', 'POST'])
def captura_config():
    """GET estado. POST {'altura_mm': 40} cuanto mas arriba suelta.
    POST {'ir': true} va al punto de descarte para verificarlo."""
    global captura_altura_mm, volver_a_home
    if request.method == 'POST':
        data = request.get_json(silent=True) or {}
        if data.get('volver_a_home') is not None:
            volver_a_home = bool(data['volver_a_home'])
            guardar_calibracion()
        if data.get('altura_mm') is not None:
            v = int(data['altura_mm'])
            if not (0 <= v <= 120):
                return jsonify({'ok': False, 'error': 'altura_mm fuera de rango (0-120)'})
            captura_altura_mm = v
            guardar_calibracion()
        if data.get('ir'):
            if punto_captura is None:
                return jsonify({'ok': False, 'error': 'No hay punto de captura grabado'})
            r = mover_con_transito(_subir(punto_captura, captura_altura_mm))
            if not r.get('ok'):
                return jsonify({'ok': False, 'error': r.get('error')})
    return jsonify({'ok': True, 'punto_captura': punto_captura,
                    'altura_mm': captura_altura_mm,
                    'volver_a_home': volver_a_home,
                    'nivel': nivel_actual,
                    'reinicio_horas': reinicio_horas,
                    'listo': punto_captura is not None})

def _validar_sugerencia_humana(data, falla, fen_actual):
    """Un botón antiguo no puede confirmar otra posición o una duda nueva."""
    if 'confirmacion_sugerida' not in data:
        return True
    confirmacion = data.get('confirmacion_sugerida')
    if not isinstance(confirmacion, dict) or not isinstance(falla, dict):
        return False
    jugada = str(data.get('origen') or '') + str(data.get('destino') or '')
    jugada += str(data.get('promocion') or '')
    return bool(
        data.get('recuperacion_dudosa') is True
        and falla.get('sugerencia_humana') == jugada
        and falla.get('fen_sugerencia') == fen_actual
        and confirmacion.get('fen') == fen_actual
        and confirmacion.get('hora') == falla.get('hora')
        and falla.get('hora')
    )


@app.route('/mover', methods=['POST'])
@_serializar_partida
def mover():
    data = request.json or {}
    origen = data.get('origen')
    destino = data.get('destino')

    # BROKIE POST-LAB:
    # True únicamente cuando el jugador informa por touch una jugada
    # física que visión dejó DUDOSA.
    recuperacion_dudosa = bool(data.get('recuperacion_dudosa', False))

    # el candado evita que la camara empuje otra jugada al mismo tiempo
    _lock_partida.acquire()
    # brazo=True -> el robot ejecuta fisicamente la respuesta del motor
    # si el cliente no lo dice, vale la preferencia guardada: asi una pagina
    # recien abierta no juega "sin brazo" sin que el jugador se entere
    con_brazo = (False if MODO_PRUEBA_SIN_BRAZO else bool(data.get('brazo', vision_con_brazo)) and SERVOS_OK)
    try:
        if not _validar_sugerencia_humana(data, falla_vision, tablero.fen()):
            return jsonify({'ok': False,
                            'error': 'La duda cambió. Revisá el aviso actual antes de confirmar.'}), 409
        # El touch no puede iniciar otra transición mientras BROKIE espera que
        # se coloque su respuesta, ni después de un final manual. Antes estas
        # solicitudes podían avanzar el FEN en un estado intermedio.
        if jugada_brokie_manual:
            return jsonify({'ok': False,
                            'error': 'primero colocá la jugada de BROKIE',
                            'jugada_brokie_manual': jugada_brokie_manual,
                            'estado': estado_partida()}), 409
        if jugada_pendiente:
            return jsonify({'ok': False,
                            'error': 'hay una jugada de BROKIE pendiente',
                            'jugada_pendiente': jugada_pendiente,
                            'estado': estado_partida()}), 409
        if fin_manual:
            return jsonify({'ok': False, 'fin': True,
                            'error': fin_manual.get('aviso', 'La partida terminó'),
                            'estado': estado_partida()}), 409
        # La partida ya termino: no tiene sentido evaluar la jugada ni decir
        # "estas en jaque". Antes, tras un mate, cualquier intento de mover
        # respondia eso y el cartel de MATE no llegaba a aparecer.
        if tablero.is_game_over():
            est = estado_partida()
            return jsonify({'ok': False, 'fin': True, 'estado': est,
                            'error': est.get('aviso', 'La partida termino')})

        # PROMOCION: si un peon llega al fondo, la jugada necesita la pieza.
        # Sin eso, from_uci arma una jugada sin promocion y sale ilegal.
        pieza = (data.get('promocion') or '').lower()
        uci = f"{origen}{destino}"
        try:
            base_mv = chess.Move.from_uci(uci)
        except Exception:
            return jsonify({'ok': False, 'error': f'Jugada mal escrita: {uci}'})
        opciones = [m for m in tablero.legal_moves
                    if m.from_square == base_mv.from_square
                    and m.to_square == base_mv.to_square and m.promotion]
        if opciones and not pieza:
            return jsonify({'ok': False, 'promocion_requerida': True,
                            'origen': origen, 'destino': destino,
                            'opciones': ['q', 'r', 'b', 'n'],
                            'estado': estado_partida(),
                            'error': 'Peon corona: elegi con que pieza'})
        if opciones and pieza:
            if pieza not in ('q', 'r', 'b', 'n'):
                return jsonify({'ok': False, 'error': f'Pieza invalida: {pieza}'})
            uci = f"{origen}{destino}{pieza}"

        movimiento = chess.Move.from_uci(uci)
        if movimiento not in tablero.legal_moves:
            # decir POR QUE, no solo que es ilegal
            p = tablero.piece_at(base_mv.from_square)
            if p is None:
                motivo = f'No hay ninguna pieza en {origen.upper()}'
            elif (p.color == chess.WHITE) != (tablero.turn == chess.WHITE):
                motivo = f'Esa pieza no es tuya: juegan las {"blancas" if tablero.turn == chess.WHITE else "negras"}'
            elif tablero.is_check():
                motivo = 'Estas en JAQUE: tenes que defender al rey'
            elif any(m.from_square == base_mv.from_square for m in tablero.legal_moves):
                motivo = f'{p.symbol().upper()} no puede ir de {origen.upper()} a {destino.upper()}'
            else:
                motivo = f'La pieza de {origen.upper()} no tiene movidas (dejaria al rey en jaque)'
            return jsonify({'ok': False, 'error': motivo, 'ilegal': True,
                            'estado': estado_partida()})

        respuesta = {'ok': True, 'movimiento': uci}
        _aplicar_jugada_humana(movimiento, 'touch')
        _limpiar_falla()

        # BROKIE POST-LAB — CIERRE DE DUDOSA MANUAL
        #
        # El movimiento físico ya ocurrió y el usuario acaba de
        # identificarlo explícitamente. El FEN avanza UNA sola vez.
        #
        # No renovamos todavía la referencia aquí si BROKIE debe
        # responder: en MODO_PRUEBA_SIN_BRAZO la referencia definitiva
        # se fija después de colocar físicamente la respuesta de BROKIE.
        if recuperacion_dudosa:
            globals()['_firma_notificada_40'] = None

            _bit(
                'vision',
                'DUDOSA resuelta por ingreso manual touch',
                jugada=uci,
                fen=tablero.fen()
            )

            respuesta['recuperacion_dudosa'] = True

        respuesta['estado'] = estado_partida()

        if tablero.is_game_over() or not engine:
            respuesta['fin'] = tablero.is_game_over()
            if respuesta['fin']:
                _cerrar_partida()
            else:
                _refrescar_vision('tras jugada manual')
            return jsonify(respuesta)

        mv = elegir_jugada()
        o, d = mv.uci()[:2], mv.uci()[2:4]
        # que se captura ANTES de empujar la jugada al tablero
        cap = None
        if tablero.is_capture(mv):
            cap = d if not tablero.is_en_passant(mv) else \
                  chess.square_name(chess.square(chess.square_file(mv.to_square),
                                                 chess.square_rank(mv.from_square)))
        enroque = tablero.is_castling(mv)
        promo = mv.promotion is not None

        if con_brazo:
            if enroque:
                ok, det = ejecutar_enroque(mv.uci())
                respuesta['brazo'] = {'ok': ok, 'detalle': det, 'enroque': True}
            else:
                ok, det = ejecutar_jugada_fisica(o, d, captura_en=cap)
                respuesta['brazo'] = {'ok': ok, 'detalle': det, 'captura': cap}
                if enroque:
                    respuesta['brazo']['aviso'] = ('ENROQUE: mover la torre a mano '
                                                   '(falta grabar el punto de espera)')
            if promo:
                pieza = {chess.QUEEN: 'DAMA', chess.ROOK: 'TORRE',
                         chess.BISHOP: 'ALFIL', chess.KNIGHT: 'CABALLO'}.get(
                             mv.promotion, 'DAMA')
                respuesta['brazo']['aviso'] = (f'BROKIE corono en {d.upper()}: '
                                               f'cambia ese peon por una {pieza}')
                respuesta['brazo']['cambiar_pieza'] = {'escaque': d, 'pieza': pieza}
                _bit('partida', f'BROKIE corono en {d}: hay que poner una {pieza}')
            if not ok:
                # Si el brazo no pudo ejecutar, NO se aplica la jugada: si no,
                # el tablero de la app queda un movimiento adelante del de
                # madera y todo lo que venga despues se desincroniza.
                _em(False)
                _bit('brazo', 'la jugada del motor NO se ejecuto: no la aplico '
                              'para no desincronizar', jugada=mv.uci(), detalle=det)
                globals()['jugada_pendiente'] = {
                    'jugada': mv.uci(), 'motivo': str(det)[:120],
                    'hora': time.strftime('%H:%M:%S')}
                respuesta['ok'] = False
                respuesta['no_aplicada'] = mv.uci()
                respuesta['error'] = (f'BROKIE no pudo completar el movimiento: {det}. Toca '
                                      'Reintentar cuando el brazo este libre.')
                respuesta['estado'] = estado_partida()
                return jsonify(respuesta)

        tablero.push(mv)
        respuesta['respuesta_engine'] = mv.uci()
        if not con_brazo:
            _marcar_brokie_para_colocacion_manual(
                mv, captura=cap, enroque=enroque, promocion=promo)
            respuesta['requiere_colocacion_manual'] = True
            respuesta['jugada_fisica'] = _uci_fisico(mv.uci())
        respuesta['estado'] = estado_partida()
        respuesta['fin'] = tablero.is_game_over()
        if respuesta['fin']:
            _cerrar_partida()
        elif con_brazo:
            _refrescar_vision('tras jugada manual + respuesta del motor')
        return jsonify(respuesta)
    except Exception as e:
        _em(False)
        return jsonify({'ok': False, 'error': str(e)})
    finally:
        _lock_partida.release()

def _verificar_respuesta_brokie(pendiente):
    """La respuesta es conocida: comprobar su transformación, no deducir otra."""
    try:
        if pendiente.get('fen_post') != tablero.fen() or not pendiente.get('fen_pre'):
            return {'ok': False, 'motivo': 'respuesta pendiente sin ancla coherente'}
        antes = chess.Board(pendiente['fen_pre'])
        movimiento = chess.Move.from_uci(pendiente['jugada'])
        if movimiento not in antes.legal_moves:
            return {'ok': False, 'motivo': 'respuesta incompatible con su PRE'}
        despues = antes.copy(stack=False)
        despues.push(movimiento)
        if despues.fen() != pendiente['fen_post']:
            return {'ok': False, 'motivo': 'POST no corresponde a la respuesta guardada'}
        pre = set(_fisicas_de_tablero(antes))
        post = set(_fisicas_de_tablero(despues))
        foco = sorted((pre ^ post) | {
            sq_fisico(chess.square_name(movimiento.from_square)).lower(),
            sq_fisico(chess.square_name(movimiento.to_square)).lower()})
        # Sin extras/continuidad: el PRE geométrico todavía puede ser anterior
        # a la jugada humana. Exigir dos observaciones absolutas del POST.
        resultado = vision.brokie45_confirmar_estado_post(
            sorted(pre), sorted(post), foco, intentos=3, pausa_s=.25,
            casillas_movimiento=foco)
        if (not resultado.get('ok') and not antes.is_capture(movimiento)
                and not antes.is_castling(movimiento) and not movimiento.promotion
                and hasattr(vision, 'confirmar_traslado_conocido_aislado')):
            relativo = vision.confirmar_traslado_conocido_aislado(
                sq_fisico(chess.square_name(movimiento.from_square)),
                sq_fisico(chess.square_name(movimiento.to_square)), sorted(pre), sorted(post))
            _bit('vision', 'verificacion relativa respuesta conocida',
                 jugada=pendiente['jugada'], detalle=relativo)
            if relativo.get('ok'):
                return relativo
        return resultado
    except Exception as error:
        return {'ok': False, 'motivo': 'fallo verificando respuesta', 'error': str(error)[:160]}


@app.route('/prueba/brokie_colocada', methods=['POST'])
@_serializar_partida
def prueba_brokie_colocada():
    """Confirma que el usuario ya reprodujo físicamente la jugada de BROKIE.

    El FEN ya estaba avanzado. Aquí NO hacemos push: sólo fijamos la nueva
    referencia física y recién entonces reanudamos la visión del turno humano.
    """
    global jugada_brokie_manual, falla_vision, _firma_notificada_40
    if not jugada_brokie_manual:
        return jsonify({'ok': False, 'error': 'no hay jugada manual de BROKIE pendiente'}), 409
    if vision is None or not vision.listo():
        return jsonify({'ok': False, 'error': 'vision no disponible'}), 503

    with _lock_partida:
        if not jugada_brokie_manual:
            return jsonify({'ok': False, 'error': 'la jugada ya fue confirmada'}), 409
        pendiente = dict(jugada_brokie_manual)
        try:
            vision.pausar(True, 'confirmando movimiento manual BROKIE')
        except Exception:
            pass
        ok, det = vision.tomar_referencia(estable=True)
        if not ok:
            return jsonify({'ok': False,
                            'error': 'no pude fijar referencia despues de la jugada manual',
                            'detalle': det}), 409
        _fijar_ancla_vision_desde_tablero()
        falla_vision = None
        _firma_notificada_40 = None
        jugada_brokie_manual = None
        try:
            vision.pausar(False)
        except Exception:
            pass
        _bit('partida', 'MODO PRUEBA: colocacion manual BROKIE confirmada',
             jugada=pendiente.get('jugada'), fen=tablero.fen())
        return jsonify({'ok': True, 'jugada': pendiente.get('jugada'),
                        'fen': tablero.fen(), 'detalle': det})


@app.route('/vision/dudosa/reintentar', methods=['POST'])
@_serializar_partida
def vision_dudosa_reintentar():
    """Fuerza otra lectura del MISMO PRE sin cambiar FEN ni referencia.

    Se usa después de que el usuario centra una pieza dudosa. Sólo limpia la
    supresión de firma repetida y vuelve a ejecutar el decisor geométrico.
    """
    global falla_vision, _firma_notificada_40
    if vision is None or not vision.listo():
        return jsonify({'ok': False, 'error': 'vision no disponible'}), 503
    if ilegal_pendiente:
        return jsonify({'ok': False, 'error': 'hay una jugada ilegal pendiente'}), 409
    if jugada_brokie_manual:
        return jsonify({'ok': False, 'error': 'primero coloque la jugada de BROKIE'}), 409
    data = request.get_json(silent=True) or {}
    casilla = str(data.get('casilla') or '').upper()
    falla_vision = None
    _firma_notificada_40 = None
    _bit('vision', 'REINTENTO HUMANO DE DUDOSA sin renovar PRE',
         casilla=casilla or None, fen=tablero.fen())

    token = _token_estado_visual()
    def _releer():
        time.sleep(0.35)
        try:
            with _lock_partida:
                if token != _token_estado_visual():
                    return
                _al_detectar_jugada()
        except Exception as e:
            _bit('vision', 'fallo relectura dudosa', error=str(e)[:160])
    threading.Thread(target=_releer, daemon=True).start()
    return jsonify({'ok': True, 'casilla': casilla or None,
                    'fen': tablero.fen(), 'detalle': 'PRE conservado; relectura lanzada'})


@app.route('/vision/dudosa/cancelar', methods=['POST'])
@_serializar_partida
def vision_dudosa_cancelar():
    """Abandona una recuperacion DUDOSA sin aceptar ninguna jugada."""
    global falla_vision, _firma_notificada_40

    anterior = falla_vision

    falla_vision = None
    _firma_notificada_40 = None

    _bit('vision',
         'ESCAPE recuperacion DUDOSA: expediente cancelado; FEN intacto',
         anterior=anterior,
         fen=tablero.fen())

    return jsonify({
        'ok': True,
        'fen': tablero.fen(),
        'detalle': 'recuperacion dudosa cancelada; FEN y PRE intactos',
    })


@app.route('/acomodar', methods=['GET', 'POST'])
@_serializar_partida
def acomodar():
    """Modo ACOMODAR.

    Entrar:
      pausa la vision mientras el jugador toca piezas.

    Salir:
      exige una referencia estable del tablero fisico ACTUAL,
      conserva exactamente el mismo FEN y turno,
      elimina cualquier expediente DUDOSO anterior y recien entonces
      vuelve a mirar.

    ACOMODAR nunca acepta una jugada ni hace tablero.push().
    """
    global falla_vision, _firma_notificada_40

    if vision is None:
        return jsonify({'ok': False, 'error': 'vision.py no esta instalado'})

    data = request.get_json(silent=True) or {}

    if 'activo' in data:

        if data['activo']:
            vision.pausar(True, 'acomodando')
            _bit('vision',
                 'modo acomodar: pausa explicita',
                 fen=tablero.fen())
        else:
            try:
                vision.pausar(True, 'acomodando')
            except Exception:
                pass

            ok, det = vision.tomar_referencia(estable=True)

            if not ok:
                _bit('vision',
                     'fin de acomodar rechazado: no hubo referencia estable',
                     detalle=det,
                     fen=tablero.fen())

                return jsonify({
                    'ok': False,
                    'error': 'no pude fijar una referencia estable',
                    'detalle': det,
                    'acomodando': True,
                    'pausada': True,
                    'motivo': 'acomodando',
                    'fen': tablero.fen(),
                }), 409

            _fijar_ancla_vision_desde_tablero()

            falla_vision = None
            _firma_notificada_40 = None

            if jugada_brokie_manual:
                vision.pausar(True, 'esperando movimiento manual BROKIE')
            else:
                vision.pausar(False)

            _bit('vision',
                 'fin del acomodar: referencia nueva + duda anterior cancelada',
                 fen=tablero.fen())

    return jsonify({
        'ok': True,
        'acomodando': vision._motivo_pausa == 'acomodando',
        'pausada': vision._pausada,
        'motivo': vision._motivo_pausa,
        'fen': tablero.fen(),
    })


@app.route('/reintentar', methods=['POST'])
@_serializar_partida
def reintentar_jugada():
    """Vuelve a intentar la jugada de BROKIE que el brazo no pudo hacer.

    POST {}            reintenta con el brazo
    POST {'a_mano': true}  la jugada ya se hizo a mano: solo se aplica

    Sin esto la partida quedaba trabada para siempre: la jugada del jugador
    aplicada, la del motor no, y el turno de BROKIE sin forma de avanzar.
    """
    global jugada_pendiente
    if not jugada_pendiente:
        return jsonify({'ok': False, 'error': 'No hay ninguna jugada pendiente'})
    uci = jugada_pendiente['jugada']
    with _lock_partida:
        try:
            mv = chess.Move.from_uci(uci)
        except Exception:
            jugada_pendiente = None
            return jsonify({'ok': False, 'error': f'jugada pendiente invalida: {uci}'})
        if mv not in tablero.legal_moves:
            jugada_pendiente = None
            return jsonify({'ok': False,
                            'error': f'{uci} ya no es legal: se descarta la pendiente'})
        a_mano = bool((request.get_json(silent=True) or {}).get('a_mano'))
        if jugada_pendiente.get('solo_manual') and not a_mano:
            return jsonify({'ok': False,
                            'error': 'Jugada parcialmente realizada: completar y '
                                     'confirmar a mano. No se repetirá con el brazo.'}), 409
        if not a_mano:
            o, d = uci[:2], uci[2:4]
            cap = None
            if tablero.is_capture(mv):
                cap = d if not tablero.is_en_passant(mv) else \
                      chess.square_name(chess.square(chess.square_file(mv.to_square),
                                                     chess.square_rank(mv.from_square)))
            if tablero.is_castling(mv):
                ok, det = ejecutar_enroque(uci)
            else:
                ok, det = ejecutar_jugada_fisica(o, d, captura_en=cap)
            if not ok:
                jugada_pendiente['motivo'] = str(det)[:120]
                jugada_pendiente['hora'] = time.strftime('%H:%M:%S')
                _bit('brazo', f'reintento fallido de {uci}', detalle=det)
                return jsonify({'ok': False, 'error': f'Sigue sin poder: {det}',
                                'pendiente': jugada_pendiente})
        tablero.push(mv)
        jugada_pendiente = None
        _bit('partida', f'jugada pendiente {uci} '
                        + ('aplicada a mano' if a_mano else 'ejecutada al reintentar'))
        est = estado_partida()
    _refrescar_vision('tras reintentar')
    return jsonify({'ok': True, 'jugada': uci, 'a_mano': a_mano, 'estado': est})




@app.route('/vision/calibracion_sesion/estado')
def vision_calibracion_sesion_estado():
    if vision is None:
        return jsonify({'ok': False, 'error': 'vision no disponible'}), 503
    return jsonify({'ok': True, 'calibracion': vision.calibracion_sesion_estado()})


@app.route('/vision/perfil_color')
def vision_perfil_color():
    if vision is None:
        return jsonify({'ok': False, 'error': 'vision no disponible'}), 503
    try:
        return jsonify({'ok': True, 'perfil': vision.perfil_color_estado()})
    except Exception as e:
        return jsonify({'ok': False, 'error': str(e)}), 500


@app.route('/vision/calibracion_sesion/vacio', methods=['POST'])
def vision_calibracion_sesion_vacio():
    if vision is None or not vision.listo():
        return jsonify({'ok': False, 'error': 'vision no disponible o sin geometria'}), 409
    try:
        vision.detener_vigilancia()
    except Exception:
        pass

    # BROKIE V34.3-SIN-AUTO-OPTICO:
    # La cámara conserva su perfil persistido y ExposureAuto=True.
    # No se ejecuta ningún barrido/optimizador de exposición, gamma,
    # brillo ni gain antes de aprender el tablero vacío.
    auto_ok = False
    auto_det = {'desactivado': True, 'motivo': 'AUTO optico pre-partida anulado'}

    ok, det = vision.calibrar_sesion_vacio()
    _bit('vision', 'calibracion pre-partida: vacio',
         ok=ok, detalle=det if isinstance(det, dict) else str(det),
         auto_optico_ok=bool(auto_ok))
    return jsonify({
        'ok': ok,
        'detalle': det,
        'auto_optico_ok': bool(auto_ok),
        'auto_optico': auto_det,
    }), (200 if ok else 409)


@app.route('/vision/calibracion_sesion/piezas', methods=['POST'])
def vision_calibracion_sesion_piezas():
    if vision is None or not vision.listo():
        return jsonify({'ok': False, 'error': 'vision no disponible o sin geometria'}), 409
    # La partida normal empieza en posición inicial: 32 casillas conocidas.
    # Además pasamos COLOR DE PIEZA en coordenadas FÍSICAS. Esto permite medir
    # automáticamente las 4 clases:
    # blanca/clara, blanca/oscura, negra/clara, negra/oscura.
    inicial = chess.Board()
    esperadas = []
    colores_fisicos = {}
    for sq in chess.SQUARES:
        pieza = inicial.piece_at(sq)
        if pieza is None:
            continue
        logica = chess.square_name(sq)
        fisica = sq_fisico(logica).upper()
        esperadas.append(fisica)
        colores_fisicos[fisica] = 'blanca' if pieza.color == chess.WHITE else 'negra'

    ok, det = vision.calibrar_sesion_piezas(
        esperadas, colores_pieza=colores_fisicos, aplicar=True,
        etiqueta_color=color_brazo)
    _bit('vision', 'calibracion pre-partida: piezas',
         ok=ok, detalle=det if isinstance(det, dict) else str(det))
    return jsonify({'ok': ok, 'detalle': det}), (200 if ok else 409)



@app.route('/vision/calibracion_sesion/reutilizar', methods=['POST'])
def vision_calibracion_sesion_reutilizar():
    """Reusar calibración anterior sólo si lado/luz/escena coinciden."""
    if vision is None or not vision.listo():
        return jsonify({'ok': False,
                        'error': 'vision no disponible o sin geometria'}), 409
    try:
        vision.detener_vigilancia()
    except Exception:
        pass

    try:
        ok, det = vision.reutilizar_calibracion_sesion(
            etiqueta_color=color_brazo)
    except Exception as e:
        ok, det = False, {'motivo': str(e)}

    _bit('vision',
         'reuso calibracion anterior: aceptado' if ok
         else 'reuso calibracion anterior: rechazado',
         color_brazo=color_brazo,
         detalle=det if isinstance(det, dict) else str(det))
    return jsonify({'ok': ok, 'detalle': det}), (200 if ok else 409)



@app.route('/partida/iniciar', methods=['POST'])
@_serializar_partida
def partida_iniciar():
    global tablero, color_brazo, vision_activa, vision_con_brazo, ilegal_pendiente, fin_manual, jugada_brokie_manual
    data = request.get_json(silent=True) or {}

    # Preferido: el frontend envia el color DEL JUGADOR.
    color_jugador = data.get('color_jugador')
    if color_jugador is not None:
        color_jugador = str(color_jugador).lower()
        if color_jugador not in ('blancas', 'negras'):
            return jsonify({'ok':False,'error':'color_jugador invalido'}),400
        color = 'negras' if color_jugador == 'blancas' else 'blancas'
    else:
        # Compatibilidad con interfaces anteriores: "color" = color de BROKIE.
        color = str(data.get('color','')).lower()
        if color not in ('blancas','negras'):
            return jsonify({'ok':False,'error':'color invalido'}),400
        color_jugador = 'negras' if color == 'blancas' else 'blancas'

    modo = str(data.get('modo','')).lower()
    try:
        nivel = int(data.get('nivel'))
    except (TypeError, ValueError):
        return jsonify({'ok':False,'error':'nivel invalido'}),400
    if modo not in ('vision','touch'):
        return jsonify({'ok':False,'error':'modo invalido'}),400
    if not (1 <= nivel <= len(NIVELES)):
        return jsonify({'ok':False,
                        'error':f'nivel fuera de rango (1 a {len(NIVELES)})'}),400

    ok_nivel, det_nivel = aplicar_nivel(nivel)
    if not ok_nivel:
        return jsonify({'ok':False,
                        'error':f'no pude aplicar nivel: {det_nivel}'}),409

    brazo_solicitado = bool(data.get('brazo', False))
    if brazo_solicitado and MODO_PRUEBA_SIN_BRAZO:
        return jsonify({'ok':False,
                        'error':'el bloqueo maestro SIN BRAZO está activo'}),409
    if brazo_solicitado and not SERVOS_OK:
        return jsonify({'ok':False,
                        'error':'servos no disponibles para jugar con brazo'}),409
    vision_con_brazo = brazo_solicitado
    if vision is not None:
        try: vision.detener_vigilancia()
        except Exception: pass
        try: vision.reiniciar_diagnostico_pasivo()
        except Exception: pass
    with _lock_partida:
        _nueva_sesion_partida()
        tablero = chess.Board()
        color_brazo = color
        ilegal_pendiente = None
        fin_manual = None
        _limpiar_falla()
        _limpiar_aviso_ilegal()
        globals()['desfase_tablero'] = None
        globals()['jugada_pendiente'] = None
        jugada_brokie_manual = None
    _reiniciar_referencia_gy302()

    cam = False
    if modo == 'vision':
        if vision is None or not vision.listo():
            return jsonify({'ok':False,'error':'vision no disponible o sin calibrar'}),409
        ok,det = vision.tomar_referencia(estable=True)
        if not ok:
            return jsonify({'ok':False,'error':'no pude tomar referencia inicial','detalle':det}),409
        _fijar_ancla_vision_desde_tablero()
        try:
            vision.calibrar_ocupacion(_ocupadas_fisicas())
        except Exception:
            pass
        okv,detv = vision.iniciar_vigilancia(callback=_al_detectar_jugada)
        if not okv:
            return jsonify({'ok':False,'error':'no pude iniciar vigilancia','detalle':detv}),409
        vision_activa = True
        cam = True
    else:
        if vision is not None:
            try: vision.detener_vigilancia()
            except Exception: pass
        vision_activa = False
        globals()['_ancla_vision_fisica'] = None

    guardar_calibracion()
    _bit('partida', 'PARTIDA INICIADA', color_jugador=color_jugador,
         color_brazo=color_brazo, modo=modo, nivel=nivel_actual,
         brazo=vision_con_brazo, fen=tablero.fen())
    return jsonify({'ok':True,
                    'color_jugador':color_jugador,
                    'color_brazo':color_brazo,'modo':modo,
                    'nivel':nivel_actual,
                    'nivel_nombre':NIVELES[nivel_actual-1][0],
                    'camara':cam,'brazo':vision_con_brazo,
                    'abre_brokie':color_brazo=='blancas',
                    'fen':tablero.fen()})



TABLAS_CP_ACEPTAR = 35

@app.route('/partida/rendirse', methods=['POST'])
def partida_rendirse():
    global fin_manual
    with _lock_partida:
        if fin_manual or tablero.is_game_over():
            return jsonify({'ok': False, 'error': 'la partida ya termino'}), 409
        gana = color_brazo
        fin_manual = {
            'jaque': tablero.is_check(),
            'fin': True,
            'turno': 'blancas' if tablero.turn == chess.WHITE else 'negras',
            'resultado': 'rendicion',
            'gana': gana,
            'aviso': f'TE RENDISTE - ganan las {gana}',
        }
        _bit('partida', 'jugador se rinde', gana=gana, fen=tablero.fen())
        _cerrar_partida()
    return jsonify({'ok': True, 'partida': estado_partida()})


@app.route('/partida/ofrecer_tablas', methods=['POST'])
def partida_ofrecer_tablas():
    global fin_manual
    with _lock_partida:
        if fin_manual or tablero.is_game_over():
            return jsonify({'ok': False, 'error': 'la partida ya termino'}), 409
        if not STOCKFISH_OK:
            return jsonify({'ok': False, 'error': 'Stockfish no disponible'}), 503
        try:
            info = engine.analyse(tablero, chess.engine.Limit(time=0.45))
            color_sf = chess.WHITE if color_brazo == 'blancas' else chess.BLACK
            pov = info['score'].pov(color_sf)
            mate = pov.mate()
            cp = pov.score(mate_score=100000)
        except Exception as e:
            return jsonify({'ok': False, 'error': f'no pude evaluar la oferta: {e}'}), 500

        acepta = (mate is None and cp is not None and abs(int(cp)) <= TABLAS_CP_ACEPTAR)
        _bit('partida', 'oferta de tablas', acepta=acepta, cp=cp, mate=mate,
             umbral_cp=TABLAS_CP_ACEPTAR, fen=tablero.fen())

        if acepta:
            fin_manual = {
                'jaque': tablero.is_check(),
                'fin': True,
                'turno': 'blancas' if tablero.turn == chess.WHITE else 'negras',
                'resultado': 'tablas acordadas',
                'aviso': 'TABLAS ACEPTADAS POR BROKIE',
            }
            _cerrar_partida()
            return jsonify({'ok': True, 'acepta': True,
                            'evaluacion_cp': cp, 'partida': estado_partida()})

        return jsonify({'ok': True, 'acepta': False,
                        'evaluacion_cp': cp, 'mate': mate,
                        'aviso': 'BROKIE RECHAZA LAS TABLAS'})


@app.route('/reiniciar', methods=['POST'])
@_serializar_partida
def reiniciar():
    """Partida nueva. Deja la camara lista sin que haya que activarla aparte:
    el jugador acomoda las piezas, toca Nueva y ya esta mirando."""
    global tablero, vision_activa, aviso_ilegal, ilegal_pendiente, fin_manual, jugada_brokie_manual
    cam = None

    # El brazo se lleva a home ANTES de tomar el candado: mover tarda decenas
    # de segundos y con el candado puesto la interfaz no responderia a nada,
    # que se ve igual que un congelamiento. La camara va en la muñeca y su
    # calibracion solo vale en esa pose.
    if vision is not None:
        try:
            vision.detener_vigilancia()
        except Exception:
            pass
        try:
            vision.reiniciar_diagnostico_pasivo()
        except Exception:
            pass
        vision_activa = False
    if (vision is not None and vision.listo() and SERVOS_OK
            and vision_con_brazo and not _brazo_en_home()):
        _bit('brazo', 'partida nueva: llevo el brazo a home')
        vision.pausar(True)
        try:
            _em(False)
            mover_a_home()
            time.sleep(1.2)
        except Exception as e:
            _bit('brazo', 'no pude llevar el brazo a home', error=str(e))
        finally:
            vision.pausar(False)

    with _lock_partida:
        _nueva_sesion_partida()
        tablero = chess.Board()
        ilegal_pendiente = None
        fin_manual = None
        _limpiar_falla()
        _limpiar_aviso_ilegal()
        globals()['desfase_tablero'] = None
        globals()['jugada_pendiente'] = None
        jugada_brokie_manual = None
    _reiniciar_referencia_gy302()
    # La camara se arranca FUERA del candado: capturar puede tardar si la
    # camara esta lenta, y el tablero ya quedo reiniciado.
    if vision is not None and vision.listo():
        try:
            ok, det = vision.tomar_referencia()
            if ok:
                # V02.1: la referencia visual y el ancla fisica deben nacer
                # juntas. Sin esto, si BROKIE juega negras el humano mueve
                # primero y _confirmar_jugada_vision() rechaza la primera
                # jugada con "sin ancla fisica".
                _fijar_ancla_vision_desde_tablero()

                # Momento ideal para que los metodos absolutos aprendan: las
                # 32 piezas estan puestas y se sabe exactamente donde.
                okc, detc = vision.calibrar_ocupacion(_ocupadas_fisicas())
                _bit('vision', 'ocupacion aprendida en partida nueva' if okc
                     else f'no se pudo aprender la ocupacion: {detc}',
                     detalle=detc if okc else None)
                ok, det = vision.iniciar_vigilancia(callback=_al_detectar_jugada)
            if ok:
                if not vision_activa:
                    vision_activa = True
                    guardar_calibracion()
                cam = True
                _bit('vision', 'camara activada al empezar partida nueva')
            else:
                cam = False
                _bit('vision', 'no se pudo activar la camara en partida nueva',
                     motivo=str(det))
        except Exception as e:
            cam = False
            _bit('vision', 'error activando la camara', error=str(e))
    else:
        _bit('partida', 'partida nueva (camara sin calibrar)')
    return jsonify({'ok': True, 'camara': cam,
                    'brazo': vision_con_brazo if cam else None})


@app.route('/electroiman', methods=['POST'])
def control_electroiman():
    global electroiman_estado
    if _prueba_tirones_activa:
        return jsonify({'ok': False,
                        'error': 'Prueba de tirones activa: control manual bloqueado'}), 409
    data = request.json
    estado = data.get('estado', False)
    electroiman_estado = estado
    if GPIO_OK:
        if estado:
            electroiman.on()
        else:
            electroiman.off()
    return jsonify({'ok': True, 'estado': electroiman_estado})

@app.route('/electroiman/estado')
def estado_electroiman():
    return jsonify({'estado': electroiman_estado})

@app.route('/servos/estado')
@_excluir_movimientos('http')
def servos_estado():
    if not SERVOS_OK:
        return jsonify({'ok': False, 'error': 'Servos no conectados'})
    pos = leer_posiciones_u()
    _luz_confirmar_home(pos)
    estados = {sid: ({'pos': p} if p is not None else {'error': 'sin lectura'})
               for sid, p in pos.items()}
    return jsonify({'ok': True, 'servos': estados})

@app.route('/servos/traza_movimiento', methods=['GET', 'POST'])
def servos_traza_movimiento():
    """Activa/desactiva la traza pasiva de consignas del suavizador."""
    global TRAZA_MOVIMIENTO_ACTIVA, TRAZA_MOVIMIENTO_MS
    if request.method == 'POST':
        data = request.get_json(silent=True) or {}
        if 'activa' in data:
            TRAZA_MOVIMIENTO_ACTIVA = bool(data['activa'])
        if data.get('intervalo_ms') is not None:
            try:
                intervalo = int(data['intervalo_ms'])
            except (TypeError, ValueError):
                return jsonify({'ok': False, 'error': 'intervalo_ms invalido'}), 400
            if not 50 <= intervalo <= 1000:
                return jsonify({'ok': False,
                                'error': 'intervalo_ms fuera de rango (50-1000)'}), 400
            TRAZA_MOVIMIENTO_MS = intervalo
    return jsonify({'ok': True, 'activa': TRAZA_MOVIMIENTO_ACTIVA,
                    'intervalo_ms': TRAZA_MOVIMIENTO_MS,
                    'tipo': 'consignas pasivas; sin lecturas UART adicionales',
                    'caja_negra': '/servos/auditoria_ordenes'})


@app.route('/servos/auditoria_ordenes')
def servos_auditoria_ordenes():
    """Caja negra en RAM de las escrituras intentadas hacia el UART.

    Filtros opcionales: ?n=500&servo=4&desde_seq=123&traza_id=...
    No lee posiciones ni toca el bus de servos.
    """
    try:
        n = max(1, min(5000, int(request.args.get('n', 500))))
    except (TypeError, ValueError):
        return jsonify({'ok': False, 'error': 'n invalido'}), 400
    try:
        servo = request.args.get('servo')
        servo = int(servo) if servo not in (None, '') else None
        desde_seq = int(request.args.get('desde_seq', 0))
    except (TypeError, ValueError):
        return jsonify({'ok': False,
                        'error': 'servo o desde_seq invalido'}), 400
    if servo is not None and servo not in (1, 2, 3, 4):
        return jsonify({'ok': False, 'error': 'servo invalido'}), 400
    traza_id = request.args.get('traza_id') or None
    with _servo_ordenes_lock:
        registros = list(_servo_ordenes)
        secuencia = _servo_orden_secuencia
        capacidad = _servo_ordenes.maxlen
    if desde_seq:
        registros = [r for r in registros if r['seq'] > desde_seq]
    if servo is not None:
        registros = [r for r in registros if r['servo'] == servo]
    if traza_id is not None:
        registros = [r for r in registros if r['traza_id'] == traza_id]
    registros = registros[-n:]
    return jsonify({
        'ok': True,
        'tipo': 'ordenes enviadas; sin lecturas fisicas adicionales',
        'secuencia_actual': secuencia,
        'capacidad': capacidad,
        'cantidad': len(registros),
        'ordenes': registros,
    })


def _prueba_tirones_seq():
    """Secuencia de la caja negra sin leer el UART."""
    with _servo_ordenes_lock:
        return _servo_orden_secuencia


def _prueba_tirones_actualizar(**cambios):
    with _prueba_tirones_lock:
        _prueba_tirones_estado.update(cambios)
        estado = dict(_prueba_tirones_estado)
        estado['marcas'] = [dict(m) for m in _prueba_tirones_estado['marcas']]
        estado['voltajes'] = [dict(m) for m in
                              _prueba_tirones_estado['voltajes']]
        estado['voltaje_min_mv'] = dict(
            _prueba_tirones_estado['voltaje_min_mv'])
    return estado


def _prueba_tirones_publicar(incluir_series=False):
    estado = _prueba_tirones_actualizar(seq_actual=_prueba_tirones_seq())
    serie = estado.get('voltajes', [])
    estado['muestras_voltaje'] = len(serie)
    estado['ultimo_voltaje'] = serie[-1] if serie else None
    if not incluir_series:
        estado.pop('voltajes', None)
    if estado.get('seq_inicio') is not None:
        estado['auditoria_url'] = (
            '/servos/auditoria_ordenes?n=5000&desde_seq='
            + str(estado['seq_inicio']))
    estado['ruta'] = (
        'todas las jugadas de la partida actual'
        if estado.get('origen_plan') == 'partida_actual' else
        'partida patrón completa: 70 medias jugadas, capturas y enroque')
    estado['mediciones_paralelas'] = 'camara y GY-302 suspendidos'
    estado['informe_url'] = '/servos/prueba_tirones/informe'
    return estado


def _prueba_tirones_medir_voltajes(etapa):
    """Lee VIN con el brazo detenido; nunca se invoca dentro de una curva."""
    valores = {}
    errores = {}
    for sid, servo in servos.items():
        try:
            valores[str(sid)] = int(servo.get_vin())
        except Exception as exc:
            valores[str(sid)] = None
            errores[str(sid)] = str(exc)[:120]
    muestra = {
        'hora': time.strftime('%H:%M:%S'),
        'ts': time.time(),
        'seq': _prueba_tirones_seq(),
        'bloque': _prueba_tirones_estado.get('bloque'),
        'ciclo': _prueba_tirones_estado.get('ciclo'),
        'jugada': _prueba_tirones_estado.get('jugada'),
        'uci': _prueba_tirones_estado.get('uci'),
        'fase': etapa,
        'mv': valores,
    }
    if errores:
        muestra['errores'] = errores
    with _prueba_tirones_lock:
        _prueba_tirones_estado['voltajes'].append(muestra)
        minimos = _prueba_tirones_estado['voltaje_min_mv']
        for sid, valor in valores.items():
            if valor is not None:
                minimos[sid] = min(valor, minimos.get(sid, valor))
    _bit('brazo', 'PRUEBA TIRON voltajes en reposo',
         etapa=etapa, voltajes_mv=valores, errores=errores or None,
         bloque=muestra['bloque'], ciclo=muestra['ciclo'])
    return muestra


def _prueba_tirones_resultado(resultado, etapa):
    if not isinstance(resultado, dict) or not resultado.get('ok'):
        detalle = (resultado or {}).get('error') if isinstance(resultado, dict) else None
        raise RuntimeError(f'{etapa}: {detalle or "movimiento sin confirmacion"}')


def _prueba_tirones_volver_home(contacto=None):
    """Termina la parada solicitada en HOME; no interrumpe un micropaso."""
    _prueba_tirones_actualizar(
        fase='retorno_seguro', detalle='Parada solicitada: volviendo a HOME')
    resultado = mover_a_home(contacto_salida=contacto)
    _prueba_tirones_resultado(resultado, 'retorno seguro a HOME')


# Partida patrón legal completa (35 jugadas, 70 medias jugadas, jaque mate).
# Incluye peones, piezas altas, capturas y enroque largo. La posición virtual
# se usa sólo para derivar altura/capturas: jamás reemplaza ``tablero`` ni toca
# el FEN de la partida real.
_PRUEBA_TIRON_PARTIDA_UCI = tuple("""
e2e4 g8h6 g2g3 d7d5 e4d5 c8e6 d5e6 c7c5 e6f7 h6f7
f1c4 d8d2 c1d2 h7h6 c4f7 e8f7 d1f3 f7g8 d2b4 c5b4
f3b7 b8d7 b7d5 e7e6 d5e6 g8h7 e6e4 h7g8 e4a8 a7a6
b1d2 g7g6 a8a6 f8c5 e1c1 c5f2 a6c6 f2g3 c6d7 g6g5
d1e1 g3h2 d7f5 g8g7 f5g5 g7h7 g5h6 h7h6 d2b3 h8b8
h1h2 h6g7 h2h7 g7h7 e1e7 h7g8 e7g7 g8g7 c1b1 g7g6
b3a1 g6h7 g1f3 b8g8 b1c1 g8f8 f3g5 h7g6 c1b1 f8f1
""".split())


def _prueba_tirones_plan_partida(movimientos=None):
    """Plan inmutable de una partida con alturas y hechos especiales."""
    virtual = chess.Board()
    plan = []
    secuencia = tuple(movimientos or _PRUEBA_TIRON_PARTIDA_UCI)
    for numero, uci in enumerate(secuencia, 1):
        mov = chess.Move.from_uci(uci)
        if mov not in virtual.legal_moves:
            raise RuntimeError(f'Partida patrón inválida en {numero}: {uci}')
        pieza = virtual.piece_at(mov.from_square)
        origen = chess.square_name(mov.from_square)
        destino = chess.square_name(mov.to_square)
        captura_sq = None
        altura_captura = None
        if virtual.is_capture(mov):
            cap_square = mov.to_square
            if virtual.is_en_passant(mov):
                cap_square = chess.square(
                    chess.square_file(mov.to_square),
                    chess.square_rank(mov.from_square))
            capturada = virtual.piece_at(cap_square)
            captura_sq = chess.square_name(cap_square)
            altura_captura = ALTURA_PIEZA.get(
                capturada.symbol().lower(), 'rey') if capturada else 'rey'
        torre = None
        if virtual.is_castling(mov):
            torre = ({'e1c1': ('a1', 'd1'), 'e1g1': ('h1', 'f1'),
                      'e8c8': ('a8', 'd8'), 'e8g8': ('h8', 'f8')}
                     .get(uci[:4]))
        plan.append({
            'numero': numero,
            'uci': uci,
            'origen': origen,
            'destino': destino,
            'altura': ALTURA_PIEZA.get(pieza.symbol().lower(), 'rey'),
            'captura': captura_sq,
            'altura_captura': altura_captura,
            'torre': torre,
        })
        virtual.push(mov)
    return plan


def _prueba_tirones_transferir(origen, destino_pos, altura, destino=None,
                                etiqueta='pieza'):
    """Una toma real sin pieza: origen, imán ON, destino, imán OFF."""
    p_origen = _pos_escaque(origen, altura)
    if p_origen is None:
        raise RuntimeError(f'Falta calibración {altura.upper()} en {origen.upper()}')

    _prueba_tirones_actualizar(
        fase=f'{etiqueta}_ir_origen',
        detalle=f'{etiqueta}: yendo a {origen.upper()}')
    r = mover_con_transito(
        p_origen, sq_destino=sq_fisico(origen), altura=altura)
    _prueba_tirones_resultado(r, f'yendo a {origen.upper()}')
    _prueba_tirones_medir_voltajes(f'{etiqueta}_origen_iman_off')
    if _prueba_tirones_stop.is_set():
        return None, True

    _prueba_tirones_actualizar(
        fase=f'{etiqueta}_iman_on',
        detalle=f'{etiqueta}: electroimán ON en {origen.upper()}')
    _em(True)
    espera = max(0.0, float(iman_espera_s))
    detener = _prueba_tirones_stop.wait(min(0.10, espera))
    if not detener:
        _prueba_tirones_medir_voltajes(f'{etiqueta}_origen_iman_on')
        detener = _prueba_tirones_stop.wait(max(0.0, espera - 0.10))
    if detener:
        _em(False)
        return None, True

    nombre_destino = destino.upper() if destino else 'CAJA'
    _prueba_tirones_actualizar(
        fase=f'{etiqueta}_traslado',
        detalle=f'{etiqueta}: {origen.upper()} -> {nombre_destino}, imán ON')
    r = mover_con_transito(
        destino_pos,
        sq_destino=sq_fisico(destino) if destino else None,
        sq_origen=sq_fisico(origen),
        altura=altura if destino else None)
    _prueba_tirones_resultado(r, f'{origen.upper()} -> {nombre_destino}')
    if not _prueba_tirones_stop.is_set():
        _prueba_tirones_medir_voltajes(f'{etiqueta}_destino_iman_on')
    _em(False)
    _prueba_tirones_stop.wait(max(0.0, float(iman_soltar_s)))
    return destino_pos, _prueba_tirones_stop.is_set()


def _prueba_tirones_worker(repeticiones, plan):
    """Reproduce una partida completa sin piezas y sin modificar su FEN."""
    global _prueba_tirones_activa
    propietario = False
    hubo_error = False
    try:
        propietario = _propietario_movimiento.acquire(blocking=False)
        if not propietario:
            raise RuntimeError('Brazo ocupado: la prueba no se inició')

        _cerrar_ajuste_home()
        if punto_captura is None:
            raise RuntimeError('Falta el punto de caja para reproducir capturas')
        _prueba_tirones_medir_voltajes('inicio_home')

        for repeticion in range(1, repeticiones + 1):
            for jugada in plan:
                if _prueba_tirones_stop.is_set():
                    break
                _prueba_tirones_actualizar(
                    estado='en_curso', bloque='PARTIDA COMPLETA',
                    ciclo=repeticion, jugada=jugada['numero'],
                    jugadas_total=len(plan), uci=jugada['uci'],
                    fase='inicio_jugada',
                    detalle=(f'Repetición {repeticion}/{repeticiones}, '
                             f'jugada {jugada["numero"]}/{len(plan)}: '
                             f'{jugada["uci"].upper()}'))
                _bit('brazo', 'PRUEBA TIRON: jugada de partida',
                     repeticion=repeticion, jugada=jugada['numero'],
                     total=len(plan), uci=jugada['uci'],
                     captura=jugada['captura'], enroque=bool(jugada['torre']))

                # Captura real: primero lleva la pieza rival a la caja, sin
                # volver a HOME entre esa retirada y la jugada propia.
                if jugada['captura']:
                    caja = _subir(punto_captura, captura_altura_mm)
                    _contacto, detener = _prueba_tirones_transferir(
                        jugada['captura'], caja, jugada['altura_captura'],
                        etiqueta='captura')
                    if detener:
                        _prueba_tirones_volver_home()
                        break

                destino_pos = _pos_escaque(jugada['destino'], jugada['altura'])
                if destino_pos is None:
                    raise RuntimeError(
                        f'Falta calibración {jugada["altura"]} '
                        f'en {jugada["destino"].upper()}')
                contacto, detener = _prueba_tirones_transferir(
                    jugada['origen'], destino_pos, jugada['altura'],
                    destino=jugada['destino'], etiqueta='jugada')
                _prueba_tirones_volver_home(contacto=contacto)
                _prueba_tirones_medir_voltajes('home_fin_jugada')
                if detener:
                    break

                # El enroque físico hace una segunda transferencia para torre.
                if jugada['torre']:
                    torre_o, torre_d = jugada['torre']
                    torre_pos = _pos_escaque(torre_d, 'rey')
                    contacto, detener = _prueba_tirones_transferir(
                        torre_o, torre_pos, 'rey', destino=torre_d,
                        etiqueta='torre_enroque')
                    _prueba_tirones_volver_home(contacto=contacto)
                    _prueba_tirones_medir_voltajes('home_fin_enroque')
                    if detener:
                        break
            if _prueba_tirones_stop.is_set():
                break

        detenido = _prueba_tirones_stop.is_set()
        _prueba_tirones_actualizar(
            estado='detenida' if detenido else 'completa',
            fase='home', error=None,
            detalle=('Prueba detenida en HOME' if detenido else
                     'Prueba completa; brazo en HOME'))
        _bit('brazo', 'PRUEBA TIRON finalizada',
             detenida=detenido, repeticiones=repeticiones,
             marcas=len(_prueba_tirones_estado.get('marcas', [])))
    except Exception as exc:
        hubo_error = True
        _prueba_tirones_actualizar(
            estado='error', error=str(exc),
            detalle='Prueba abortada; no se enviaron más movimientos')
        _bit('brazo', 'PRUEBA TIRON abortada', error=str(exc))
    finally:
        _em(False)
        _prueba_tirones_activa = False
        if propietario:
            _propietario_movimiento.release()
        # Conserva estado/error/marcas para el informe; sólo baja la bandera.
        _prueba_tirones_actualizar(
            activa=False, seq_actual=_prueba_tirones_seq(),
            error=_prueba_tirones_estado.get('error') if hubo_error else None)


@app.route('/servos/prueba_tirones')
def servos_prueba_tirones_estado():
    return jsonify({'ok': True, **_prueba_tirones_publicar()})


@app.route('/servos/prueba_tirones/informe')
def servos_prueba_tirones_informe():
    """Informe completo bajo demanda; el sondeo del touch usa el resumen."""
    return jsonify({'ok': True, **_prueba_tirones_publicar(incluir_series=True)})


@app.route('/servos/prueba_tirones/iniciar', methods=['POST'])
def servos_prueba_tirones_iniciar():
    global _prueba_tirones_activa
    data = request.get_json(silent=True) or {}
    try:
        repeticiones = int(data.get('repeticiones', data.get('ciclos', 1)))
    except (TypeError, ValueError):
        return jsonify({'ok': False,
                        'error': 'Cantidad de repeticiones inválida'}), 400
    if not 1 <= repeticiones <= 3:
        return jsonify({'ok': False,
                        'error': 'Usá entre 1 y 3 partidas completas'}), 400
    if not SERVOS_OK:
        return jsonify({'ok': False, 'error': 'Servos no conectados'}), 503
    if vision is not None and getattr(vision, 'vigilando', False):
        return jsonify({'ok': False,
                        'error': 'Apagá Cámara antes de iniciar la prueba'}), 409
    if transito_pausado:
        return jsonify({'ok': False,
                        'error': 'Reanudá el tránsito antes de iniciar'}), 409
    historial_actual = [mov.uci() for mov in tablero.move_stack]
    origen_plan = ('partida_actual' if historial_actual else
                   'partida_patron_completa')
    try:
        plan = _prueba_tirones_plan_partida(
            historial_actual if historial_actual else None)
    except Exception as exc:
        return jsonify({'ok': False,
                        'error': f'Partida patrón inválida: {exc}'}), 500
    requeridos = []
    for jugada in plan:
        requeridos.extend(((jugada['origen'], jugada['altura']),
                           (jugada['destino'], jugada['altura'])))
        if jugada['captura']:
            requeridos.append((jugada['captura'], jugada['altura_captura']))
        if jugada['torre']:
            requeridos.extend((sq, 'rey') for sq in jugada['torre'])
    faltantes = sorted({f'{sq.upper()} {alt.upper()}'
                        for sq, alt in requeridos
                        if _pos_escaque(sq, alt) is None})
    if faltantes:
        return jsonify({'ok': False,
                        'error': 'Falta calibración: ' + ', '.join(faltantes)}), 409
    if any(j['captura'] for j in plan) and punto_captura is None:
        return jsonify({'ok': False,
                        'error': 'Falta grabar el punto de caja de capturas'}), 409
    with _gy302_lock:
        home_confirmado = bool(_luz_home and not _luz_movimientos)
    if not home_confirmado:
        return jsonify({'ok': False,
                        'error': 'HOME no confirmado. Usá Sincronizar real'}), 409

    seq = _prueba_tirones_seq()
    with _prueba_tirones_lock:
        if _prueba_tirones_activa:
            return jsonify({'ok': False,
                            'error': 'La prueba ya está en curso'}), 409
        _prueba_tirones_activa = True
        _prueba_tirones_stop.clear()
        _prueba_tirones_estado.update({
            'activa': True,
            'estado': 'preparando',
            'bloque': None,
            'ciclo': 0,
            'ciclos_por_bloque': repeticiones,
            'repeticiones': repeticiones,
            'jugada': 0,
            'jugadas_total': len(plan),
            'uci': None,
            'origen_plan': origen_plan,
            'fase': 'inicio',
            'detalle': 'Reservando el brazo',
            'error': None,
            'marcas': [],
            'voltajes': [],
            'voltaje_min_mv': {},
            'seq_inicio': seq,
            'seq_actual': seq,
            'inicio_ts': time.time(),
            'inicio_hora': time.strftime('%H:%M:%S'),
        })
    with _gy302_lock:
        _gy302_estado.update(suspendida=True, estable=False,
                             motivo_suspension='prueba_tirones',
                             pendiente=False, cambio_ts=None,
                             lectura_ts=None)
    hilo = threading.Thread(target=_prueba_tirones_worker,
                            args=(repeticiones, plan),
                            name='prueba-tirones', daemon=True)
    hilo.start()
    _bit('brazo', 'PRUEBA TIRON iniciada', repeticiones=repeticiones,
         jugadas=len(plan), ruta=origen_plan)
    return jsonify({'ok': True, **_prueba_tirones_publicar()})


@app.route('/servos/prueba_tirones/detener', methods=['POST'])
def servos_prueba_tirones_detener():
    if not _prueba_tirones_activa:
        return jsonify({'ok': False, 'error': 'No hay una prueba activa'}), 409
    _prueba_tirones_stop.set()
    _prueba_tirones_actualizar(
        estado='deteniendo',
        detalle='Parada pedida; completando el tramo y volviendo a HOME')
    return jsonify({'ok': True, **_prueba_tirones_publicar()})


@app.route('/servos/prueba_tirones/marcar', methods=['POST'])
def servos_prueba_tirones_marcar():
    if not _prueba_tirones_activa:
        return jsonify({'ok': False, 'error': 'No hay una prueba activa'}), 409
    seq = _prueba_tirones_seq()
    with _prueba_tirones_lock:
        marca = {
            'numero': len(_prueba_tirones_estado['marcas']) + 1,
            'hora': time.strftime('%H:%M:%S'),
            'ts': time.time(),
            'seq': seq,
            'bloque': _prueba_tirones_estado.get('bloque'),
            'ciclo': _prueba_tirones_estado.get('ciclo'),
            'jugada': _prueba_tirones_estado.get('jugada'),
            'uci': _prueba_tirones_estado.get('uci'),
            'fase': _prueba_tirones_estado.get('fase'),
        }
        _prueba_tirones_estado['marcas'].append(marca)
        _prueba_tirones_estado.update(
            estado='deteniendo',
            detalle='TIRÓN MARCADO; completando el tramo y volviendo a HOME')
    _prueba_tirones_stop.set()
    _bit('brazo', 'PRUEBA TIRON marcado por usuario', **marca)
    return jsonify({'ok': True, 'marca': marca,
                    **_prueba_tirones_publicar()})

@app.route('/servos/mover', methods=['POST'])
@_excluir_movimientos('http')
@_suspender_luz_durante_movimiento()
def servos_mover():
    if not SERVOS_OK:
        return jsonify({'ok': False, 'error': 'Servos no conectados'})
    data = request.json
    servo_id = data.get('id')
    posicion = data.get('posicion')
    tiempo = data.get('tiempo', 500)
    verificar = data.get('verificar', True)
    try:
        servo_id = int(servo_id)
        posicion = int(posicion)
        tiempo = int(tiempo)
        if servo_id not in servos:
            return jsonify({'ok': False, 'error': 'servo invalido'}), 400
        if not 0 <= posicion <= 1000:
            return jsonify({'ok': False, 'error': 'posicion fuera de 0-1000'}), 400
        if servo_id == 4 and posicion < MUNECA_MIN:
            return jsonify({'ok': False,
                            'error': f'muñeca no puede bajar de {MUNECA_MIN}'}), 400
        s = servos[servo_id]
        # Una acción manual equivale exactamente a una orden. Antes, después de
        # esta orden, el endpoint podía ejecutar hasta tres sobrepasos/retornos
        # distintos según una lectura física. Eso hacía que un solo clic siguiera
        # moviendo el brazo cuando el usuario ya esperaba que estuviese quieto.
        _enviar_lote_servo([(servo_id, u2g(posicion), int(tiempo))])
        time.sleep(max(0, tiempo) / 1000.0 + 0.1)
        if not verificar:
            return jsonify({'ok': True, 'ordenes': 1,
                            'correccion_automatica': False})
        real = _leer_servo_robusto(s, intentos=2)
        if real is None:
            return jsonify({'ok': False,
                            'error': 'orden enviada, pero no pude leer el servo',
                            'ordenes': 1,
                            'correccion_automatica': False}), 503
        return jsonify({'ok': True, 'pos_real': real,
                        'error_posicion': real - posicion,
                        'reintentos': 0, 'ordenes': 1,
                        'correccion_automatica': False})
    except Exception as e:
        return jsonify({'ok': False, 'error': str(e)})

@app.route('/servos/home', methods=['POST'])
def servos_set_home():
    """Fija la posicion de home de UN servo.

    Se valida con cuidado: sin esto, una peticion sin datos escribia
    servo_home[None]=None, y esa clave nula rompia despues la carga ENTERA
    del calibracion.json al arrancar (int('null') falla), dejando el sistema
    sin puntos, sin tabla y sin ajustes.
    """
    data = request.get_json(silent=True) or {}
    try:
        servo_id = int(data.get('id'))
        posicion = int(data.get('posicion'))
    except (TypeError, ValueError):
        return jsonify({'ok': False,
                        'error': 'Faltan id (1-4) y posicion (0-1000)'}), 400
    if servo_id not in (1, 2, 3, 4):
        return jsonify({'ok': False, 'error': 'id debe ser 1, 2, 3 o 4'}), 400
    if not (0 <= posicion <= 1000):
        return jsonify({'ok': False, 'error': 'posicion fuera de 0-1000'}), 400
    if servo_id == 4 and posicion < MUNECA_MIN:
        return jsonify({'ok': False,
                        'error': f'HOME de muñeca no puede bajar de {MUNECA_MIN}'}), 400
    servo_home[servo_id] = posicion
    guardar_calibracion()
    return jsonify({'ok': True, 'home': servo_home})

@app.route('/servos/home_actual')
def servos_home_actual():
    return jsonify({'ok': True, 'home': servo_home})


@app.route('/servos/confirmar_home', methods=['POST'])
@_excluir_movimientos('http')
def servos_confirmar_home():
    """Comprueba el HOME canónico sin enviar consignas a los servos."""
    global _fallo_retorno_home, _mediciones_bloqueadas_hasta
    if vision is None:
        return jsonify({'ok': False, 'error': 'Visión no disponible'}), 503
    try:
        confirmado, detalle = vision.validar_home_canonico()
    except Exception as exc:
        confirmado, detalle = False, {'error': str(exc)[:180]}
    if not confirmado:
        return jsonify({'ok': False,
                        'error': 'El canónico no pudo validar los cuatro ArUco',
                        'home_canonico': detalle}), 409
    _luz_confirmar_home_canonico()
    with _gy302_lock:
        _mediciones_bloqueadas_hasta = max(
            _mediciones_bloqueadas_hasta, time.monotonic() + espera_home_s)
    _fallo_retorno_home = None
    if vision.vigilando:
        _refrescar_vision('HOME confirmado por cuatro ArUco')
    return jsonify({'ok': True, 'confirmado_por': 'cuatro_aruco',
                    'home_canonico': detalle})


@app.route('/servos/ir_home', methods=['POST'])
@_excluir_movimientos('http')
def servos_ir_home():
    global _fallo_retorno_home
    recuperando = bool(_fallo_retorno_home)
    if not SERVOS_OK:
        return jsonify({'ok': False, 'error': 'Servos no conectados'})

    antes, sosp = leer_posiciones_robusta()
    _contar_lecturas(sosp)
    data = request.get_json(silent=True) or {}
    contacto_salida = None
    contacto_sq = None
    contacto_ignorado = None
    if data.get('contacto_escaque') not in (None, ''):
        contacto_sq = _escaque_valido(data.get('contacto_escaque'))
        contacto_altura = data.get('contacto_altura', 'rey')
        if not contacto_sq or contacto_altura not in ALTURAS:
            return jsonify({'ok': False,
                            'error': 'contacto post-suelta inválido'}), 400
        contacto_salida, _ = _punto_base_fisico(contacto_sq,
                                                 contacto_altura)
        if contacto_salida is None:
            return jsonify({'ok': False,
                            'error': (f'{contacto_sq} no tiene altura '
                                      f'{contacto_altura.upper()}')}), 400
        # La corrección codo-primero sólo corresponde si el brazo realmente
        # está todavía sobre ese punto. Ante un estado web obsoleto se vuelve
        # a HOME normal: nunca se fabrica un retiro post-suelta falso.
        diferencias = {
            sid: (None if antes.get(sid) is None else
                  antes[sid] - contacto_salida[sid])
            for sid in (1, 2, 3, 4)
        }
        if any(v is None or abs(v) > 35 for v in diferencias.values()):
            contacto_ignorado = diferencias
            contacto_salida = None
            _bit('brazo', 'HOME manual: contacto post-suelta ignorado',
                 escaque=contacto_sq, diferencias=diferencias)
    ya_en_home = all(
        antes.get(sid) is not None and
        abs(antes[sid] - servo_home[sid]) <= VISION_TOL_HOME
        for sid in (1,2,3,4)
    )

    mov = None
    if not ya_en_home:
        mov = (mover_a_home(contacto_salida=contacto_salida)
               if contacto_salida is not None else mover_a_home())
        if not (mov or {}).get('ok'):
            return jsonify({'ok': False, 'error': 'No pude ir a HOME',
                            'antes': antes, 'movimiento': mov}), 409

    if mov and mov.get('home_confirmado_por') == 'cuatro_aruco':
        final = mov.get('posicion_real_final') or antes
        confirmado = True
    else:
        final, confirmado = _leer_home_asentado(servo_home)
        if not confirmado:
            return jsonify({'ok': False,
                            'error': 'HOME no confirmado por UART ni canónico',
                            'real_final': final, 'movimiento': mov}), 409
        _luz_confirmar_home(final)
    _fallo_retorno_home = None
    if recuperando:
        _refrescar_vision('HOME recuperado por el usuario')
    return jsonify({'ok': True, 'home': servo_home,
                    'ya_estaba': ya_en_home,
                    'antes': antes, 'real_final': final,
                    'contacto_post_suelta': (contacto_sq
                                             if contacto_salida is not None
                                             else None),
                    'contacto_ignorado': contacto_ignorado,
                    'movimiento': mov})


@app.route('/servos/retraso_muneca', methods=['GET', 'POST'])
def servos_retraso_muneca():
    """Lee (GET) o ajusta (POST) el retraso de la muñeca respecto al hombro."""
    global retraso_muneca_val
    if request.method == 'POST':
        data = request.json or {}
        try:
            v = float(data.get('valor'))
        except (TypeError, ValueError):
            return jsonify({'ok': False, 'error': 'valor invalido'})
        if not (1.0 <= v <= 4.0):
            return jsonify({'ok': False, 'error': 'fuera de rango seguro (1.0 a 4.0)'})
        retraso_muneca_val = v
        guardar_calibracion()
        return jsonify({'ok': True, 'retraso_muneca': retraso_muneca_val})
    return jsonify({'ok': True, 'retraso_muneca': retraso_muneca_val})

@app.route('/servos/traslado', methods=['GET', 'POST'])
def servos_traslado():
    """Lee (GET) o ajusta (POST) la postura del brazo en el traslado (banda cercana)."""
    global traslado_hombro, traslado_codo, factor_vel_traslado
    if request.method == 'POST':
        data = request.json or {}
        for campo, gname in [('hombro', 'traslado_hombro'), ('codo', 'traslado_codo')]:
            if campo in data:
                v = data[campo]
                if v is None or v == '':
                    globals()[gname] = None
                else:
                    try:
                        vi = int(v)
                    except (TypeError, ValueError):
                        return jsonify({'ok': False, 'error': f'{campo} invalido'})
                    if not (0 <= vi <= 1000):
                        return jsonify({'ok': False, 'error': f'{campo} fuera de rango (0-1000)'})
                    globals()[gname] = vi
        if 'factor_vel' in data and data['factor_vel'] not in (None, ''):
            try:
                fv = float(data['factor_vel'])
            except (TypeError, ValueError):
                return jsonify({'ok': False, 'error': 'factor_vel invalido'})
            if not (0.3 <= fv <= 3.0):
                return jsonify({'ok': False, 'error': 'factor_vel fuera de rango (0.3-3.0)'})
            factor_vel_traslado = fv
        guardar_calibracion()
        return jsonify({'ok': True,
                        'traslado_hombro': traslado_hombro,
                        'traslado_codo': traslado_codo,
                        'factor_vel_traslado': factor_vel_traslado,
                        'home_hombro': servo_home[2], 'home_codo': servo_home[3]})
    return jsonify({'ok': True,
                    'traslado_hombro': traslado_hombro,
                    'traslado_codo': traslado_codo,
                    'factor_vel_traslado': factor_vel_traslado,
                    'home_hombro': servo_home[2], 'home_codo': servo_home[3]})

@app.route('/servos/vel_muneca_bajada', methods=['GET', 'POST'])
def servos_vel_muneca_bajada():
    """Lee (GET) o ajusta (POST) la velocidad de la muñeca en la bajada."""
    global vel_muneca_bajada, vel_muneca_bajada_cercana
    global vel_muneca_bajada_media
    if request.method == 'POST':
        data = request.json or {}
        try:
            v = float(data.get('valor'))
        except (TypeError, ValueError):
            return jsonify({'ok': False, 'error': 'valor invalido'})
        if not (0.5 <= v <= 4.0):
            return jsonify({'ok': False, 'error': 'fuera de rango (0.5 a 4.0)'})
        if data.get('banda') == 'cercana':
            vel_muneca_bajada_cercana = v
        elif data.get('banda') == 'media':
            vel_muneca_bajada_media = v
        else:
            vel_muneca_bajada = v
        guardar_calibracion()
    return jsonify({'ok': True, 'vel_muneca_bajada': vel_muneca_bajada,
                    'vel_muneca_bajada_cercana': vel_muneca_bajada_cercana,
                    'vel_muneca_bajada_media': vel_muneca_bajada_media})

@app.route('/servos/despegue_codo', methods=['GET', 'POST'])
def servos_despegue_codo():
    """Lee (GET) o ajusta (POST) cuanto abre el codo al despegar."""
    global despegue_codo
    if request.method == 'POST':
        data = request.json or {}
        try:
            v = int(data.get('valor'))
        except (TypeError, ValueError):
            return jsonify({'ok': False, 'error': 'valor invalido'})
        if not (0 <= v <= 300):
            return jsonify({'ok': False, 'error': 'fuera de rango (0 a 300)'})
        despegue_codo = v
        guardar_calibracion()
    return jsonify({'ok': True, 'despegue_codo': despegue_codo})

@app.route('/servos/bajada_codo', methods=['GET', 'POST'])
def servos_bajada_codo():
    """Lee (GET) o ajusta (POST) cuanto ABRE el codo el punto intermedio de la bajada
    (espejo del despegue). POST body: {valor: 50}. El ultimo tramo baja el hombro y
    CIERRA el codo juntos = vertical real. Mayor = descenso mas vertical.
    0 = comportamiento viejo (arco de hombro)."""
    global bajada_codo
    if request.method == 'POST':
        data = request.get_json(silent=True) or {}
        try:
            v = int(data.get('valor'))
        except (TypeError, ValueError):
            return jsonify({'ok': False, 'error': 'valor invalido'})
        if not (0 <= v <= 300):
            return jsonify({'ok': False, 'error': 'fuera de rango (0 a 300)'})
        banda = data.get('banda')
        if banda:
            if banda not in ('cercana', 'media', 'lejana'):
                return jsonify({'ok': False, 'error': 'banda invalida'})
            bajada_codo_banda[banda] = v
        else:
            bajada_codo = v
        guardar_calibracion()
    return jsonify({'ok': True, 'bajada_codo': bajada_codo,
                    'bajada_codo_banda': bajada_codo_banda})

@app.route('/servos/bajada_codo_escaque', methods=['GET', 'POST'])
def servos_bajada_codo_escaque():
    """Ajuste local del encare sin modificar una banda completa.

    POST {"escaque":"E1", "altura":"rey", "valor":170}.
    Con ``quitar:true`` elimina el ajuste y vuelve a heredar el de la banda.
    """
    if request.method == 'POST':
        data = request.get_json(silent=True) or {}
        sq = str(data.get('escaque') or '').upper()
        altura = str(data.get('altura') or '').lower()
        if (len(sq) != 2 or sq[0] not in 'ABCDEFGH' or sq[1] not in '12345678'
                or altura not in ('peon', 'rey')):
            return jsonify({'ok': False, 'error': 'escaque o altura invalida'}), 400
        clave = f'{sq}|{altura}'
        if data.get('quitar') is True:
            bajada_codo_escaque.pop(clave, None)
        else:
            try:
                v = int(data.get('valor'))
            except (TypeError, ValueError):
                return jsonify({'ok': False, 'error': 'valor invalido'}), 400
            if not (0 <= v <= 300):
                return jsonify({'ok': False,
                                'error': 'fuera de rango (0 a 300)'}), 400
            bajada_codo_escaque[clave] = v
        guardar_calibracion()
    return jsonify({'ok': True,
                    'bajada_codo_escaque': bajada_codo_escaque})

@app.route('/servos/margen_lejana', methods=['GET', 'POST'])
def servos_margen_lejana():
    """Lee (GET) o ajusta (POST) el margen vertical de aterrizaje en filas lejanas (7-8)."""
    global margen_aterrizaje_lejana
    if request.method == 'POST':
        data = request.json or {}
        try:
            v = int(data.get('valor'))
        except (TypeError, ValueError):
            return jsonify({'ok': False, 'error': 'valor invalido'})
        if not (20 <= v <= 300):
            return jsonify({'ok': False, 'error': 'fuera de rango (20 a 300)'})
        margen_aterrizaje_lejana = v
        guardar_calibracion()
    return jsonify({'ok': True, 'margen_aterrizaje_lejana': margen_aterrizaje_lejana})

@app.route('/servos/aterrizaje', methods=['GET', 'POST'])
def servos_aterrizaje():
    """Modo del ULTIMO tramo de la bajada.
    POST {'directo': true, 'ms': 500}. directo=true manda una sola orden por
    servo (evita la zona muerta); false usa la curva suave por pasos."""
    global aterrizaje_directo, aterrizaje_ms, aterrizaje_vel, base_solo_arriba
    global paso_transito, paso_bajada, codo_max_encare, margen_max_encare, margen_max_cercana
    global verif_activa, verif_tolerancia, verif_ms, ruta_ms
    global punto_captura, captura_altura_mm, color_brazo, volver_a_home
    global iman_espera_s, iman_soltar_s, punto_espera, enroque_por_afuera
    global vision_activa, vision_con_brazo, espera_home_s
    global nivel_actual, reinicio_horas
    if request.method == 'POST':
        data = request.get_json(silent=True) or {}
        if data.get('vel') is not None:
            try:
                v = float(data['vel'])
            except (TypeError, ValueError):
                return jsonify({'ok': False, 'error': 'vel invalida'})
            if not (0.02 <= v <= 1.0):
                return jsonify({'ok': False, 'error': 'vel fuera de rango (0.02-1.0 u/ms)'})
            aterrizaje_vel = v
        if 'base_solo_arriba' in data:
            base_solo_arriba = bool(data['base_solo_arriba'])
        if 'directo' in data:
            aterrizaje_directo = bool(data['directo'])
        if data.get('ms') is not None:
            try:
                v = int(data['ms'])
            except (TypeError, ValueError):
                return jsonify({'ok': False, 'error': 'ms invalido'})
            if not (150 <= v <= 3000):
                return jsonify({'ok': False, 'error': 'ms fuera de rango (150-3000)'})
            aterrizaje_ms = v
        guardar_calibracion()
    return jsonify({'ok': True, 'aterrizaje_directo': aterrizaje_directo,
                    'aterrizaje_ms': aterrizaje_ms, 'aterrizaje_vel': aterrizaje_vel,
                    'base_solo_arriba': base_solo_arriba})

@app.route('/servos/encare', methods=['GET', 'POST'])
def servos_encare():
    """Altura del punto de encare. En vez de un margen fijo por banda, cada
    escaque toma la altura que le permita el tope del codo.
    POST {'codo_max': 790, 'margen_max': 120}."""
    global codo_max_encare, margen_max_encare, margen_max_cercana
    if request.method == 'POST':
        data = request.get_json(silent=True) or {}
        if data.get('codo_max') is not None:
            v = int(data['codo_max'])
            if not (300 <= v <= 1000):
                return jsonify({'ok': False, 'error': 'codo_max fuera de rango'})
            codo_max_encare = v
        if data.get('margen_max') is not None:
            v = int(data['margen_max'])
            if not (36 <= v <= 300):
                return jsonify({'ok': False, 'error': 'margen_max fuera de rango'})
            margen_max_encare = v
        if data.get('margen_max_cercana') is not None:
            v = int(data['margen_max_cercana'])
            if not (36 <= v <= 300):
                return jsonify({'ok': False, 'error': 'margen_max_cercana fuera de rango'})
            margen_max_cercana = v
        guardar_calibracion()
    return jsonify({'ok': True, 'codo_max_encare': codo_max_encare,
                    'margen_max_encare': margen_max_encare,
                    'margen_max_cercana': margen_max_cercana})

@app.route('/sistema/comprobar', methods=['POST'])
@_serializar_partida
def sistema_comprobar():
    """Lee dispositivos sin moverlos ni renovar referencias del tablero."""
    # Tras reiniciar puede haber una diferencia residual de algunos ticks en
    # un servo aunque el brazo esté físicamente en HOME. Antes de comprobar la
    # cámara, usar la evidencia óptica de los cuatro ArUco. No se hace durante
    # ningún movimiento y nunca envía consignas al brazo.
    with _gy302_lock:
        comprobar_home_optico = bool(
            SERVOS_OK and not _luz_home and not _luz_movimientos)
    if comprobar_home_optico and vision is not None:
        try:
            home_ok, home_det = vision.validar_home_canonico()
        except Exception as exc:
            home_ok, home_det = False, {'error': str(exc)[:180]}
        if home_ok:
            _luz_confirmar_home_canonico()
            _bit('sistema', 'HOME confirmado desde chequeo inicial por 4 ArUco',
                 detalle=home_det)
    if vision is not None:
        vision.capturar()
    if SERVOS_OK:
        _, sospechosos = leer_posiciones_robusta()
        _contar_lecturas(sospechosos)
    return sistema_salud()

@app.route('/sistema/salud')
def sistema_salud():
    """Estado del enlace con los servos. Si el % de fallas sube, las
    interpolaciones empiezan a arrancar de posiciones viejas y el brazo salta."""
    tot = lecturas_ok + lecturas_falladas
    horas = (time.time() - arranque_ts) / 3600.0
    with _gy302_lock:
        gy = dict(_gy302_estado)
    cam_geometria = bool(vision and vision.listo())
    cam_capturas = int(getattr(vision, '_capturas_ok', 0) or 0) if vision else 0
    ahora = time.monotonic()
    cam_ts = getattr(vision, '_ultima_captura_ok_ts', None) if vision else None
    cam_edad = max(0.0, ahora-cam_ts) if cam_ts is not None else None
    cam_comprobada = bool(cam_geometria and cam_capturas > 0 and
                          cam_edad is not None and cam_edad <= 15 and
                          not getattr(vision, '_ultimo_error', None))
    gy_ts = gy.get('lectura_ts')
    gy_disponible = bool(gy.get('error') is None and gy.get('lux') is not None
                         and gy_ts is not None and ahora-gy_ts <= 5)
    servo_comprobado = bool(_lecturas_servos_actuales)
    servo_sano = bool(SERVOS_OK and all(
        sid in _lecturas_servos_actuales and _lecturas_servos_actuales[sid][1]
        and ahora-_lecturas_servos_actuales[sid][0] <= 15 for sid in (1,2,3,4)))
    diagnostico = ('pendiente de comprobar' if not servo_comprobado else
                   'enlace sano' if servo_sano else
                   'ENLACE DEGRADADO o lectura vencida: comprobar conexión')
    return jsonify({'ok': True,
                    'camara': {'disponible': cam_comprobada, 'edad_s': cam_edad,
                               'error': getattr(vision, '_ultimo_error', None),
                               'modulo_cargado': vision is not None,
                               'comprobada': cam_comprobada,
                               'capturas_ok': cam_capturas,
                               'estado': getattr(vision, 'estado_ciclo', None) if vision else 'sin vision',
                               'geometria': cam_geometria},
                    'gy302': {'disponible': gy_disponible,
                              'comprobado': gy_disponible,
                              'estable': bool(gy.get('estable')),
                              'lux': gy.get('lux'),
                              'error': gy.get('error'),
                              'suspendido': bool(gy.get('suspendida')),
                              'home_confirmado': bool(gy.get('home_confirmado')),
                              'motivo': gy.get('motivo_suspension')},
                    'servo_comprobado': servo_comprobado,
                    'servos_operativos': servo_sano,
                    'modo_prueba_sin_brazo': MODO_PRUEBA_SIN_BRAZO,
                    # El GY-302 es un testigo ambiental auxiliar: mejora la
                    # deteccion de cambios globales de luz, pero la vision ya
                    # tiene su propio diagnostico por imagen. Si el sensor no
                    # enumera despues de un reinicio debe avisarse, nunca
                    # bloquear el touch ni impedir una partida sin brazo.
                    # La selección viene después: sin brazo sólo necesita
                    # visión; con brazo /partida/iniciar valida los servos.
                    'partida_lista': bool(cam_comprobada),
                    'horas_encendido': round(horas, 2),
                    'lecturas_ok': lecturas_ok,
                    'lecturas_home_uart': _home_lecturas_uart,
                    'lecturas_con_fallas': lecturas_falladas,
                    'porcentaje_fallas': round(100.0 * lecturas_falladas / tot, 2) if tot else 0,
                    'fallas_por_servo': fallas_por_servo,
                    'diagnostico': diagnostico})

@app.route('/servos/paso_bajada', methods=['GET', 'POST'])
def servos_paso_bajada():
    """Suavidad de la LLEGADA (bajada final y regreso a home).
    POST {'valor': 0.022}. Mas chico = llega mas despacio y vibra menos."""
    global paso_bajada
    if request.method == 'POST':
        data = request.get_json(silent=True) or {}
        try:
            v = float(data.get('valor'))
        except (TypeError, ValueError):
            return jsonify({'ok': False, 'error': 'valor invalido'}), 400
        if not (0.004 <= v <= 0.08):
            return jsonify({'ok': False,
                            'error': 'fuera de rango (0.004 a 0.08)'}), 400
        paso_bajada = v
        guardar_calibracion()
        _bit('brazo', f'paso de bajada = {v} (mas chico = mas suave)')
    return jsonify({'ok': True, 'paso_bajada': paso_bajada})


@app.route('/servos/paso_transito', methods=['GET', 'POST'])
def servos_paso_transito():
    """Velocidad del tramo de transito (despegue -> encare).
    POST {'valor': 0.015}. Mas chico = mas lento. 0.03 era el valor viejo."""
    global paso_transito, paso_bajada, codo_max_encare, margen_max_encare, margen_max_cercana
    if request.method == 'POST':
        data = request.get_json(silent=True) or {}
        try:
            v = float(data.get('valor'))
        except (TypeError, ValueError):
            return jsonify({'ok': False, 'error': 'valor invalido'})
        if not (0.005 <= v <= 0.08):
            return jsonify({'ok': False, 'error': 'fuera de rango (0.005 a 0.08)'})
        paso_transito = v
        guardar_calibracion()
    return jsonify({'ok': True, 'paso_transito': paso_transito})

@app.route('/servos/verificacion', methods=['GET', 'POST'])
def servos_verificacion():
    """Diagnóstico posterior al aterrizaje; jamás reenvía consignas.

    Se acepta la tolerancia para señalar el error residual en la interfaz. La
    antigua clave ``activa`` se conserva en la respuesta por compatibilidad,
    fijada siempre en ``false``.
    """
    global verif_activa, verif_tolerancia
    verif_activa = False
    if request.method == 'POST':
        data = request.get_json(silent=True) or {}
        if data.get('tolerancia') is not None:
            try:
                v = int(data['tolerancia'])
            except (TypeError, ValueError):
                return jsonify({'ok': False, 'error': 'tolerancia invalida'})
            if not (1 <= v <= 20):
                return jsonify({'ok': False, 'error': 'tolerancia fuera de rango (1-20)'})
            verif_tolerancia = v
        guardar_calibracion()
    return jsonify({'ok': True, 'verif_activa': verif_activa,
                    'verif_tolerancia': verif_tolerancia,
                    'solo_diagnostico': True,
                    'correccion_automatica': False})

@app.route('/ruta/tramo', methods=['POST'])
def ruta_tramo():
    """Graba la posicion ACTUAL como el proximo tramo de la bajada de un escaque.
    POST {'escaque':'D1','altura':'rey'}. Se llama una vez por tramo, en orden
    desde arriba hacia abajo. El punto final NO hace falta grabarlo: el transito
    cierra siempre con el calibrado del escaque."""
    if not SERVOS_OK:
        return jsonify({'ok': False, 'error': 'Servos no conectados'})
    data = request.get_json(silent=True) or {}
    sq = str(data.get('escaque', '')).upper()
    altura = data.get('altura', 'rey')
    if len(sq) != 2 or altura not in ALTURAS:
        return jsonify({'ok': False, 'error': 'escaque o altura invalidos'})
    pos, _ = leer_posiciones_robusta()
    if any(pos.get(sid) is None for sid in (1, 2, 3, 4)):
        return jsonify({'ok': False, 'error': 'Sin lectura confiable. Sincronizar real.'})
    clave = f"{sq}|{altura}"
    rutas_bajada.setdefault(clave, []).append({sid: pos[sid] for sid in (1, 2, 3, 4)})
    guardar_calibracion()
    return jsonify({'ok': True, 'escaque': sq, 'altura': altura,
                    'tramos': len(rutas_bajada[clave]),
                    'ruta': rutas_bajada[clave]})

@app.route('/ruta/set', methods=['POST'])
def ruta_set():
    """Carga una ruta completa con valores (sin mover el brazo).
    POST {'escaque':'D1','altura':'rey',
          'tramos': [[base,hombro,codo,muneca], ...]}
    Tambien acepta cada tramo como {'1':..,'2':..,'3':..,'4':..}."""
    data = request.get_json(silent=True) or {}
    sq = str(data.get('escaque', '')).upper()
    altura = data.get('altura', 'rey')
    if len(sq) != 2 or altura not in ALTURAS:
        return jsonify({'ok': False, 'error': 'escaque o altura invalidos'})
    tramos_in = data.get('tramos') or []
    if not tramos_in:
        return jsonify({'ok': False, 'error': 'falta la lista de tramos'})
    ruta = []
    for i, t in enumerate(tramos_in):
        try:
            if isinstance(t, dict):
                p = {sid: int(t.get(str(sid), t.get(sid))) for sid in (1, 2, 3, 4)}
            else:
                p = {sid: int(v) for sid, v in zip((1, 2, 3, 4), t)}
        except (TypeError, ValueError):
            return jsonify({'ok': False, 'error': f'tramo {i+1} invalido'})
        for sid, v in p.items():
            if not (0 <= v <= 1000):
                return jsonify({'ok': False,
                                'error': f'tramo {i+1}: servo {sid} fuera de rango'})
        if p[4] < MUNECA_MIN:
            return jsonify({'ok': False,
                            'error': f'tramo {i+1}: muñeca {p[4]} < {MUNECA_MIN} '
                                     f'(choca el codo)'})
        ruta.append(p)
    rutas_bajada[f"{sq}|{altura}"] = ruta
    guardar_calibracion()
    return jsonify({'ok': True, 'escaque': sq, 'altura': altura,
                    'tramos': len(ruta), 'ruta': ruta})

@app.route('/ruta/borrar', methods=['POST'])
def ruta_borrar():
    """POST {'escaque':'D1','altura':'rey'} borra la ruta entera.
    Con {'ultimo': true} borra solo el ultimo tramo grabado."""
    data = request.get_json(silent=True) or {}
    clave = f"{str(data.get('escaque','')).upper()}|{data.get('altura','rey')}"
    if clave not in rutas_bajada:
        return jsonify({'ok': False, 'error': f'{clave} no tiene ruta'})
    if data.get('ultimo'):
        rutas_bajada[clave].pop()
        if not rutas_bajada[clave]:
            del rutas_bajada[clave]
    else:
        del rutas_bajada[clave]
    guardar_calibracion()
    return jsonify({'ok': True, 'tramos': len(rutas_bajada.get(clave, []))})

@app.route('/ruta/listar')
def ruta_listar():
    return jsonify({'ok': True,
                    'rutas': {k: len(v) for k, v in rutas_bajada.items()},
                    'detalle': rutas_bajada, 'ruta_ms': ruta_ms})

@app.route('/ruta/copiar', methods=['POST'])
def ruta_copiar():
    """Copia una ruta a otros escaques conservando la FORMA (los tramos se
    guardan como diferencias respecto del punto calibrado, y se re-aplican
    sobre el calibrado de cada destino).
    POST {'origen':'D1','altura':'rey','destinos':['E1'],
          'altura_destino':'peon'}   # opcional: copiar a la otra capa"""
    data = request.get_json(silent=True) or {}
    alt = data.get('altura', 'rey')
    alt_dst = data.get('altura_destino', alt)
    if alt_dst not in ALTURAS:
        return jsonify({'ok': False, 'error': 'altura_destino invalida'})
    org = str(data.get('origen', '')).upper()
    clave = f"{org}|{alt}"
    if clave not in rutas_bajada:
        return jsonify({'ok': False, 'error': f'{org} no tiene ruta en {alt}'})

    def punto(sq, a):
        if sq in calibracion_puntos and a in calibracion_puntos[sq]:
            return calibracion_puntos[sq][a]
        if sq in tabla_escaques and a in tabla_escaques[sq]:
            return tabla_escaques[sq][a]
        return None
    p_org = punto(org, alt)
    if not p_org:
        return jsonify({'ok': False, 'error': f'{org} no tiene punto calibrado'})
    deltas = [{sid: paso[sid] - p_org[sid] for sid in (1, 2, 3, 4)}
              for paso in rutas_bajada[clave]]

    hechos, sin_punto = [], []
    for dst in [str(x).upper() for x in data.get('destinos', [])]:
        p = punto(dst, alt_dst)
        if not p:
            sin_punto.append(dst); continue
        rutas_bajada[f"{dst}|{alt_dst}"] = [
            {sid: max(0, min(1000, p[sid] + d[sid])) for sid in (1, 2, 3, 4)}
            for d in deltas]
        hechos.append(dst)
    guardar_calibracion()
    return jsonify({'ok': True, 'copiada_a': hechos, 'altura_destino': alt_dst,
                    'sin_punto': sin_punto, 'tramos': len(deltas)})

@app.route('/ruta/ms', methods=['POST'])
def ruta_set_ms():
    global ruta_ms
    data = request.get_json(silent=True) or {}
    try:
        v = int(data.get('valor'))
    except (TypeError, ValueError):
        return jsonify({'ok': False, 'error': 'valor invalido'})
    if not (150 <= v <= 3000):
        return jsonify({'ok': False, 'error': 'fuera de rango (150-3000)'})
    ruta_ms = v
    guardar_calibracion()
    return jsonify({'ok': True, 'ruta_ms': ruta_ms})

@app.route('/servos/pausa', methods=['GET', 'POST'])
def servos_pausa():
    """Pausa/reanuda el transito entre tramos. POST {pausado: true/false}."""
    global transito_pausado
    if request.method == 'POST':
        data = request.json or {}
        transito_pausado = bool(data.get('pausado', False))
    return jsonify({'ok': True, 'transito_pausado': transito_pausado})

@app.route('/servos/relajar', methods=['POST'])
@_suspender_luz_durante_movimiento()
def servos_relajar():
    global _torque_liberado_idle, _cancelacion_movimiento
    if not SERVOS_OK:
        return jsonify({'ok': False, 'error': 'Servos no conectados'})
    _cancelacion_movimiento += 1
    for sid, s in servos.items():
        try:
            s.disable_torque()
        except Exception:
            pass
    _torque_liberado_idle = True
    return jsonify({'ok': True})

@app.route('/servos/retomar', methods=['POST'])
@_excluir_movimientos('http')
@_suspender_luz_durante_movimiento()
def servos_retomar():
    """Reactiva torque de forma segura tras Liberar: lee posicion y sincroniza."""
    global _torque_liberado_idle
    if not SERVOS_OK:
        ok, detalle = _inicializar_servos()
        if not ok:
            return jsonify({'ok': False, 'error': detalle}), 503
    pos = {}
    lote_retorno = []
    for sid, s in servos.items():
        try:
            a = s.get_physical_angle()
            s.enable_torque()
            lote_retorno.append((sid, a, 500))
            pos[sid] = g2u(a)
        except Exception:
            pos[sid] = None
    ok = len(pos) == 4 and all(p is not None for p in pos.values())
    if ok:
        try:
            _enviar_lote_servo(lote_retorno)
        except Exception:
            ok = False
    if ok:
        for sm in smooth.values():
            try:
                sm.running = False
                sm.x = 1.0
            except Exception:
                pass
        _torque_liberado_idle = False
        _bit('brazo', 'torque retomado y posiciones sincronizadas', posiciones=pos)
    _luz_confirmar_home(pos if ok else None)
    return jsonify({'ok': ok, 'posiciones': pos,
                    'error': None if ok else 'No se pudo retomar todos los servos'})

# ── Helpers de calibracion 2 alturas ──────────────────────

def altura_de_pieza(pieza):
    """Mapea tipo de pieza a altura de calibracion."""
    if not pieza:
        return 'rey'
    p = str(pieza).lower()
    if p in ('p', 'peon', 'pawn'):
        return 'peon'
    return 'rey'

def _escaques_con_capa(altura):
    """Lista de escaques que tienen grabada la capa indicada."""
    return [sq for sq, pt in calibracion_puntos.items()
            if isinstance(pt, dict) and altura in pt]

@app.route('/calibracion/punto', methods=['POST'])
def calibracion_punto():
    data = request.get_json(silent=True) or {}
    escaque = _escaque_valido(data.get('escaque'))
    if not escaque:
        return jsonify({'ok': False,
                        'error': 'escaque invalido (usar A1 a H8)'}), 400
    altura = data.get('altura', 'rey')
    if altura not in ALTURAS:
        return jsonify({'ok': False, 'error': f'Altura invalida: {altura}'}), 400
    if not SERVOS_OK:
        return jsonify({'ok': False, 'error': 'Servos no conectados'}), 503
    posiciones_int, sospechosos = leer_posiciones_robusta()
    _contar_lecturas(sospechosos)
    if sospechosos or any(posiciones_int.get(sid) is None
                          for sid in (1, 2, 3, 4)):
        return jsonify({'ok': False,
                        'error': 'No pude leer los cuatro servos; no se guardo',
                        'sospechosos': sospechosos,
                        'posiciones': posiciones_int}), 409
    posiciones_int = {sid: int(posiciones_int[sid]) for sid in (1, 2, 3, 4)}
    if escaque not in calibracion_puntos or not isinstance(calibracion_puntos[escaque], dict):
        calibracion_puntos[escaque] = {}
    calibracion_puntos[escaque][altura] = posiciones_int
    puntos_derivados.discard(f'{escaque}:{altura}')   # medido a mano
    guardar_calibracion()
    recalcular_limites()      # la correccion pasa a formar parte del envolvente
    return jsonify({'ok': True, 'altura': altura,
                    'posiciones': posiciones_int,
                    'total_peon': len(_escaques_con_capa('peon')),
                    'total_rey': len(_escaques_con_capa('rey'))})

@app.route('/calibracion/borrar', methods=['POST'])
def calibracion_borrar():
    data = request.json
    escaque = data.get('escaque')
    altura = data.get('altura', 'rey')
    if altura not in ALTURAS:
        return jsonify({'ok': False, 'error': f'Altura invalida: {altura}'})
    borrado = False
    if escaque in calibracion_puntos and altura in calibracion_puntos[escaque]:
        del calibracion_puntos[escaque][altura]
        puntos_derivados.discard(f'{escaque}:{altura}')
        if not calibracion_puntos[escaque]:
            del calibracion_puntos[escaque]
        borrado = True
        guardar_calibracion()
    return jsonify({'ok': True, 'borrado': borrado, 'escaque': escaque, 'altura': altura,
                    'total_peon': len(_escaques_con_capa('peon')),
                    'total_rey': len(_escaques_con_capa('rey'))})

@app.route('/calibracion/puntos_guardados')
def calibracion_puntos_guardados():
    return jsonify({'ok': True,
                    'peon': _escaques_con_capa('peon'),
                    'rey': _escaques_con_capa('rey')})

@app.route('/calibracion/generar', methods=['POST'])
def calibracion_generar():
    bordes = set()
    for col in 'ABCDEFGH':
        bordes.add(col + '1')
        bordes.add(col + '8')
    for fila in range(1, 9):
        bordes.add('A' + str(fila))
        bordes.add('H' + str(fila))

    cols = 'ABCDEFGH'
    total_generado = {}

    for altura in ALTURAS:
        faltantes = [p for p in bordes
                     if p not in calibracion_puntos or altura not in calibracion_puntos[p]]
        if faltantes:
            return jsonify({'ok': False,
                            'error': f'Faltan puntos de borde en altura {altura.upper()}',
                            'altura': altura,
                            'faltantes': sorted(faltantes)})

        for sq in bordes:
            if sq not in tabla_escaques or not isinstance(tabla_escaques[sq], dict):
                tabla_escaques[sq] = {}
            tabla_escaques[sq][altura] = dict(calibracion_puntos[sq][altura])

        for col_i in range(1, 7):
            col = cols[col_i]
            for fila in range(2, 8):
                sq = col + str(fila)
                t_col = col_i / 7.0
                t_fil = (fila - 1) / 7.0
                izq   = calibracion_puntos['A' + str(fila)][altura]
                der   = calibracion_puntos['H' + str(fila)][altura]
                abajo = calibracion_puntos[col + '1'][altura]
                arriba= calibracion_puntos[col + '8'][altura]
                p = {}
                for sid in [1, 2, 3, 4]:
                    interp_fila = izq[sid] * (1 - t_col) + der[sid] * t_col
                    interp_col  = abajo[sid] * (1 - t_fil) + arriba[sid] * t_fil
                    p[sid] = int((interp_fila + interp_col) / 2.0)
                if sq not in tabla_escaques or not isinstance(tabla_escaques[sq], dict):
                    tabla_escaques[sq] = {}
                tabla_escaques[sq][altura] = p

        total_generado[altura] = sum(1 for sq in tabla_escaques if altura in tabla_escaques[sq])

    guardar_calibracion()
    return jsonify({'ok': True, 'total': total_generado})

@app.route('/calibracion/tabla')
def calibracion_tabla():
    return jsonify({'ok': True, 'tabla': tabla_escaques})

@app.route('/calibracion/ir_punto', methods=['POST'])
@_excluir_movimientos('http')
def calibracion_ir_punto():
    if not SERVOS_OK:
        return jsonify({'ok': False, 'error': 'Servos no conectados'})
    data = request.get_json(silent=True) or {}
    sq = _escaque_valido(data.get('escaque'))
    if not sq:
        return jsonify({'ok': False,
                        'error': 'escaque invalido (usar A1 a H8)'}), 400
    altura = data.get('altura', 'rey')
    if altura not in ALTURAS:
        return jsonify({'ok': False, 'error': f'Altura invalida: {altura}'}), 400
    pos, origen = _punto_base_fisico(sq, altura)
    if pos is None:
        return jsonify({'ok': False,
                        'error': f'{sq} no tiene altura {altura.upper()} ni grabada '
                                 f'ni en la tabla (generar tabla primero)'})
    r = mover_con_transito(pos, sq_destino=sq, altura=altura)
    real_final = (r or {}).get('posicion_real_final')
    if isinstance(r, dict) and not r.get('ok', True):
        return jsonify({'ok': False, 'escaque': sq, 'altura': altura,
                        'error': r.get('error', 'movimiento detenido'),
                        'objetivo': pos,
                        'posicion_real_final': real_final,
                        'error_final': r.get('error_final')})
    return jsonify({'ok': True, 'escaque': sq, 'altura': altura,
                    'origen': origen,
                    'objetivo': pos,
                    'posiciones': real_final or pos,
                    'posicion_real_final': real_final,
                    'error_aterrizaje': (r or {}).get('error_aterrizaje')})

@app.route('/ir_escaque', methods=['POST'])
@_excluir_movimientos('http')
def ir_escaque():
    if not SERVOS_OK:
        return jsonify({'ok': False, 'error': 'Servos no conectados'})
    data = request.get_json(silent=True) or {}
    sq = _escaque_valido(data.get('escaque'))
    if not sq:
        return jsonify({'ok': False,
                        'error': 'escaque invalido (usar A1 a H8)'}), 400
    altura = data.get('altura', 'rey')
    if altura not in ALTURAS:
        return jsonify({'ok': False, 'error': f'Altura invalida: {altura}'}), 400
    # La página de calibración encadena puntos: el primero posiciona y el
    # siguiente debe reproducir el mismo traslado origen->destino que usa una
    # jugada real. ``sq_origen`` informa a la trayectoria qué despeje de salida
    # corresponde; no activa el electroimán ni modifica el tablero lógico.
    sq_origen = None
    if data.get('origen_escaque') not in (None, ''):
        sq_origen = _escaque_valido(data.get('origen_escaque'))
        if not sq_origen:
            return jsonify({'ok': False,
                            'error': 'origen de trayectoria invalido'}), 400
        altura_origen = data.get('origen_altura', altura)
        if altura_origen != altura:
            return jsonify({'ok': False,
                            'error': 'origen y destino deben usar la misma altura'}), 400
        pos_origen, _ = _punto_base_fisico(sq_origen, altura)
        if pos_origen is None:
            return jsonify({'ok': False,
                            'error': f'{sq_origen} no tiene altura {altura.upper()}'}), 400
    pos, origen = _punto_base_fisico(sq, altura)
    if pos is None:
        return jsonify({'ok': False,
                        'error': f'{sq} no tiene altura {altura.upper()} ni grabada ni en la tabla'})
    _bit('brazo', 'PRUEBA TRAYECTORIA desde calibracion',
         origen=sq_origen or 'posición actual', destino=sq, altura=altura,
         activa_electroiman=False)
    r = mover_con_transito(pos, sq_destino=sq,
                           sq_origen=sq_origen, altura=altura)
    real_final = (r or {}).get('posicion_real_final')
    if isinstance(r, dict) and not r.get('ok', True):
        return jsonify({'ok': False, 'escaque': sq, 'altura': altura,
                        'error': r.get('error', 'movimiento detenido'),
                        'objetivo': pos,
                        'posicion_real_final': real_final,
                        'error_final': r.get('error_final')})
    return jsonify({'ok': True, 'escaque': sq, 'altura': altura,
                    'objetivo': pos,
                    'posiciones': real_final or pos,
                    'posicion_real_final': real_final,
                    'origen': origen,
                    'trayectoria_desde': sq_origen,
                    'activa_electroiman': False,
                    'error_aterrizaje': (r or {}).get('error_aterrizaje')})

@app.route('/sistema/apagar', methods=['POST'])
def sistema_apagar():
    """Apaga BROKIE de forma ordenada: suelta la pieza, se repliega a home y
    recien ahi corta el torque y apaga la Pi. Cortar la energia con el brazo
    extendido lo deja caer de golpe."""
    import subprocess
    try:
        guardar_calibracion()            # 0. asegurar los ajustes en disco
        _em(False)                       # 1. soltar la pieza SIEMPRE primero
        if SERVOS_OK:
            try:                         # 2. replegarse a home
                mover_a_home()
            except Exception:
                pass
            time.sleep(0.4)
            for sid, s in servos.items():   # 3. liberar torque
                try:
                    s.disable_torque()
                except Exception:
                    pass
        try:
            subprocess.run(['sync'], timeout=10)
        except Exception:
            pass
        subprocess.Popen(['sudo', 'shutdown', '-h', 'now'])
        return jsonify({'ok': True, 'mensaje': 'BROKIE se repliega y se apaga...'})
    except Exception as e:
        return jsonify({'ok': False, 'error': str(e)})

# ── PRE-CALIBRACION POR BORDES ────────────────────────────
# Con las 4 ESQUINAS medidas (A1, H1, A8, H8) se generan los 28 puntos de borde
# por interpolacion. Los bordes alimentan luego la bilineal de /calibracion/generar.
# La muñeca NUNCA se interpola: se recalcula con la formula de perpendicularidad.

ESQUINAS = ('A1', 'H1', 'A8', 'H8')
BORDES_COLS = 'ABCDEFGH'

def _lista_bordes():
    """Los 28 escaques de borde: fila 1, fila 8, columna A, columna H."""
    b = set()
    for col in BORDES_COLS:
        b.add(col + '1'); b.add(col + '8')
    for fila in range(1, 9):
        b.add('A' + str(fila)); b.add('H' + str(fila))
    return sorted(b)

def _interp(p0, p1, t):
    """Interpola base/hombro/codo; deriva la muñeca por perpendicularidad."""
    h = int(round(p0[2] + (p1[2] - p0[2]) * t))
    c = int(round(p0[3] + (p1[3] - p0[3]) * t))
    return {1: int(round(p0[1] + (p1[1] - p0[1]) * t)),
            2: h, 3: c, 4: muneca_perp(h, c)}

def _bordes_desde_esquinas(esq):
    """esq = dict con A1,H1,A8,H8 (cada uno {1..4}) -> los 28 bordes."""
    A1, H1, A8, H8 = esq['A1'], esq['H1'], esq['A8'], esq['H8']
    out = {}
    for i, col in enumerate(BORDES_COLS):          # filas 1 y 8: por columna
        t = i / 7.0
        out[col + '1'] = _interp(A1, H1, t)
        out[col + '8'] = _interp(A8, H8, t)
    for fila in range(1, 9):                        # columnas A y H: por fila
        t = (fila - 1) / 7.0
        out['A' + str(fila)] = _interp(A1, A8, t)
        out['H' + str(fila)] = _interp(H1, H8, t)
    return out

def _esquinas_de(altura):
    """Devuelve las 4 esquinas grabadas en esa altura, o None si falta alguna."""
    esq = {}
    for sq in ESQUINAS:
        pt = calibracion_puntos.get(sq)
        if not pt or altura not in pt:
            return None
        esq[sq] = pt[altura]
    return esq

def _offset_rey_peon():
    """Promedio de (peon - rey) en los escaques que tengan las DOS alturas.
    Devuelve (d_hombro, d_codo, cantidad) o None si no hay ninguno."""
    difs = []
    for sq, pt in calibracion_puntos.items():
        if not (isinstance(pt, dict) and 'rey' in pt and 'peon' in pt):
            continue
        if f'{sq}:rey' in puntos_derivados or f'{sq}:peon' in puntos_derivados:
            continue                                   # derivado: no es una medicion
        difs.append((pt['peon'][2] - pt['rey'][2], pt['peon'][3] - pt['rey'][3]))
    if not difs:
        return None
    return (int(round(sum(d[0] for d in difs) / len(difs))),
            int(round(sum(d[1] for d in difs) / len(difs))),
            len(difs))

# ── PRE-CALIBRACION: 4 esquinas -> 28 bordes ──────────────
# Flujo: 1) grabar A1, H1, A8, H8 en altura REY (como cualquier punto, con el
#           boton de guardar del calibrador, con el brazo puesto a mano)
#        2) grabar UN peon en cualquier escaque que ya tenga REY (da el offset)
#        3) POST /precalibracion/expandir -> completa los 28 bordes en las 2
#           alturas. Despues, "Generar tabla" interpola el interior.
# La muñeca NUNCA se interpola: se recalcula con la formula de perpendicularidad.

ESQUINAS_PRECAL = ('A1', 'H1', 'A8', 'H8')

def _deltas_peon_medidos():
    """Todos los escaques con las DOS alturas: {escaque: {2:dh, 3:dc}}."""
    out = {}
    for sq, pt in calibracion_puntos.items():
        if isinstance(pt, dict) and 'rey' in pt and 'peon' in pt:
            r, p = pt['rey'], pt['peon']
            if all(k in r and k in p for k in (2, 3)):
                out[sq] = {2: p[2] - r[2], 3: p[3] - r[3]}
    return out

def _delta_peon_medido():
    """(delta, escaque) del primero encontrado. (None, None) si no hay ninguno."""
    ds = _deltas_peon_medidos()
    if not ds:
        return None, None
    sq = next(iter(ds))
    return ds[sq], sq

def _interp_borde(p0, p1, t):
    """Interpola base/hombro/codo entre dos puntos; la muñeca se deriva."""
    h = int(round(p0[2] + (p1[2] - p0[2]) * t))
    c = int(round(p0[3] + (p1[3] - p0[3]) * t))
    return {1: int(round(p0[1] + (p1[1] - p0[1]) * t)),
            2: h, 3: c, 4: muneca_perp(h, c)}

@app.route('/precalibracion/estado')
def precalibracion_estado():
    """Que falta para poder expandir: esquinas sin grabar y offset del peon."""
    faltan = [sq for sq in ESQUINAS_PRECAL
              if sq not in calibracion_puntos or 'rey' not in calibracion_puntos[sq]]
    todos = _deltas_peon_medidos()
    delta, sq_delta = _delta_peon_medido()
    distintos = sorted({(v[2], v[3]) for v in todos.values()})
    return jsonify({'ok': True,
                    'esquinas': list(ESQUINAS_PRECAL),
                    'faltan_esquinas': faltan,
                    'delta_peon': delta,
                    'delta_desde': sq_delta,
                    'deltas_encontrados': todos,
                    'aviso': ('Hay deltas de peon distintos entre si: se usa el de '
                              f'{sq_delta}. Manda delta_peon en el body para elegir.'
                              if len(distintos) > 1 else None),
                    'listo': (not faltan) and (delta is not None)})

@app.route('/precalibracion/expandir', methods=['POST'])
def precalibracion_expandir():
    """Genera los 28 puntos de BORDE en las 2 alturas desde las 4 esquinas REY.
    Body opcional: {'delta_peon': {'2': 6, '3': 45},   # si falta, se auto-mide
                    'sobrescribir': false}             # true = pisa lo ya grabado
    Las 4 esquinas medidas a mano NUNCA se sobrescriben."""
    data = request.get_json(silent=True) or {}
    faltan = [sq for sq in ESQUINAS_PRECAL
              if sq not in calibracion_puntos or 'rey' not in calibracion_puntos[sq]]
    if faltan:
        return jsonify({'ok': False, 'faltan_esquinas': faltan,
                        'error': 'Faltan esquinas en altura REY: ' + ', '.join(faltan)})

    d = data.get('delta_peon')
    if d:
        try:
            delta = {2: int(d.get('2', d.get(2, 0))), 3: int(d.get('3', d.get(3, 0)))}
        except (TypeError, ValueError):
            return jsonify({'ok': False, 'error': 'delta_peon invalido'})
        origen_delta = 'manual'
    else:
        delta, origen_delta = _delta_peon_medido()
        if delta is None:
            return jsonify({'ok': False,
                            'error': 'No hay ningun escaque con las 2 alturas. '
                                     'Graba un peon en un escaque ya calibrado en REY, '
                                     'o manda delta_peon en el body.'})

    sobrescribir = bool(data.get('sobrescribir', False))
    A1 = calibracion_puntos['A1']['rey']; H1 = calibracion_puntos['H1']['rey']
    A8 = calibracion_puntos['A8']['rey']; H8 = calibracion_puntos['H8']['rey']

    cols = 'ABCDEFGH'
    bordes = {}
    for i, col in enumerate(cols):                 # filas 1 y 8: por columna
        t = i / 7.0
        bordes[col + '1'] = _interp_borde(A1, H1, t)
        bordes[col + '8'] = _interp_borde(A8, H8, t)
    for fila in range(1, 9):                       # columnas A y H: por fila
        t = (fila - 1) / 7.0
        bordes['A' + str(fila)] = _interp_borde(A1, A8, t)
        bordes['H' + str(fila)] = _interp_borde(H1, H8, t)

    escritos, respetados = [], []
    for sq, p in bordes.items():
        if sq not in calibracion_puntos or not isinstance(calibracion_puntos[sq], dict):
            calibracion_puntos[sq] = {}
        pe = {1: p[1],
              2: max(0, min(1000, p[2] + delta[2])),
              3: max(0, min(1000, p[3] + delta[3]))}
        pe[4] = muneca_perp(pe[2], pe[3])
        for altura, valor in (('rey', p), ('peon', pe)):
            ya = altura in calibracion_puntos.get(sq, {})
            if ya and f'{sq}:{altura}' not in puntos_derivados:
                respetados.append(f'{sq}/{altura} (medido)')   # nunca pisar lo medido
                continue
            if sq in ESQUINAS_PRECAL and altura == 'rey':
                respetados.append(f'{sq}/rey (medido)')
                continue
            if altura in calibracion_puntos[sq] and not sobrescribir:
                respetados.append(f'{sq}/{altura}')
                continue
            calibracion_puntos[sq][altura] = dict(valor)
            escritos.append(f'{sq}/{altura}')

    guardar_calibracion()
    recalcular_limites()
    _todos = _deltas_peon_medidos()
    _distintos = sorted({(v[2], v[3]) for v in _todos.values()})
    return jsonify({'ok': True,
                    'delta_peon': delta, 'origen_delta': origen_delta,
                    'aviso': ('Habia deltas de peon distintos; se uso el de '
                              f'{origen_delta}.' if len(_distintos) > 1 else None),
                    'escritos': len(escritos), 'respetados': len(respetados),
                    'detalle_escritos': sorted(escritos),
                    'detalle_respetados': sorted(respetados),
                    'total_peon': len(_escaques_con_capa('peon')),
                    'total_rey': len(_escaques_con_capa('rey')),
                    'siguiente': 'Ahora tocar "Generar tabla" para el interior.'})

# ── MODELO GEOMETRICO ─────────────────────────────────────
# El brazo llega girando la base: hombro y codo dependen SOLO de la distancia
# radial R del eje de la base al escaque (todos los escaques estan a la misma
# altura), y la base es un atan puro. Interpolar lineal en el tablero corta la
# cuerda de esa curva -> error maximo en el centro.
CASILLA_MM = 31.2          # tablero 25cm / 8
U_HOMBRO_POR_MM = 1.2      # ~36u de hombro = 3cm (ATERRIZAJE_HOMBRO)
RATIO_CODO_BAJADA = 1.39   # codo cierra 1.39u por cada u de hombro que baja
GRADOS_POR_U = 0.24        # 240 grados / 1000 unidades

def _ms_aterrizaje(desde, hasta):
    """Tiempo del aterrizaje segun el recorrido, para velocidad pareja."""
    rec = max((abs(hasta[sid] - desde[sid]) for sid in (1, 2, 3, 4)
               if desde.get(sid) is not None and hasta.get(sid) is not None),
              default=0)
    v = aterrizaje_vel if aterrizaje_vel > 0 else 0.12
    return int(max(aterrizaje_ms, min(4000, rec / v)))

def _xy_escaque(sq):
    """Centro del escaque en mm, con origen en el centro de la fila 1."""
    return ((ord(sq[0].upper()) - 65 - 3.5) * CASILLA_MM,
            (int(sq[1]) - 1) * CASILLA_MM)

def _ajustar_eje_base(muestras):
    """muestras: [(x, y, u1)] -> (bx, by, B0, rms). Busqueda local contractiva."""
    def _e(bx, by):
        ths = [math.degrees(math.atan2(x - bx, y - by)) / GRADOS_POR_U
               for x, y, _ in muestras]
        B0 = sum(u1 + t for (_, _, u1), t in zip(muestras, ths)) / len(muestras)
        return sum((B0 - t - u1) ** 2 for (_, _, u1), t in zip(muestras, ths)), B0
    bx, by, paso = 0.0, -150.0, 40.0
    for _ in range(60):
        cands = [(bx + dx * paso, by + dy * paso) for dx in (-1, 0, 1) for dy in (-1, 0, 1)]
        _, bx, by = sorted((_e(a, b)[0], a, b) for a, b in cands)[0]
        paso *= 0.75
    e, B0 = _e(bx, by)
    return bx, by, B0, math.sqrt(e / len(muestras))

def _fit_poly(xs, ys, grado):
    """Minimos cuadrados en x centrado. Devuelve (coefs, x0) o None."""
    n = grado + 1
    x0 = sum(xs) / len(xs)
    t = [x - x0 for x in xs]
    A = [[sum(v ** (i + j) for v in t) for j in range(n)] for i in range(n)]
    b = [sum(y * (v ** i) for v, y in zip(t, ys)) for i in range(n)]
    for i in range(n):
        p = max(range(i, n), key=lambda r: abs(A[r][i]))
        A[i], A[p] = A[p], A[i]; b[i], b[p] = b[p], b[i]
        if abs(A[i][i]) < 1e-12:
            return None
        for r in range(n):
            if r == i:
                continue
            f = A[r][i] / A[i][i]
            for c in range(i, n):
                A[r][c] -= f * A[i][c]
            b[r] -= f * b[i]
    return [b[i] / A[i][i] for i in range(n)], x0

TOL_RADIO_MM = 8.0   # radios mas cercanos que esto son el MISMO anillo

def _agrupar_radios(rs, ys):
    """Agrupa (radio, valor) por cercania y promedia. Evita micro-tramos entre
    dos anclas casi al mismo radio, que dan pendientes absurdas al extrapolar."""
    orden = sorted(zip(rs, ys))
    grupos = []
    for r, y in orden:
        if grupos and r - grupos[-1][0][-1] <= TOL_RADIO_MM:
            grupos[-1][0].append(r); grupos[-1][1].append(y)
        else:
            grupos.append(([r], [y]))
    return [(sum(g) / len(g), sum(v) / len(v)) for g, v in grupos]

def _fit_tramos(xs, ys):
    """Tramos lineales entre anillos de radio (promediando cada anillo)."""
    return ('tramos', _agrupar_radios(xs, ys))

def _evaluar_poly(fit, x):
    """Evalua un ajuste: ('tramos', pares) o (coefs, x0) polinomico."""
    if isinstance(fit, tuple) and len(fit) == 2 and fit[0] == 'tramos':
        pares = fit[1]
        if x <= pares[0][0]:
            (x0, y0), (x1, y1) = pares[0], pares[1] if len(pares) > 1 else pares[0]
        elif x >= pares[-1][0]:
            (x0, y0), (x1, y1) = (pares[-2] if len(pares) > 1 else pares[-1]), pares[-1]
        else:
            for i in range(len(pares) - 1):
                if pares[i][0] <= x <= pares[i + 1][0]:
                    (x0, y0), (x1, y1) = pares[i], pares[i + 1]
                    break
        if x1 == x0:
            return y0
        return y0 + (y1 - y0) * (x - x0) / (x1 - x0)
    coefs, x0 = fit
    return sum(c * ((x - x0) ** i) for i, c in enumerate(coefs))

def _nota_ajuste(info):
    n = info.get('rey', {}).get('radios_distintos', 0)
    if n >= 4:
        return 'OK: tramos lineales entre anillos. Sumar mas anclas solo afina.'
    if n == 3:
        return 'Parabola. Medi un escaque de fila 6-7 (D6/D7) y sumalo a anclas.'
    return 'Recta. Medi un escaque del centro (D4) y sumalo a anclas.'

def _geometrico(data):
    """Genera los 64 escaques x 2 alturas con el modelo geometrico, usando como
    anclas los escaques MEDIDOS a mano.
    Body opcional: {'anclas': ['A1','H1','A8','H8','D4'],   # default: 4 esquinas
                    'delta_peon': {'2': 17, '3': 0}}
    Con 2 distancias radiales distintas ajusta una recta; con 3 o mas, una
    parabola (capta la curvatura del brazo)."""
    anclas = [str(s).upper() for s in data.get('anclas', list(ESQUINAS_PRECAL))]
    # El eje de la base se ajusta con SUS PROPIAS anclas (por defecto las 4
    # esquinas): son las mejor colocadas y dan el atan casi exacto. Un escaque
    # del centro sirve para la curvatura radial, pero su error lateral de
    # colocacion a mano ensuciaria el ajuste angular.
    anclas_base = [str(s).upper() for s in data.get('anclas_base', list(ESQUINAS_PRECAL))]
    # correccion vertical global de TODO lo generado (mm). + = mas abajo.
    try:
        bajar_mm = float(data.get('bajar_mm', 0) or 0)
    except (TypeError, ValueError):
        return ({'ok': False, 'error': 'bajar_mm invalido'})
    if abs(bajar_mm) > 15:
        return ({'ok': False, 'error': 'bajar_mm fuera de rango seguro (+-15mm)'})

    faltan = [sq for sq in set(anclas) | set(anclas_base)
              if sq not in calibracion_puntos or 'rey' not in calibracion_puntos[sq]]
    if faltan:
        return ({'ok': False, 'error': 'Anclas sin altura REY: ' + ', '.join(sorted(faltan))})

    # 1. eje de la base a partir del servo 1 de las anclas_base
    muestras = []
    for sq in anclas_base:
        x, y = _xy_escaque(sq)
        muestras.append((x, y, calibracion_puntos[sq]['rey'][1]))
    if len(muestras) < 3:
        return ({'ok': False, 'error': 'Hacen falta al menos 3 anclas de base'})
    bx, by, B0, rms = _ajustar_eje_base(muestras)

    def radio(sq):
        x, y = _xy_escaque(sq)
        return math.hypot(x - bx, y - by)

    # 2. hombro/codo en funcion de R, por altura
    fits, info = {}, {}
    fits_mun = {}
    for altura in ALTURAS:
        rs, hs, cs, ms = [], [], [], []
        for sq in anclas:
            pt = calibracion_puntos.get(sq, {})
            if altura in pt:
                rs.append(radio(sq)); hs.append(pt[altura][2]); cs.append(pt[altura][3])
                if pt[altura].get(4) is not None:
                    ms.append(pt[altura][4])
        distintos = len(_agrupar_radios(rs, hs)) if rs else 0
        if distintos >= 2:
            modo = str(data.get('modo', 'auto')).lower()
            usar_tramos = (modo == 'tramos') or (modo == 'auto' and distintos >= 4)
            # la MUÑECA tambien por radio: la formula de perpendicularidad es
            # un ajuste global y se desvia hasta 13u (3 grados) segun el sector.
            if len(ms) == len(rs) and _agrupar_radios(rs, ms) and distintos >= 2:
                fits_mun[altura] = (_fit_tramos(rs, ms) if usar_tramos
                                    else _fit_poly(rs, ms, 2 if distintos >= 3 else 1))
            if usar_tramos:
                fits[altura] = (_fit_tramos(rs, hs), _fit_tramos(rs, cs))
                info[altura] = {'anclas': len(rs), 'radios_distintos': distintos,
                                'modo': 'tramos lineales'}
            else:
                g = 2 if distintos >= 3 else 1
                fits[altura] = (_fit_poly(rs, hs, g), _fit_poly(rs, cs, g))
                info[altura] = {'anclas': len(rs), 'radios_distintos': distintos,
                                'modo': f'polinomio grado {g}'}
    if 'rey' not in fits:
        return ({'ok': False,
                        'error': 'Las anclas REY no dan 2 distancias radiales distintas'})
    # el peon solo usa ajuste propio si esta tan bien muestreado como el rey;
    # si no, se deriva del rey (que tiene la curva buena) + delta medido
    if 'peon' in fits and info['peon']['radios_distintos'] < info['rey']['radios_distintos']:
        del fits['peon']
        info['peon'] = {'derivado_de_rey': True,
                        'motivo': 'menos anillos medidos que REY'}

    # 3. si el peon no alcanza para su propio ajuste, se deriva del rey + delta
    d = data.get('delta_peon')
    delta = None
    if 'peon' not in fits:
        if d:
            delta = {2: int(d.get('2', d.get(2, 0))), 3: int(d.get('3', d.get(3, 0)))}
        else:
            delta, _o = _delta_peon_medido()
        if delta is None:
            return ({'ok': False,
                            'error': 'Sin datos para la capa PEON (medi un peon o manda delta_peon)'})
        info['peon'] = {'derivado_de_rey': True, 'delta': delta}

    # 4. generar los 64 x 2
    generados = 0
    for col in 'ABCDEFGH':
        for fila in range(1, 9):
            sq = col + str(fila)
            r = radio(sq)
            x, y = _xy_escaque(sq)
            base = int(round(B0 - math.degrees(math.atan2(x - bx, y - by)) / GRADOS_POR_U))
            base = max(0, min(1000, base))
            fh, fc = fits['rey']
            h_rey = int(round(_evaluar_poly(fh, r))); c_rey = int(round(_evaluar_poly(fc, r)))
            capas = {'rey': (h_rey, c_rey)}
            if 'peon' in fits:
                fh2, fc2 = fits['peon']
                capas['peon'] = (int(round(_evaluar_poly(fh2, r))),
                                 int(round(_evaluar_poly(fc2, r))))
            else:
                capas['peon'] = (h_rey + delta[2], c_rey + delta[3])
            for altura, (h, c) in capas.items():
                _fm = fits_mun.get(altura) or fits_mun.get('rey')
                _h0, _c0 = h, c          # pose de la capa ANTES de bajar_mm
                if bajar_mm:
                    dh = bajar_mm * U_HOMBRO_POR_MM
                    h += dh                      # hombro + = baja
                    c -= dh * RATIO_CODO_BAJADA  # codo cierra = descenso vertical
                h = int(round(max(0, min(1000, h))))
                c = int(round(max(0, min(1000, c))))
                if _fm is not None:
                    mun = round(_evaluar_poly(_fm, r))
                    if altura not in fits_mun:
                        # la curva es de OTRA capa (el rey): corregir la muñeca
                        # por la diferencia de pose entre capas, si no la campana
                        # queda inclinada ~4 grados en la capa derivada.
                        mun += muneca_perp(_h0, _c0) - muneca_perp(h_rey, c_rey)
                    mun = int(max(MUNECA_MIN, min(1000, mun)))
                    if bajar_mm:      # al bajar, la muñeca sube para compensar
                        mun = int(max(MUNECA_MIN, min(1000, mun + round(
                            bajar_mm * U_HOMBRO_POR_MM * (1.0143 + 0.9837 * RATIO_CODO_BAJADA)))))
                else:
                    mun = muneca_perp(h, c)
                p = {1: base, 2: h, 3: c, 4: mun}
                if sq not in tabla_escaques or not isinstance(tabla_escaques[sq], dict):
                    tabla_escaques[sq] = {}
                tabla_escaques[sq][altura] = p
                # los puntos NO ancla se reescriben para que no tapen la tabla
                if (sq in calibracion_puntos and altura in calibracion_puntos[sq]
                        and sq not in anclas
                        and f'{sq}:{altura}' in puntos_derivados):
                    calibracion_puntos[sq][altura] = dict(p)
                if sq not in anclas and f'{sq}:{altura}' not in puntos_derivados \
                        and altura not in calibracion_puntos.get(sq, {}):
                    puntos_derivados.add(f'{sq}:{altura}')
                generados += 1

    guardar_calibracion()
    recalcular_limites()
    return ({'ok': True,
                    'anclas_base': anclas_base,
                    'anclas_radiales': anclas,
                    'eje_base': {'lateral_mm': round(bx, 1),
                                 'detras_fila1_mm': round(-by, 1),
                                 'cero_base_u': round(B0, 1),
                                 'rms_u': round(rms, 2)},
                    'ajuste': info,
                    'muneca': {a: 'ajustada por radio' for a in fits_mun} or 'formula global',
                    'generados': generados,
                    'bajar_mm': bajar_mm,
                    'nota': _nota_ajuste(info)})



@app.route('/precalibracion/geometrico', methods=['POST'])
def precalibracion_geometrico():
    return jsonify(_geometrico(request.get_json(silent=True) or {}))

@app.route('/precalibracion/recalcular', methods=['POST'])
def precalibracion_recalcular():
    """Boton de ACTUALIZAR: rehace la tabla usando como anclas TODOS los puntos
    grabados a mano. Cada correccion pasa a mandar sobre su anillo de radio.
    Body opcional: {'bajar_mm':0, 'extra':['C5'], 'anclas_base':[...]}"""
    data = dict(request.get_json(silent=True) or {})
    medidos = sorted({sq for sq, pt in calibracion_puntos.items()
                      if isinstance(pt, dict) and 'rey' in pt
                      and f'{sq}:rey' not in puntos_derivados})
    extra = [str(x).upper() for x in data.get('extra', [])]
    anclas = sorted(set(medidos) | set(extra) | set(ESQUINAS_PRECAL))
    data['anclas'] = anclas
    r = _geometrico(data)
    r['anclas_usadas'] = anclas
    r['medidos_a_mano'] = medidos
    return jsonify(r)

@app.route('/precalibracion/medidos', methods=['GET', 'POST'])
def precalibracion_medidos():
    """Que puntos cuentan como MEDIDOS a mano (los que no estan marcados como
    derivados). GET lista. POST {'escaques':[...],'altura':'rey','medido':true}
    fuerza el estado, para los que ya existian antes de registrarse el origen."""
    if request.method == 'POST':
        data = request.get_json(silent=True) or {}
        altura = data.get('altura', 'rey')
        if altura not in ALTURAS:
            return jsonify({'ok': False, 'error': 'altura invalida'})
        medido = bool(data.get('medido', True))
        sin_punto = []
        for sq in [str(x).upper() for x in data.get('escaques', [])]:
            if sq not in calibracion_puntos or altura not in calibracion_puntos[sq]:
                sin_punto.append(sq); continue
            if medido:
                puntos_derivados.discard(f'{sq}:{altura}')
            else:
                puntos_derivados.add(f'{sq}:{altura}')
        guardar_calibracion()
    out = {}
    for alt in ALTURAS:
        out[alt] = sorted(sq for sq, pt in calibracion_puntos.items()
                          if isinstance(pt, dict) and alt in pt
                          and f'{sq}:{alt}' not in puntos_derivados)
    return jsonify({'ok': True, 'medidos': out,
                    'derivados': sorted(puntos_derivados)})

def _vigilante_reinicio():
    """Sale del proceso cuando se cumplen las horas Y el brazo esta quieto.
    systemd (Restart=always) lo vuelve a levantar en limpio."""
    import os
    while True:
        time.sleep(30)
        try:
            if not reinicio_horas or reinicio_horas <= 0:
                continue
            if time.time() - arranque_ts < reinicio_horas * 3600:
                continue
            if time.time() - ultimo_mov_ts < reinicio_quieto_s:
                continue
            if transito_pausado:
                continue
            print(f"[reinicio] {reinicio_horas}h encendido y brazo quieto: "
                  f"reiniciando para refrescar el enlace serie")
            os._exit(0)
        except Exception:
            pass

@app.route('/sistema/reinicio_auto', methods=['GET', 'POST'])
def sistema_reinicio_auto():
    """POST {'horas': 1, 'quieto_s': 45}. horas=0 desactiva."""
    global reinicio_horas, reinicio_quieto_s
    if request.method == 'POST':
        data = request.get_json(silent=True) or {}
        if data.get('horas') is not None:
            try:
                v = float(data['horas'])
            except (TypeError, ValueError):
                return jsonify({'ok': False, 'error': 'horas invalidas'})
            if not (0 <= v <= 72):
                return jsonify({'ok': False, 'error': 'fuera de rango (0-72)'})
            if v > 0:
                # sin Restart=always el proceso se cierra y NO vuelve
                try:
                    with open('/etc/systemd/system/chess.service') as _f:
                        if 'Restart=always' not in _f.read():
                            return jsonify({'ok': False,
                                'error': 'El servicio no tiene Restart=always: si se '
                                         'cierra no vuelve a levantar. Agregalo antes '
                                         'de activar el reinicio automatico.'})
                except Exception:
                    return jsonify({'ok': False,
                        'error': 'No se pudo verificar Restart=always en el servicio'})
            reinicio_horas = v
        if data.get('quieto_s') is not None:
            reinicio_quieto_s = max(10, int(data['quieto_s']))
    falta = max(0.0, reinicio_horas * 3600 - (time.time() - arranque_ts)) if reinicio_horas else None
    return jsonify({'ok': True, 'reinicio_horas': reinicio_horas,
                    'quieto_s': reinicio_quieto_s,
                    'minutos_para_el_reinicio': round(falta / 60, 1) if falta is not None else None,
                    'quieto_hace_s': round(time.time() - ultimo_mov_ts, 1)})

if not MODO_PRUEBA_SIN_BRAZO:
    _inicializar_servos()

_luz_home_confirmado_al_arrancar = _confirmar_home_arranque_luz()
threading.Thread(target=_vigilar_gy302, daemon=True).start()
if not _luz_home_confirmado_al_arrancar:
    threading.Thread(target=_recuperar_home_arranque_luz, daemon=True).start()
threading.Thread(target=_vigilante_reinicio, daemon=True).start()

def _arrancar_vision():
    """Reactiva la vigilancia si estaba activa al apagar.

    Se espera un poco: al arrancar, los servos todavia se estan enumerando y
    la primera lectura de pose puede fallar. Reintenta unas cuantas veces y
    despues se rinde en silencio (el usuario siempre puede prenderla a mano).
    """
    if vision is None or not vision_activa:
        return
    token = _token_estado_visual()
    for intento in range(10):
        time.sleep(3)
        with _lock_partida:
            if token != _token_estado_visual():
                return
            try:
                ok, det = vision.tomar_referencia()
                if not ok:
                    continue
                # BROKIE 4.0G: TODA referencia válida de partida crea también ancla.
                _fijar_ancla_vision_desde_tablero()
                _bit('vision', 'BROKIE 4.0G.3: arranque automatico fija ancla',
                     fen=tablero.fen(), ancla=_ancla_vision_fisica)
                ok, det = vision.iniciar_vigilancia(callback=_al_detectar_jugada)
                if ok:
                    _bit('vision', 'vigilancia reactivada sola al arrancar',
                         intento=intento + 1)
                    return
            except Exception as e:
                _bit('vision', 'no pude reactivar la vigilancia', error=str(e))
    _bit('vision', 'no se pudo reactivar la vigilancia al arrancar '
                   '(prenderla a mano desde la pantalla)')


if vision is not None and vision_activa:
    threading.Thread(target=_arrancar_vision, daemon=True).start()


if __name__ == '__main__':
    # debug=False: el debugger de Werkzeug ocupa RAM y expone una consola de
    # ejecucion de codigo en el navegador. threaded=True para que la web
    # responda mientras el brazo se mueve.
    app.run(host='0.0.0.0', port=5000, debug=False, use_reloader=False,
            threaded=True)
