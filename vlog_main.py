# -*- coding: utf-8 -*-
import time
import select
import socket
import pickle
import argparse
import importlib
import functools
import re
import inspect
from typing import Dict, List, Tuple
from urllib.parse import quote, unquote
from enum import Enum
from xmlrpc.client import ServerProxy
from subprocess import Popen
from VLOG_Majsoul.VLOGMAJSOUL import MajsoulVLOG
import numpy as np

import majsoul_wrapper as sdk
from majsoul_wrapper import all_tiles, Operation
from datetime import datetime



PRINT_LOG = True  # whether print args when enter handler

def dump_args(func):
    #Decorator to print function call details - parameters names and effective values.
    @functools.wraps(func)
    def wrapper(*args, **kwargs):
        if PRINT_LOG:
            func_args = inspect.signature(func).bind(*args, **kwargs).arguments
            func_args_str = ', '.join('{} = {!r}'.format(*item)
                                      for item in func_args.items())
            func_args_str = re.sub(r' *self.*?=.*?, *', '', func_args_str)
            #print(f'{func.__module__}.{func.__qualname__} ( {func_args_str} )')
            print(f'{func.__name__} ({func_args_str})')
        start = time.time()
        r = func(*args, **kwargs)
        end = time.time()
        time_used = end - start
        if PRINT_LOG and time_used > 0.5:
            print(f'{func.__name__} time_used = {time_used}')
        return r
    return wrapper

def log_time(func):
    @functools.wraps(func)
    def wrapper(*args, **kwargs):
        if PRINT_LOG:
            func_args = inspect.signature(func).bind(*args, **kwargs).arguments
            func_args_str = ', '.join('{} = {!r}'.format(*item)
                                      for item in func_args.items())
            func_args_str = re.sub(r' *self.*?=.*?, *', '', func_args_str)
            #print(f'{func.__module__}.{func.__qualname__} ( {func_args_str} )')
            #print(f'{func.__name__} ({func_args_str})')
        start = time.time()
        r = func(*args, **kwargs)
        end = time.time()
        time_used = end - start
        if PRINT_LOG and time_used > 0.5:
            print(f'{func.__name__} time_used = {time_used}')
        return r
    return wrapper


class State(Enum):  # 当前状态是否改变
    Start = 0
    Enter = 1
    Unchanged = 2


class CardRecorder:
    # 由于雀魂不区分相同牌的编号，但天凤区分tile136，需要根据出现的顺序转换
    def __init__(self):
        self.clear()

    def clear(self):
        self.cardDict = {tile: 0 for tile in sdk.all_tiles}

    def majsoul2tenhou(self, tile: str, count=True) -> Tuple[int, int]:
        # tileStr to (tile136,tile34) (e.g. '0s' -> (88,37)
        t = 'mpsz'.index(tile[-1])
        if tile[0] == '0':
            #红宝牌
            return [(16, 35), (52, 36), (88, 37)][t]
        else:
            tile136 = (ord(tile[0])-ord('0')-1)*4+9*4*t
            if tile[0] == '5' and t < 3:  # 5 m|p|s
                tile136 += 1
            if count:
                tile136 += self.cardDict[tile]
                self.cardDict[tile] += 1
            assert(0 <= self.cardDict[tile] <= 4)
            tile34 = tile136//4
            return (tile136, tile34)
    
    def tenhou2majsoul(self, tile136=None, tile34=None):
        # (tile136,tile34) to tileStr
        if tile136 != None:
            assert(tile34 == None)
            tile136 = int(tile136)
            if tile136 in (16, 52, 88):
                #红宝牌
                return '0'+'mps'[(16, 52, 88).index(tile136)]
            else:
                return str((tile136//4) % 9+1)+'mpsz'[tile136//36]
        else:
            assert(tile136 == None)
            tile34 = int(tile34)
            if tile34 > 34:
                #红宝牌
                return '0'+'mps'[tile34-35]
            else:
                return str(tile34 % 9+1)+'mpsz'[tile34//9]
    
    def akaToNormal(self, tile:str):
        if tile in ['0m', '0p', '0s']:
            return '5'+tile[1]
        return tile


class AIWrapper(sdk.GUIInterface, sdk.MajsoulHandler):
    # TenHouAI <-> AI_Wrapper <-> Majsoul Interface

    def __init__(self, webdriver_args=[], force_riichi=False):
        super().__init__(chrome_arguments=webdriver_args)
        self.AI_socket = None
        self.msg_file = None
        # 与Majsoul的通信
        self.majsoul_server = ServerProxy(
            "http://127.0.0.1:37247")   # 初始化RPC服务器
        self.liqiProto = sdk.LiqiProto()
        # 牌号转换
        self.cardRecorder = CardRecorder()
        self.force_riichi = force_riichi

    def init(self, AI: MajsoulVLOG, dump_file=None):
        # 设置与AI的socket链接并初始化
        self.AI = AI
        #  与Majsoul的通信
        self.majsoul_history_msg = []   # websocket flow_msg
        self.majsoul_msg_p = 0  # 当前准备解析的消息下标
        self.liqiProto.init()
        # AI上一次input操作的msg_dict(维护tile136一致性)
        self.lastDiscard = None         # 牌桌最后一次出牌tile136，用于吃碰杠牌号
        self.hai = []                   # 我当前手牌的tile136编号(和AI一致)
        self.isLiqi = False             # 当前是否处于立直状态
        self.wait_a_moment = False      # 下次操作是否需要额外等待
        self.lastSendTime = time.time()  # 防止操作过快
        self.pengInfo = dict()          # 记录当前碰的信息，以维护加杠时的一致性
        self.lastOperation = None       # 用于判断吃碰是否需要二次选择
        # tenhou proto dump文件
        self.dump_file = dump_file
        self.need_action = False

    def isPlaying(self) -> bool:
        # 从majsoul websocket中获取数据，并判断数据流是否为对局中
        retry = 3
        n = 0
        while retry > 0:
            try:
                n = self.majsoul_server.get_len()
                break
            except:
                retry -= 1
        liqiProto = sdk.LiqiProto()
        if n == 0:
            return False
        flow = pickle.loads(self.majsoul_server.get_items(0, min(100, n)).data)
        for flow_msg in flow:
            result = liqiProto.parse(flow_msg)
            if result.get('method', '') == '.lq.FastTest.authGame':
                return True
        return False

    def recvFromMajsoul(self):
        # 从majsoul websocket中获取数据，并尝试解析执行。
        # 如果未达到要求无法执行则锁定self.majsoul_msg_p直到下一次尝试。
        retry = 3
        n = 0
        while retry > 0:
            try:
                n = self.majsoul_server.get_len()
                break
            except:
                retry -= 1
        l = len(self.majsoul_history_msg)
        if l < n:
            flow = pickle.loads(self.majsoul_server.get_items(l, n).data)
            self.majsoul_history_msg = self.majsoul_history_msg+flow
            pickle.dump(self.majsoul_history_msg, open(
                'websocket_frames.pkl', 'wb'))
        while self.majsoul_msg_p < n:
            flow_msg = self.majsoul_history_msg[self.majsoul_msg_p]
            result = self.liqiProto.parse(flow_msg)
            failed = self.parse(result)
            if not failed:
                self.majsoul_msg_p += 1
            if result.get('method', '') == '.lq.FastTest.authGame':
                return State.Start
            if result.get('method', '') == '.lq.FastTest.enterGame':
                return State.Enter
        return State.Unchanged

    def send(self, data: bytes):
        #向AI发送tenhou proto数据
        self.need_action = False
        if type(data) == bytes:
            data = data.decode()
        print('send:', data)
        if self.dump_file:
            self.dump_file.write(data)
            self.dump_file.write('\n')
            self.dump_file.flush()
        self.AI.receive_msg(data)
        self.lastSendTime = time.time()

    def actionPurge(self):
        self.need_action = False

    @dump_args
    def actionHandler(self, riichi_candidates=[], can_ron=False, can_tsumo=False, can_push=False):
        self.need_action = True
        self.riichi_candidates = riichi_candidates
        self.can_ron = can_ron
        self.can_tsumo = can_tsumo
        self.can_push = can_push
        pass

    def actionGet(self):
        assert(self.need_action)
        return self.action(riichi_candidates=self.riichi_candidates, can_ron=self.can_ron, 
            can_tsumo=self.can_tsumo, can_push=self.can_push)

    @dump_args
    def action(self, riichi_candidates=[], can_ron=False, can_tsumo=False, can_push=False):
        action_id, if_riichi = self.AI.make_decision(riichi_candidates, can_ron=can_ron, 
            can_tsumo=can_tsumo, can_push = can_push, force_riichi=self.force_riichi)
        return action_id, if_riichi


    def actionDo(self,action_id, if_riichi):
        if if_riichi:
            # 立直
            self.on_Liqi(tile34=action_id)
        elif action_id < 34:
            # 出牌
            self.on_DiscardTile(tile34=action_id)
        elif action_id == 41 or action_id == 46:
            # 立直action 不会被返回
            print(action_id)
            raise NotImplementedError()
        elif action_id >= 34 and action_id <= 45:
            # 回应吃碰杠等
            self.on_ChiPengGang(action_id)
        else:
            print(action_id)
            raise NotImplementedError()
        self.need_action = False
            

    def tenhouDecode(self, msg: str) -> Dict:  # get tenhou protocol msg
        l = []
        msg = str.strip(msg)[1:-2] + ' '
        bv = 0
        last_i = 0
        for i in range(len(msg)):
            if msg[i] == '"':
                bv ^= 1
            elif msg[i] == ' ' and not bv:
                l.append(msg[last_i:i])
                last_i = i + 1
        msg = [str.strip(s) for s in l if len(s) > 0]
        d = {s.split('=')[0]: s.split('=')[1][1:-1] for s in msg[1:]}
        d['opcode'] = msg[0]
        return d

    def tenhouEncode(self, kwargs: Dict) -> str:  # encode tenhou protocol msg
        opcode = kwargs['opcode']
        s = '<' + str(opcode)
        for k, v in kwargs.items():
            if k != 'opcode':
                s += ' ' + str(k) + '="' + str(v) + '"'
        s += '/>\x00'
        return s

    #-------------------------AI回调函数-------------------------

    def on_HELO(self, msg_dict):
        #step 1: init JianYangAI
        self.send(b'<HELO uname="%74%73%74%5F%74%69%6F" auth="20190421-9c033b1f" PF4="9,50,986.91,-4027.0,29,43,71,107,14,1362,162,257,226,135" ratingscale="PF3=1.000000&PF4=1.000000&PF01C=0.582222&PF02C=0.501632&PF03C=0.414869&PF11C=0.823386&PF12C=0.709416&PF13C=0.586714&PF23C=0.378722&PF33C=0.535594&PF1C00=8.000000" rr="PF3=0,0&PF4=272284,0&PF01C=0,0&PF02C=0,0&PF03C=0,0&PF11C=0,0&PF12C=0,0&PF13C=0,0&PF23C=0,0&PF33C=0,0&PF1C00=0,0"/>\x00')

    def on_PXR(self, msg_dict):
        #step 2: init JianYangAI
        self.send(b'<LN n="BgZ1Bdh1Xn1Ik" j="D1C2D2D2D1D12C3B13C1C2B1D12C4D8C1C1B3C2B1C1C1B1B" g="HA3Q1ME1E2BA1Bc4E8Lw3c1Dg12Gc4BQ12BQ4E8M1DM2Bj2Bg2S1t1q1M1BI2S"/>\x00')

    def on_JOIN(self, msg_dict):
        #step 3: init JianYangAI 四人东模式
        self.send(b'<GO type="1" lobby="0" gpid="EE26C0F2-327686F1"/>\x00')
        #step 4: 用户信息
        self.send(('<UN n0="'+quote('tst-tio')+'" n1="'+quote('user1')+'" n2="'+quote('user2')+'" n3="' +
                   quote('user3')+'" dan="9,9,9,0" rate="985.47,1648.57,1379.50,1500.00" sx="M,M,M,M"/>\x00').encode())
        #step 5: fake录像地址
        self.send(
            ('<TAIKYOKU oya="0" log="xxxxxxxxxxxx-xxxx-xxxx-xxxxxxxx"/>\x00').encode())

    #-------------------------Majsoul回调函数-------------------------

    @dump_args
    def beginGame(self):
        #开始整场对局
        self.isMajsoulReady = True
        msg_dict = {}
        self.on_HELO(msg_dict)
        self.on_PXR(msg_dict)
        self.on_JOIN(msg_dict)
        print('BeginGame Game')


    @dump_args
    def newRound(self, chang: int, ju: int, ben: int, liqibang: int, tiles: List[str], scores: List[int], leftTileCount: int, doras: List[str]):
        """
        chang:当前的场风，0~3:东南西北
        ju:当前第几局(0:1局,3:4局，连庄不变)
        liqibang:流局立直棒数量(画面左上角一个红点的棒)
        ben:连装棒数量(画面左上角八个黑点的棒)
        tiles:我的初始手牌
        scores:当前场上四个玩家的剩余分数(从东家开始顺序)
        leftTileCount:剩余牌数
        doras:宝牌列表
        """
        assert(chang*4+ju >= 0)
        assert(len(tiles) in (13, 14) and all(
            tile in all_tiles for tile in tiles))
        assert(leftTileCount == 69)
        assert(all(dora in all_tiles for dora in doras))
        assert(len(doras) == 1)
        self.isLiqi = False
        self.cardRecorder.clear()
        self.pengInfo.clear()
        dora136, _ = self.cardRecorder.majsoul2tenhou(doras[0])
        seed = [chang*4+ju, ben, liqibang, -1, -1, dora136]     # 当前轮数/连庄立直信息
        self.ten = ten = [scores[(self.mySeat+i) % 4] //
                          100 for i in range(4)]  # 当前分数(1ten=100分)
        oya = (4-self.mySeat+ju) % 4      # 0~3 当前轮谁是庄家(我是0)
        if oya == 0:
            self.wait_a_moment = True  # 庄家第一轮多等一会儿
        self.hai = []     # 当前手牌tile136
        for tile in tiles[:13]:
            tile136, _ = self.cardRecorder.majsoul2tenhou(tile)
            self.hai.append(tile136)
        assert(len(seed) == 6)
        assert(len(ten) == 4)
        assert(0 <= oya < 4)
        self.send(('<INIT seed="'+','.join(str(i) for i in seed)+'" ten="'+','.join(str(i)
                                                                                    for i in ten)+'" oya="'+str(oya)+'" hai="'+','.join(str(i) for i in self.hai)+'"/>\x00').encode())
        self.actionPurge()
        if len(tiles) == 14:
            # operation TODO
            self.iDealTile(self.mySeat, tiles[13], leftTileCount, {}, {})

    @dump_args
    def newDora(self, dora: str):
        """
        处理discardTile/dealTile中通知增加明宝牌的信息
        """
        tile136, _ = self.cardRecorder.majsoul2tenhou(dora)
        self.send(self.tenhouEncode({'opcode': 'DORA', 'hai': tile136}))

    @dump_args
    def discardTile(self, seat: int, tile: str, moqie: bool, isLiqi: bool, operation):
        """
        seat:打牌的玩家
        tile:打出的手牌
        moqie:是否是摸切
        isLiqi:当回合是否出牌后立直
        operation:可选动作(吃碰杠)
        """
        assert(0 <= seat < 4)
        assert(tile in sdk.all_tiles)
        if isLiqi:
            msg_dict = {'opcode': 'REACH', 'who': (
                seat-self.mySeat) % 4, 'step': 1}
            self.send(self.tenhouEncode(msg_dict))
            if seat == self.mySeat:
                self.isLiqi = True
        op = 'DEFG'[(seat-self.mySeat) % 4]
        if op == 'D':
            tile136=None
            for t in self.hai:
                if self.cardRecorder.tenhou2majsoul(tile136=t)==tile:
                    tile136=t
                    self.hai.remove(t)
                    break
            assert(tile136!=None)
        else:
            tile136, _ = self.cardRecorder.majsoul2tenhou(tile)
        if moqie:
            op = op.lower()
        msg_dict = {'opcode': op+str(tile136)}
        if operation != None:
            assert(operation.get('seat', 0) == self.mySeat)
            opList = operation.get('operationList', [])
            canChi = any(op['type'] == Operation.Chi.value for op in opList)
            canPeng = any(op['type'] == Operation.Peng.value for op in opList)
            canGang = any(
                op['type'] == Operation.MingGang.value for op in opList)
            canHu = any(op['type'] == Operation.Hu.value for op in opList)
            if canHu:
                msg_dict['t'] = 8
            elif canGang:
                msg_dict['t'] = 3
            elif canPeng:
                msg_dict['t'] = 1
            elif canChi:
                msg_dict['t'] = 4
        self.send(self.tenhouEncode(msg_dict))
        self.lastDiscard = tile136
        self.lastDiscardSeat = seat
        self.lastOperation = operation
        if operation != None:
            self.actionHandler(riichi_candidates=[], can_ron=canHu)
        else:
            self.actionPurge()
        #operation TODO

    @dump_args
    def dealTile(self, seat: int, leftTileCount: int, liqi: Dict):
        """
        seat:摸牌的玩家
        leftTileCount:剩余牌数
        liqi:如果上一回合玩家出牌立直，则紧接着的摸牌阶段有此参数表示立直成功
        """
        assert(0 <= seat < 4)
        assert(type(liqi) == dict or liqi == None)
        if liqi:
            tenhow_seat = (liqi.get('seat', 0)-self.mySeat) % 4
            score = liqi.get('score', 0)
            self.ten[tenhow_seat] = score//100
            msg_dict = {'opcode': 'REACH', 'who': tenhow_seat,
                        'ten': ','.join(str(i) for i in self.ten), 'step': 2}
            self.send(self.tenhouEncode(msg_dict))
        op = 'UVW'[(seat-self.mySeat-1) % 4]
        self.send(('<'+op+'/>\x00').encode())
        self.actionPurge()

    @dump_args
    def iDealTile(self, seat: int, tile: str, leftTileCount: int, liqi: Dict, operation: Dict):
        """
        seat:我自己
        tile:摸到的牌
        leftTileCount:剩余牌数
        liqi:如果上一回合玩家出牌立直，则紧接着的摸牌阶段有此参数表示立直成功
        operation:可选操作列表
        """
        assert(seat == self.mySeat)
        assert(tile in sdk.all_tiles)
        assert(type(liqi) == dict or liqi == None)
        if liqi:
            tenhow_seat = (liqi.get('seat', 0)-self.mySeat) % 4
            score = liqi.get('score', 0)
            self.ten[tenhow_seat] = score//100
            msg_dict = {'opcode': 'REACH', 'who': tenhow_seat,
                        'ten': ','.join(str(i) for i in self.ten), 'step': 2}
            self.send(self.tenhouEncode(msg_dict))
        tile136, _ = self.cardRecorder.majsoul2tenhou(tile)
        self.hai.append(tile136)
        msg_dict = {'opcode': 'T'+str(tile136)}
        riichi_candidates = []
        if operation != None:
            opList = operation.get('operationList', [])
            need_action = (not self.isLiqi) or (len(opList) > 0)
            canJiaGang = any(
                op['type'] == Operation.JiaGang.value for op in opList)
            canLiqi = any(op['type'] == Operation.Liqi.value for op in opList)
            canZimo = any(op['type'] == Operation.Zimo.value for op in opList)
            canHu = any(op['type'] == Operation.Hu.value for op in opList)
            if canZimo or canHu:
                msg_dict['t'] = 16  # 自摸
            elif canLiqi:
                msg_dict['t'] = 32  # 立直
            if canLiqi:
                # riichi_candidates
                liqi_operation = [op for op in opList if op['type'] == Operation.Liqi.value]
                assert(len(liqi_operation) == 1)
                liqi_operation = liqi_operation[0]
                for t in liqi_operation['combination']:
                    t = self.cardRecorder.akaToNormal(t)
                    _, tile34 = self.cardRecorder.majsoul2tenhou(t, count=False)
                    if tile34 not in riichi_candidates:
                        riichi_candidates.append(tile34)
        self.send(self.tenhouEncode(msg_dict))
        if operation != None and need_action:
            self.actionHandler(riichi_candidates=riichi_candidates, can_ron=canHu, can_tsumo=canZimo, can_push=False)
        else:
            self.actionPurge()

    @dump_args
    def chiPengGang(self, type_: int, seat: int, tiles: List[str], froms: List[int], tileStates: List[int]):
        """
        type_:操作类型
        seat:吃碰杠的玩家
        tiles:吃碰杠牌组
        froms:每张牌来自哪个玩家
        tileStates:未知(TODO)
        """
        assert(0 <= seat < 4)
        assert(all(tile in sdk.all_tiles for tile in tiles))
        assert(all(0 <= i < 4 for i in froms))
        assert(seat != froms[-1])
        lastDiscardStr = self.cardRecorder.tenhou2majsoul(
            tile136=self.lastDiscard)
        assert(tiles[-1] == lastDiscardStr)
        tenhou_seat = (seat-self.mySeat) % 4
        from_whom = (froms[-1]-seat) % 4

        def popHai(tile):
            #从self.hai中找到tile并pop
            for tile136 in self.hai:
                if self.cardRecorder.tenhou2majsoul(tile136=tile136) == tile:
                    self.hai.remove(tile136)
                    return tile136
            raise Exception(tile+' not found.')

        if type_ in (0, 1):
            assert(len(tiles) == 3)
            tile1 = self.lastDiscard
            if seat == self.mySeat:
                tile2 = popHai(tiles[1])
                tile3 = popHai(tiles[0])
            else:
                tile2 = self.cardRecorder.majsoul2tenhou(tiles[1])[0]
                tile3 = self.cardRecorder.majsoul2tenhou(tiles[0])[0]
            tile136s = sorted([tile1, tile2, tile3])
            t1, t2, t3 = (i % 4 for i in tile136s)
            if type_ == 0:
                # 吃
                assert(tiles[0] != tiles[1] != tiles[2])
                base = tile136s[0]//4  # 最小牌tile34
                base = base//9*7 + base % 9
                called = tile136s.index(tile1)  # 哪张牌是别人的
                base_and_called = base*3 + called
                m = (base_and_called << 10) + (t3 << 7) + \
                    (t2 << 5) + (t1 << 3) + (1 << 2) + from_whom
            elif type_ == 1:
                # 碰
                assert(tiles[0] == tiles[1] == tiles[2] or all(
                    i[0] in ('0', '5') for i in tiles))
                base = tile136s[0]//4  # 最小牌tile34
                called = tile136s.index(tile1)  # 哪张牌是别人的
                base_and_called = base*3 + called
                t4 = ((1, 2, 3), (0, 2, 3), (0, 1, 3),
                      (0, 1, 2)).index((t1, t2, t3))
                m = (base_and_called << 9) + (t4 << 5) + (1 << 3) + from_whom
                self.pengInfo[base] = m
        elif type_ == 2:
            # 明杠
            assert(len(tiles) == 4)
            assert(tiles[0] == tiles[1] == tiles[2] == tiles[2] or all(
                i[0] in ('0', '5') for i in tiles))
            tile1 = self.lastDiscard
            if seat == self.mySeat:
                tile2 = popHai(tiles[2])
                tile3 = popHai(tiles[1])
                tile4 = popHai(tiles[0])
            else:
                tile2 = self.cardRecorder.majsoul2tenhou(tiles[2])[0]
                tile3 = self.cardRecorder.majsoul2tenhou(tiles[1])[0]
                tile4 = self.cardRecorder.majsoul2tenhou(tiles[0])[0]
            tile136s = sorted([tile1, tile2, tile3, tile4])
            base = tile136s[0]//4  # 最小牌tile34
            called = tile136s.index(tile1)  # 哪张牌是别人的
            base_and_called = base*4 + called
            m = (base_and_called << 8) + (1 << 6) + from_whom
        else:
            raise NotImplementedError
        msg_dict = {'opcode': 'N', 'who': tenhou_seat, 'm': m}
        self.send(self.tenhouEncode(msg_dict))
        if seat == self.mySeat and type_ in (0, 1):
            # 吃碰之后打牌
            self.actionHandler()
        else:
            self.actionPurge()

    @dump_args
    def anGangAddGang(self, type_: int, seat: int, tiles: str):
        """
        type_:操作类型
        seat:杠的玩家
        tiles:杠的牌
        """
        tenhou_seat = (seat-self.mySeat) % 4

        def popHai(tile):
            #从self.hai中找到tile并pop
            for tile136 in self.hai:
                if self.cardRecorder.tenhou2majsoul(tile136=tile136) == tile:
                    self.hai.remove(tile136)
                    return tile136
            raise Exception(tile+' not found.')
        if type_ == 2:
            #自己加杠
            assert(tiles in all_tiles)
            if seat == self.mySeat:
                tile = popHai(tiles)
            else:
                tile = self.cardRecorder.majsoul2tenhou(tiles)[0]
            t4 = tile % 4
            base = tile//4  # 最小牌tile34
            assert(base in self.pengInfo)
            base_and_called = self.pengInfo[base] >> 9
            from_whom = self.pengInfo[base] & 3
            m = (base_and_called << 9) + (t4 << 5) + (1 << 4) + from_whom
        elif type_ == 3:
            # 他家暗杠
            # 暗杠Tenhou见replay3/7
            tile4 = [tiles.replace('0', '5') for i in range(4)]
            if tiles[0] in '05' and tiles[1] in 'mps':
                tile4[0] = '0'+tiles[1]
            if seat == self.mySeat:
                for i in range(4):
                    tile = popHai(tile4[i])
            else:
                for i in range(4):
                    tile = self.cardRecorder.majsoul2tenhou(tile4[i])[0]
            m = (tile//4) << 10
        else:
            raise NotImplementedError
        msg_dict = {'opcode': 'N', 'who': tenhou_seat, 'm': m}
        self.send(self.tenhouEncode(msg_dict))
        # TODO 抢杠
        self.actionPurge()

    @dump_args
    def hule(self, hand: List[str], huTile: str, seat: int, zimo: bool, liqi: bool, doras: List[str], liDoras: List[str], fan: int, fu: int, oldScores: List[int], deltaScores: List[int], newScores: List[int]):
        """
        hand:胡牌者手牌
        huTile:点炮牌
        seat:玩家座次
        zimo:是否自摸
        liqi:是否立直
        doras:明宝牌列表
        liDoras:里宝牌列表
        fan:番数
        fu:符数
        oldScores:4人旧分
        deltaScores::新分减旧分
        newScores:4人新分
        """
        assert(all(tile in all_tiles for tile in hand))
        assert(huTile in all_tiles)
        assert(0 <= seat < 4)
        assert(all(tile in all_tiles for tile in doras))
        assert(all(tile in all_tiles for tile in liDoras))
        def L2S(l): return ','.join(str(i) for i in l)
        who = (seat-self.mySeat) % 4
        fromWho = who if zimo else (self.lastDiscardSeat-self.mySeat) % 4
        self.cardRecorder.clear()
        machi, _ = self.cardRecorder.majsoul2tenhou(huTile)
        ten = L2S((fu, deltaScores[seat], 0))
        if seat == self.mySeat:
            hai = L2S(self.hai)
        else:
            hai = L2S(self.cardRecorder.majsoul2tenhou(
                tile)[0] for tile in hand)
        doraHai = L2S(self.cardRecorder.majsoul2tenhou(
            tile)[0] for tile in doras)
        doraHaiUra = L2S(self.cardRecorder.majsoul2tenhou(tile)[
                         0] for tile in liDoras)
        sc = []
        for i in range(4):
            sc.append(oldScores[(self.mySeat+i) % 4]//100)
            sc.append(deltaScores[(self.mySeat+i) % 4]//100)
        sc = L2S(sc)
        msg_dict = {'opcode': 'AGARI', 'who': who, 'fromWho': fromWho,
                    'machi': machi, 'ten': ten, 'hai': hai, 'doraHai': doraHai, 'sc': sc}
        if doraHaiUra:
            msg_dict['doraHaiUra'] = doraHaiUra
        self.send(self.tenhouEncode(msg_dict))
        self.actionPurge()

    @dump_args
    def liuju(self, tingpai: List[bool], hands: List[List[str]], oldScores: List[int], deltaScores: List[int]):
        """
        tingpai:4个玩家是否停牌
        hands:听牌玩家的手牌(没听为[])
        oldScores:4人旧分
        deltaScores::新分减旧分
        """
        assert(all(tile in all_tiles for hand in hands for tile in hand))
        def L2S(l): return ','.join(str(i) for i in l)
        sc = []
        for i in range(4):
            sc.append(oldScores[(self.mySeat+i) % 4]//100)
            sc.append(deltaScores[(self.mySeat+i) % 4]//100)
        msg_dict = {'opcode': 'RYUUKYOKU', 'sc': L2S(sc)}
        self.cardRecorder.clear()
        for i in range(4):
            if tingpai[i]:
                tenhou_seat = (i-self.mySeat) % 4
                if i == self.mySeat:
                    hai = self.hai
                else:
                    hai = [self.cardRecorder.majsoul2tenhou(
                        tile)[0] for tile in hands[i]]
                msg_dict['hai'+str(tenhou_seat)] = L2S(hai)
        self.send(self.tenhouEncode(msg_dict))
        self.actionPurge()

    def specialLiuju(self):
        """
        四风连打、九种九牌、四杠散了引起的流局
        """
        self.send(self.tenhouEncode({'opcode': 'RYUUKYOKU'}))
        self.actionPurge()

    #-------------------------Majsoul动作函数-------------------------

    def wait_for_a_while(self, delay=1.0):
        # 如果读秒不足delay则强行等待一会儿
        dt = time.time()-self.lastSendTime
        if dt < delay:
            time.sleep(delay-dt)

    @dump_args
    def on_DiscardTile(self, tile34):
        if self.wait_a_moment:
            self.wait_a_moment = False
            time.sleep(2)
        self.wait_for_a_while(0.3)
        tile = self.cardRecorder.tenhou2majsoul(tile34=int(tile34))
        self.majsoul_hai = [self.cardRecorder.tenhou2majsoul(tile136=x) for x in self.hai]
        print('hai:', self.majsoul_hai)
        if tile in ['5m', '5p', '5s'] and tile not in self.majsoul_hai:
            tile = '0' + tile[1]
        assert(tile in self.majsoul_hai)
        if not self.isLiqi:
            self.actionDiscardTile(tile)

    @dump_args
    def on_ChiPengGang(self, action_id):
        # <N ...\>
        self.wait_for_a_while(2.0)
        if action_id == 45:
            #无操作
            self.actionChiPengGang(sdk.Operation.NoEffect, [])
            return
        if action_id == 44:
            # TODO 九种九牌流局
            self.actionChiPengGang(sdk.Operation.NoEffect, [])
            return 
        if action_id == 37:
            #碰
            self.actionChiPengGang(sdk.Operation.Peng, [])
            if self.lastOperation != None:
                opList = self.lastOperation.get('operationList', [])
                opList = [op for op in opList if op['type']
                          == Operation.Peng.value]
                assert(len(opList) == 1)
                op = opList[0]
                combination = op['combination']
                if len(combination) > 1:
                    combination = [c for c in combination if '0' in c]
                    assert(len(combination) == 1)
                    combination = combination[0]
                    combination = tuple(sorted(combination.split('|')))
                    print('clickCandidateMeld Peng aka', combination)
                    time.sleep(1)
                    self.clickCandidateMeld(combination)
        elif action_id == 39:
            #明杠
            self.actionChiPengGang(sdk.Operation.MingGang, [])
        elif action_id in [34, 35, 36]:
            #吃
            self.actionChiPengGang(sdk.Operation.Chi, [])
            #判断是否有多个候选方案需二次选择
            if self.lastOperation != None:
                opList = self.lastOperation.get('operationList', [])
                opList = [op for op in opList if op['type']
                          == Operation.Chi.value]
                assert(len(opList) == 1)
                op = opList[0]
                combination = op['combination']
                # e.g. combination = ['4s|0s', '4s|5s']
                if len(combination) > 1:
                    # 需要二次选择
                    # picked up tile
                    chiTile = self.cardRecorder.tenhou2majsoul(tile136=self.lastDiscard)
                    # change aka to normal order
                    chiOrder = int(chiTile[0])
                    chiType = chiTile[1]
                    if chiOrder == 0:
                        chiOrder = 5
                    if action_id == 34:
                        tile1 = str(chiOrder + 1) + chiType
                        tile2 = str(chiOrder + 2) + chiType
                    elif action_id == 35:
                        tile1 = str(chiOrder - 1) + chiType
                        tile2 = str(chiOrder + 1) + chiType
                    else:
                        tile1 = str(chiOrder - 2) + chiType
                        tile2 = str(chiOrder - 1) + chiType
                    combination = [tuple(sorted(c.split('|')))
                                   for c in combination]
                    AI_combination = tuple(sorted([tile1, tile2]))
                    # 如果有包含红宝牌的同构吃，优先用红宝牌
                    oc = tuple(sorted([i.replace('5', '0')
                                       for i in AI_combination]))
                    if oc in combination:
                        AI_combination = oc
                    assert(AI_combination in combination)
                    print('clickCandidateMeld AI_combination', AI_combination)
                    time.sleep(1)
                    self.clickCandidateMeld(AI_combination)
        elif action_id == 38:
            #暗杠
            self.actionChiPengGang(sdk.Operation.MingGang, [])
        elif action_id == 40:
            #加杠
            self.actionChiPengGang(sdk.Operation.JiaGang, [])
        elif action_id == 42:
            #点炮胡
            self.actionHu()
        elif action_id == 43:
            #自摸胡
            self.actionZimo()
        else:
            raise NotImplementedError

    @dump_args
    def on_Liqi(self, tile34):
        self.wait_for_a_while(2.0)
        tile = self.cardRecorder.tenhou2majsoul(tile34=int(tile34))
        self.majsoul_hai = [self.cardRecorder.tenhou2majsoul(tile136=x) for x in self.hai]
        if tile in ['5m', '5p', '5s'] and tile not in self.majsoul_hai:
            tile = '0' + tile[1]
        assert(tile in self.majsoul_hai)
        self.actionLiqi(tile)


def MainLoop(isRemoteMode=False, remoteIP: str = None, level=None, length=0, webdriver_args=[], 
    dump_file=None, agent_save_path=None, model_path=None, force_riichi=False):
    # 循环进行段位场对局，level=0~4表示铜/银/金/玉/王之间，None需手动开始游戏
    # calibrate browser position
    aiWrapper = AIWrapper(webdriver_args=webdriver_args, force_riichi=force_riichi)

    # create AI
    now = int(datetime.timestamp(datetime.now()))
    AI = MajsoulVLOG(model_path)
    while True:
        if dump_file:
            dump_file_handler = open(dump_file, 'a')
        else:
            dump_file_handler = None

        print('waiting to calibrate the browser location')
        while not aiWrapper.calibrateMenu():
            print('  majsoul menu not found, calibrate again')
            time.sleep(3)

        aiWrapper.init(AI, dump_file=dump_file_handler)

        if level != None:
            aiWrapper.actionBeginGame(level, length=length)

        print('waiting for the game to start')
        while not aiWrapper.isPlaying():
            time.sleep(3)

        aiWrapper.actionPurge()
        print('loading the game')
        while aiWrapper.recvFromMajsoul() != State.Enter:
            time.sleep(3)
        
        print('enter game')
        while True:
            aiWrapper.recvFromMajsoul()
            if aiWrapper.need_action:
                action_id, if_riichi = aiWrapper.actionGet()
                aiWrapper.actionDo(action_id, if_riichi)
                aiWrapper.actionPurge()
            if aiWrapper.isEnd:
                results = [rv for r in zip(aiWrapper.finalScore, [-1]*4) for rv in r]
                aiWrapper.send('owari="{},{},{},{},{},{},{},{}"\x00<PROF\x00'.format(*results))
                aiWrapper.isEnd = False
                if dump_file_handler:
                    dump_file_handler.close()
                aiWrapper.actionReturnToMenu()
                break
            time.sleep(0.25)
        if agent_save_path:
            AI.save_data(agent_save_path)
        else:
            AI.save_data('agent{}.pth'.format(str(now)))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="MajsoulVLOG")
    parser.add_argument('-l', '--level', default=None)
    parser.add_argument('-p', '--profile-directory', default=None)
    parser.add_argument('-u', '--user-data-dir', default=None)
    parser.add_argument('-d', '--dump-file', default=None)
    parser.add_argument('-a', '--agent-save-path', default=None)
    parser.add_argument('-m', '--model', default=None)
    parser.add_argument('-L', '--length', default=None)
    parser.add_argument('-f', '--force-riichi', action='store_true')
    parser.set_defaults(force_riichi=False)
    args = parser.parse_args()
    level = None if args.level == None else int(args.level)
    length = 0 if args.length == None else int(args.length)
    webdriver_args = []
    if args.profile_directory is not None:
        webdriver_args.append('--profile-directory='+args.profile_directory)
    if args.user_data_dir is not None:
        webdriver_args.append('--user-data-dir='+args.user_data_dir)

    MainLoop(level=level, length=length, webdriver_args=webdriver_args, dump_file=args.dump_file, agent_save_path=args.agent_save_path, model_path=args.model, force_riichi=args.force_riichi)
