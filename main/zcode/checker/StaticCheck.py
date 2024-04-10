from AST import *
from Visitor import *
from Utils import Utils
from StaticError import *
from functools import reduce

from main.zcode.utils.Visitor import BaseVisitor


class VarClass():    
    def __init__(self, name, typ, init):
        self.name = name
        self.typ = typ
        
    
class FuncClass():
    def __init__(self, name, params, retType, body) -> None:
        self.name = name
        self.params = params
        self.retType = retType
        self.body = body

class GetEnv(BaseVisitor, Utils):
    def visitProgram(self, ctx: Program, o: object):
        o = {
            'gloEnv' : [],
            'no_body' : []
        }
        for decl in ctx.decl:
            o += [self.visit(decl, o)]
        return o
    def visitVarDecl(self, ctx: VarDecl, o: object):
        term = self.lookup(ctx.name, o['gloEnv'], lambda x: x.name)
        if term is not None:
            raise Redeclared(Variable(), ctx.name)
        elif term:
            # if ctx.modifier in ['dynamic', 'var']: # The implicit keyword cannot be used for array type
            #         o['gloEnv'] += [VarClass(ctx.name, [NumberType, BoolType, StringType])]
            # else:
            o['gloEnv'] += [VarClass(ctx.name, ctx.varType)]
                
                    
    def visitFuncDecl(self, ctx: FuncDecl, o: object):
        term = self.lookup(ctx.name.name, o['gloEnv'], lambda x: x.name)
        if term is not None:
            raise Redeclared(Function(), ctx.name.name)
            
        else:
            if ctx.body is None:
                for f in o['no_body']:
                    if f.name == ctx.name.name:
                        raise Redeclared(Function(), ctx.name.name)                
                o['no_body'] += [FuncClass(ctx.name.name, ctx.param, None, False)]
            else:                
                for f in o['no_body']:
                    if f.name == ctx.name.name:
                        funcCheck(f, ctx)                        
                        o['no_body'].remove(f)
                        break  
                o['gloEnv'] += [FuncClass(ctx.name.name, ctx.param, None, True)]
            
def funcCheck(func_cls, func_decl): # name is the same    
    if len(func_cls.params) != len(func_decl):
        raise Redeclared(Function(), func_decl.name.name)
    else:
        for i in range(len(func_cls.params)):
            if type(func_cls.params[i]) is not type(func_decl.param[i]):
                raise Redeclared(Function(), func_decl.name.name)
    
class SymbolTable():
    def __init__(self, ctx):        
        self.env = [GetEnv.visit(ctx, None)]
        self.table = self.env['gloEnv']
        self.no_body = self.env['no_body']
        self.arr = []

class StaticChecker(BaseVisitor, Utils):
    def __init__(self, ctx):
        self.env = SymbolTable()
        self.scope = 0
        self.arr_none = False
        
    def check(self, ctx):
        return self.visit(ctx, self.env)
    
    def typeInfer(self, expr, typ, env):
        if type(expr) is Id:
            for i in range(len(env)):
                for j in range(len(env[i])):
                    if env[i][j].name == expr.name:
                        if env[i][j].typ is None: # 
                            env[i][j].typ = typ
                        else:
                            if type(env[i][j].typ) is list and typ in env[i][j].typ:
                                env[i][j].typ = typ                           
                                return  
        elif type(expr) in [CallExpr, CallStmt]:
            for i in range(env[-1]):
                if env[-1][i].name == expr.name:
                    env[-1][i].retType = typ 
                    return
          
    def arrayInfer(self, arr, eleType, env):
        if type(arr) in [Id, CallExpr, CallStmt]:            
            self.typeInfer(ele, eleType, env)
        elif type(arr) is ArrayLiteral:
            for ele in arr.value:
                self.arrayInfer(arr, eleType, env)
                    
            
    def compareArray(self, explicit, implicit, env):
        if len(explicit.size) == len(implicit.size) and explicit.size == implicit.size: 
            if implicit.eleType is None:
                self.arr_none = True                  
                return False       
            elif type(explicit.eleType) is type(implicit.eleType):                
                return True             
        
        return False
    
    def visitProgram(self, ctx, env):
        for decl in ctx.decl:
            self.visit(decl, env)
            
        
    def visitVarDecl(self, ctx: VarDecl, env):
        term = self.lookup(ctx.name, env[0], lambda x: x.name)
        if self.scope and term is not None:
            raise Redeclared(Variable(), ctx.name)
        elif self.scope:            
            if ctx.varType is not None and ctx.varInit is not None:
                typ = self.visit(ctx.varType, env)
                init = self.visit(ctx.varInit, env)
                if init is None:  # id, callExpr
                    self.typeInfer(ctx.varInit, typ, env)
                    env[0] += [VarClass(ctx.name, typ)]
                else:
                    if typ is not init:
                        raise TypeMismatchInExpression(ctx)
                    else:
                        if typ is ArrayType:
                            if self.compareArray(typ, init):
                                env[0] += [VarClass(ctx.name, typ)]
                            elif self.arr_none:
                                self.arrayInfer(ctx.varInit, typ.eleType, env)
                                self.arr_none = False
                            else:
                                raise TypeMismatchInExpression(ctx)
                        else:
                            env[0] += [VarClass(ctx.name, init)]
                            
            elif ctx.varType:
                typ = self.visit(ctx.varType, env)
                env[0] += [VarClass(ctx.name, typ)]
            elif ctx.varInit: # var, dynamic
                init = self.visit(ctx.varInit, env)
                if init is None: # id, callExpr
                    raise TypeCannotBeInferred(ctx)
                    # env[0] += [VarClass(ctx.name, [NumberType, BoolType, StringType])]
                elif init in [NumberType, BoolType, StringType]:                    
                    env[0] += [VarClass(ctx.name, init)]
                else:
                    raise TypeMismatchInExpression(ctx)
            else:
                if ctx.modifier == 'dynamic':
                    env[0] += [VarClass(ctx.name, [NumberType, BoolType, StringType])]
                else:                    
                    raise TypeCannotBeInferred(ctx)   
        elif term:
            for i in range(len(env[0])):
                if env[0][i].name == ctx.name:
                    if ctx.varType is not None and ctx.varInit is not None:
                        typ = self.visit(ctx.varType, env)
                        init = self.visit(ctx.varInit, env)                                                 
                        if init is None:
                            self.typeInfer(ctx.varInit, typ, env)
                            env[0][i].typ = typ
                        else:
                            if typ is not init:
                                raise TypeMismatchInExpression(ctx)
                            else:
                                if typ is ArrayType:
                                    if self.compareArray(typ, init):
                                        env[0] += [VarClass(ctx.name, typ)]
                                    elif self.arr_none:
                                        self.arrayInfer(ctx.varInit, typ.eleType, env)
                                        self.arr_none = False
                                else:
                                    env[0][i].typ = typ
                            
                    elif ctx.varType:
                        typ = self.visit(ctx.varType, env)
                        env[0][i].typ = typ
                    elif ctx.varInit: #dynamic, var
                        init = self.visit(ctx.varInit, env)
                        if init is None: 
                            raise TypeCannotBeInferred(ctx)
                            # env[0][i].typ = [NumberType, BoolType, StringType]
                        elif init in [NumberType, BoolType, StringType]:
                            env[0][i].typ = init
                        else:
                            raise TypeMismatchInExpression(ctx)
                    else: # var, dynamic
                        if ctx.modifier == 'dynamic':
                            env[0][i].typ = [NumberType, BoolType, StringType]
                        else:                            
                            raise TypeCannotBeInferred(ctx)
                        
                    break  
    def visitFuncDecl(self, ctx: FuncDecl, env):
        term = self.lookup(ctx.name.name, env[0], lambda x: x.name)
        if not self.scope:
            if term is not None:
                funcCheck(term, ctx)
                if ctx.body is None:
                    return
                else:                                   
                    paramLst = []
                    for param in ctx.param:
                        self.visit(param, paramLst)
                    env = [paramLst] + env
                    self.scope += 1
                    retType = self.visit(ctx.body, env)
                    for i in range(len(env[-1])):
                        if env[-1][i].name == ctx.name.name:                            
                            env[-1][i] = FuncClass(ctx.name, paramLst, retType, True)
                            break
                                                    
                        
    def visitArrayLiteral(self, ctx: ArrayLiteral, env):
        self.arr += [ctx]
        eleType = None
        for ele in ctx.value:
            typ = self.visit(ele, env)
            if type(typ) is ArrayType and typ.eleType is not None:
                eleType =  typ 
                break            
            if typ is not None and eleType is None:
                eleType = typ
                continue
            
        
        if eleType is not None:
            for ele in ctx.value:
                typ = self.visit(ele, env)
                if typ is None:  # Id, callExpr
                    self.typeInfer(ele, eleType, env)
                elif type(typ) is not type(eleType):
                    raise TypeMismatchInExpression(self.arr[0])
                else:
                    if eleType is ArrayType:
                        if eleType.eleType is None:
                            if len(eleType.size) == len(typ.size) and eleType.size == typ.size:
                                continue
                            else:
                                raise TypeMismatchInExpression(self.arr[0])
                        else:
                            if self.compareArray(eleType, typ, env):
                                continue
                            else:
                                if self.arr_none:
                                    self.typeInfer(ele, eleType, env)
                                    self.arr_none = False
                                else:
                                    raise TypeMismatchInExpression(self.arr[0])
                    else: # number, bool, string                       
                        continue
            self.arr = self.arr[:-1]
            if type(eleType) is ArrayType:                
                return ArrayType([len(ctx.value)] + eleType.size , eleType) 
                
            else: 
                return ArrayType([len(ctx.value)], eleType)
                                    
        else:
            self.arr = self.arr[:-1]
            return ArrayType([len(ctx.value)], None)
                    
            
                    
            
                
            
    
    def visitAssign(self, ctx: Assign, env):
        rhsType, lhsType = self.visit(ctx.exp, env), self.visit(ctx.lhs, env)
        
        if rhsType is not None and lhsType is not None:
            if lhsType is not rhsType:
                raise TypeMismatchInStatement(ctx)
            else:
                if lhsType is ArrayType:
                    if lhsType.eleType is not None:
                        if self.compareArray(lhsType, rhsType, env):
                            return
                        elif self.arr_none:
                            self.arrayInfer(rhsType, lhsType.eleType, env)
                            return
                        else:
                            raise TypeMismatchInStatement(ctx)
                    elif rhsType.eleType is not None:
                        if self.compareArray(rhsType, lhsType, env):
                            return
                        elif self.arr_none:
                            self.arrayInfer(lhsType, rhsType.eleType, env)
                            return
                        else:
                            raise TypeMismatchInStatement(ctx)
                    else:
                        raise TypeCannotBeInferred(ctx)
                                            
        elif lhsType:
            self.typeInfer(ctx.exp, lhsType, env)
        elif rhsType:
            self.typeInfer(ctx.lhs, rhsType, env)
        else:
            raise TypeCannotBeInferred(ctx)

    
    def visitId(self, ctx: Id, env):
        for scope in env:
            term = self.lookup(ctx.name, scope, lambda x: x.name)
            if term.typ is None:
                return None 
            elif term.typ is list:
                return None
            else:
                return term.typ 
        
        raise Undeclared(Variable(), ctx.name)
            
    
    
                
               
            
            
        
                         
                        
