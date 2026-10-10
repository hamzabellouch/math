import Mathlib
import OAI.Combinatorics.UniformKServer.ConstructorProgram
import OAI.Combinatorics.UniformKServer.TypedStack

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2
open TypedStack
open scoped Classical

inductive Key where
  | base (k : K') | pay | buf
  deriving DecidableEq,Fintype
inductive Control (qc qa : ℕ) where
  | bootCons | bootOne | bootRead | bootDrain
  | construct (c : Fin qc)
  | pad | sample | sampleSep | savePayload
  | randomCons | randomOne | randomDrain
  | requestCons | requestRead | requestOne | requestDrain
  | payloadCons | payloadDrain
  | active (c : Fin qa) | emit
  deriving DecidableEq,Fintype

abbrev g := Fintype.card Γ'
abbrev main : Key := .base .main
abbrev digit (b : Bool) : Fin g := FlatTM2.letters (RawBits.letter b)
abbrev sep : Fin g := FlatTM2.letters Γ'.cons
abbrev Action (qc qa : ℕ) := TypedStack.Action (Control qc qa) Key g
abbrev State (qc qa : ℕ) := TypedStack.State (Control qc qa) Key g

variable {qc qa : ℕ}
def pass (q : Control qc qa) (y : Bool:=false) : Action qc qa :=
  {control:=q,yield:=y}
def write (q : Control qc qa) (k : Key) (a : Fin g) : Action qc qa :=
  {control:=q,stackOp:=fun j=>if j=k then .push a else .keep}
def pop (q : Control qc qa) (k : Key) (y : Bool:=false) : Action qc qa :=
  {control:=q,stackOp:=fun j=>if j=k then .pop else .keep,yield:=y}
def move (q : Control qc qa) (src dst : Key) (a : Fin g) : Action qc qa :=
  {control:=q,stackOp:=fun j=>if j=src then .pop else if j=dst then .push a else .keep}
def read (q exit : Control qc qa) (i : Option Bool) : Action qc qa :=
  match i with
  | none=>pass exit
  | some b=>{write q .buf (digit b) with inputMove:=.right}
def drain (q exit : Control qc qa) (src : Key) (h : Key→Option (Fin g)) : Action qc qa :=
  match h src with
  | none=>pass exit
  | some a=>move q src main a

def lift {q' : ℕ} (q : Control qc qa) (a : StackCompiler.Action q' (Fintype.card K') g) (y : Bool) : Action qc qa :=
  {control:=q,stackOp:=fun j=>match j with
    | .base k=>a.stackOp (FlatTM2.keys k)
    | _=>.keep,yield:=y}

def processor (C : StackCompiler.Processor qc (Fintype.card K') g)
    (A : StackCompiler.Processor qa (Fintype.card K') g) : TypedStack.Processor (Control qc qa) Key g where
  start:=.bootCons
  transition:=fun q inp h coin=>match q with
  | .bootCons=>write .bootOne main sep
  | .bootOne=>write .bootRead main (digit true)
  | .bootRead=>read .bootRead .bootDrain inp
  | .bootDrain=>match h .buf with
    | none=>pass (.construct C.start) true
    | some a=>move .bootDrain .buf main a
  | .construct c=>
    let a:=C.transition c none (fun i=>h (.base (FlatTM2.keys.symm i))) false
    lift (bif a.yield then .pad else .construct a.control) a true
  | .pad=>if h main=some sep then pop .sample main true else pop .pad main true
  | .sample=>if h main=some (digit false) then move .sample main .buf (digit coin)
    else pop .sampleSep main
  | .sampleSep=>pop .savePayload main
  | .savePayload=>if h main=some sep then pop .randomCons main
    else match h main with
    | none=>pass .randomCons
    | some a=>move .savePayload main .pay a
  | .randomCons=>write .randomOne main sep
  | .randomOne=>write .randomDrain main (digit true)
  | .randomDrain=>drain .randomDrain .requestCons .buf h
  | .requestCons=>write .requestRead main sep
  | .requestRead=>read .requestRead .requestOne inp
  | .requestOne=>write .requestDrain main (digit true)
  | .requestDrain=>drain .requestDrain .payloadCons .buf h
  | .payloadCons=>write .payloadDrain main sep
  | .payloadDrain=>drain .payloadDrain (.active A.start) .pay h
  | .active c=>
    let a:=A.transition c none (fun i=>h (.base (FlatTM2.keys.symm i))) false
    lift (bif a.yield then .emit else .active a.control) a false
  | .emit=>if h main=some sep then pop .sample main true
    else {pop .emit main with emit:=some (decide (h main=some (digit true)))}

def literalC (mult : ℕ) := LiteralPartrec.processor (ConstructorProgram.code mult)
def literalA := LiteralBound.program

def uniform (mult : ℕ) := processor (literalC mult) literalA

def machine (mult : ℕ) : BitMachine := StackCompiler.machine (TypedStack.compile (uniform mult))

end UniformKServer.UniformWrapper

end

end OAI
