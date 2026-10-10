import Mathlib
import OAI.Combinatorics.UniformKServer.Epochs
import OAI.Combinatorics.UniformKServer.StackTape

namespace OAI

noncomputable section

/-! Finite-control, finite-alphabet stack processors, compiled to the exact
binary multitape model. There is no unit-cost arithmetic oracle. -/
namespace UniformKServer.StackCompiler
open scoped Classical

instance : Fintype HeadMove := ⟨{.left,.stay,.right},by intro x;cases x <;> simp⟩

inductive Op (g : ℕ) where
  | keep | push (a : Fin g) | pop
  deriving DecidableEq,Fintype

structure Action (q m g : ℕ) where
  control : Fin q
  inputMove : HeadMove
  stackOp : Fin m → Op g
  emit : Option Bool
  yield : Bool
  deriving Fintype

structure Processor (q m g : ℕ) where
  start : Fin q
  transition : Fin q → Option Bool → (Fin m → Option (Fin g)) → Bool → Action q m g

structure State (q m g : ℕ) where
  control : Fin q
  input : BitTape
  store : Fin m → List (Fin g)
  outputRev : List Bool
  yielded : Bool

def applyOp {g : ℕ} (o : Op g) (s : List (Fin g)) : List (Fin g) :=
  match o with
  | .keep => s
  | .push a => a::s
  | .pop => s.tail

def step {q m g : ℕ} (P : Processor q m g) (s : State q m g) (coin : Bool) : State q m g :=
  if s.yielded then s else
  let a:=P.transition s.control s.input.head (fun i=>(s.store i).head?) coin
  ⟨a.control,s.input.shift a.inputMove,fun i=>applyOp (a.stackOp i) (s.store i),
    match a.emit with | none=>s.outputRev | some b=>b::s.outputRev,a.yield⟩

def initial {q m g : ℕ} (P : Processor q m g) (input : List Bool) : State q m g :=
  ⟨P.start,BitTape.ofWord input,fun _=>[],[],false⟩

def install {q m g : ℕ} (s : State q m g) (input : List Bool) : State q m g :=
  {s with input:=BitTape.ofWord input,outputRev:=[],yielded:=false}

def code {g : ℕ} (a j : Fin g) : Bool := decide (a=j)

def decode {g : ℕ} (v : Fin g → Option Bool) : Option (Fin g) :=
  if h : ∃ a,∀j,v j=some (code a j) then some (Classical.choose h) else none

theorem decode_none (g : ℕ) : decode (fun _ : Fin g=>none)=none := by
  have hn : ¬∃ a : Fin g,∀j,(none : Option Bool)=some (code a j) := by
    rintro ⟨a,h⟩
    cases (h a)
  exact dite_eq_right hn

theorem decode_code {g : ℕ} (a : Fin g) : decode (fun j=>some (code a j))=some a := by
  unfold decode
  split_ifs with h
  · congr 1
    have he: code a a=code (Classical.choose h) a := Option.some.inj (Classical.choose_spec h a)
    exact of_decide_eq_true (he.symm.trans (by simp [code]))
  · exact False.elim (h ⟨a,fun _=>rfl⟩)

abbrev controls (q m g : ℕ) := Sum (Fin q) (Action q m g)
def ctl (q m g : ℕ) : controls q m g ≃ Fin (Fintype.card (controls q m g)) := Fintype.equivFin _
def wire (m g : ℕ) : (Fin m × Fin g) ≃ Fin (Fintype.card (Fin m × Fin g)) := Fintype.equivFin _

def machine {q m g : ℕ} (P : Processor q m g) : BitMachine where
  controls := Fintype.card (controls q m g)
  tapes := Fintype.card (Fin m × Fin g)
  start := ctl q m g (.inl P.start)
  transition := fun c input work coin=>
    match (ctl q m g).symm c with
    | .inl c =>
      let a:=P.transition c input (fun i=>decode (fun j=>work (wire m g (i,j)))) coin
      {control:=ctl q m g (.inr a),inputMove:=a.inputMove,
        write:=fun v=> let i:=((wire m g).symm v).1
          match a.stackOp i with
          | .pop=>none
          | _=>work v,
        workMove:=fun v=>let i:=((wire m g).symm v).1
          match a.stackOp i with
          | .push _ => .left
          | .keep=>.stay
          | .pop=>if work v=none then .stay else .right,
        emit:=none,yield:=false}
    | .inr a =>
      {control:=ctl q m g (.inl a.control),inputMove:=.stay,
        write:=fun v=>let ij:=(wire m g).symm v
          match a.stackOp ij.1 with
          | .push a=>some (code a ij.2)
          | _=>work v,
        workMove:=fun _=>.stay,emit:=a.emit,yield:=a.yield}

structure Matches {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (z : MachineState (machine P)) : Prop where
  control : z.control=ctl q m g (.inl s.control)
  input : z.input=s.input
  output : z.outputRev=s.outputRev
  yielded : z.yielded=s.yielded
  work : ∀i j,StackTape.Rep ((s.store i).map (fun a=>code a j)) (z.work (wire m g (i,j)))

theorem matches_initial {q m g : ℕ} (P : Processor q m g) (input : List Bool) :
    Matches P (initial P input) ((machine P).initial input) :=
  ⟨rfl,rfl,rfl,rfl,fun _ _=>StackTape.blank⟩

theorem matches_install {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (z : MachineState (machine P)) (h : Matches P s z) (input : List Bool) :
    Matches P (install s input) ((machine P).install z input) :=
  ⟨h.control,rfl,rfl,rfl,h.work⟩

theorem matches_heads {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (z : MachineState (machine P)) (h : Matches P s z) (i : Fin m) :
    decode (fun j=>(z.work (wire m g (i,j))).head)=(s.store i).head? := by
  have he : (fun j=>(z.work (wire m g (i,j))).head)=
      fun j=> ((s.store i).map (fun a=>code a j)).head? := funext (fun j=>StackTape.head (h.work i j))
  rw [he]
  cases hs:s.store i with
  | nil => exact decode_none _
  | cons a as => exact decode_code a

end UniformKServer.StackCompiler

end

end OAI
