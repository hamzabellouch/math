import Mathlib
import OAI.Combinatorics.UniformKServer.StackRun

namespace OAI

noncomputable section

namespace UniformKServer.TypedStack
open StackCompiler
open scoped Classical

structure Action (Q K : Type*) (g : ℕ) where
  control : Q
  inputMove : HeadMove := .stay
  stackOp : K→Op g := fun _=>.keep
  emit : Option Bool := none
  yield : Bool := false
structure Processor (Q K : Type*) (g : ℕ) where
  start : Q
  transition : Q→Option Bool→(K→Option (Fin g))→Bool→Action Q K g
structure State (Q K : Type*) (g : ℕ) where
  control : Q
  input : BitTape
  store : K→List (Fin g)
  outputRev : List Bool
  yielded : Bool

variable {Q K : Type*} {g : ℕ}

def step (P : Processor Q K g) (s : State Q K g) (coin : Bool) : State Q K g :=
  if s.yielded then s else
  let a:=P.transition s.control s.input.head (fun i=>(s.store i).head?) coin
  ⟨a.control,s.input.shift a.inputMove,fun i=>applyOp (a.stackOp i) (s.store i),
    match a.emit with | none=>s.outputRev | some b=>b::s.outputRev,a.yield⟩
def initial (P : Processor Q K g) (input : List Bool) : State Q K g :=
  ⟨P.start,BitTape.ofWord input,fun _=>[],[],false⟩
def install (s : State Q K g) (input : List Bool) : State Q K g :=
  {s with input:=BitTape.ofWord input,outputRev:=[],yielded:=false}
def run (P : Processor Q K g) (s : State Q K g) (coins : List Bool) : State Q K g :=
  coins.foldl (step P) s

def eqv (A : Type*) [Fintype A] : A≃Fin (Fintype.card A) := Fintype.equivFin A

def compile [Fintype Q] [Fintype K] (P : Processor Q K g) :
    StackCompiler.Processor (Fintype.card Q) (Fintype.card K) g where
  start:=eqv Q P.start
  transition:=fun q inp h b=>
    let a:=P.transition ((eqv Q).symm q) inp (fun k=>h (eqv K k)) b
    ⟨eqv Q a.control,a.inputMove,fun i=>a.stackOp ((eqv K).symm i),a.emit,a.yield⟩
def encode [Fintype Q] [Fintype K] (s : State Q K g) :
    StackCompiler.State (Fintype.card Q) (Fintype.card K) g :=
  ⟨eqv Q s.control,s.input,fun i=>s.store ((eqv K).symm i),s.outputRev,s.yielded⟩

theorem encode_step [Fintype Q] [Fintype K] (P : Processor Q K g) (s : State Q K g) (b : Bool) :
    encode (step P s b)=StackCompiler.step (compile P) (encode s) b := by
  cases hy:s.yielded <;> simp only [step,StackCompiler.step,encode,compile,hy,
    Bool.false_eq_true,↓reduceIte,Equiv.symm_apply_apply]
  rfl

theorem encode_run [Fintype Q] [Fintype K] (P : Processor Q K g) (s : State Q K g) (bs : List Bool) :
    encode (run P s bs)=StackCompiler.run (compile P) (encode s) bs := by
  induction bs generalizing s with
  | nil=>rfl
  | cons b bs ih=>
    change encode (run P (step P s b) bs)=StackCompiler.run (compile P) (StackCompiler.step (compile P) (encode s) b) bs
    rw [ih,encode_step]

theorem encode_initial [Fintype Q] [Fintype K] (P : Processor Q K g) (w : List Bool) :
    encode (initial P w)=StackCompiler.initial (compile P) w := rfl

theorem encode_install [Fintype Q] [Fintype K] (s : State Q K g) (w : List Bool) :
    encode (install s w)=StackCompiler.install (encode s) w := rfl

theorem run_cons (P : Processor Q K g) (s : State Q K g) (b : Bool) (bs : List Bool) :
    run P s (b::bs)=run P (step P s b) bs := rfl

theorem run_append (P : Processor Q K g) (s : State Q K g) (as bs : List Bool) :
    run P s (as++bs)=run P (run P s as) bs := List.foldl_append

theorem run_yielded (P : Processor Q K g) (s : State Q K g) (h : s.yielded=true) (bs : List Bool) :
    run P s bs=s := by
  induction bs with
  | nil=>rfl
  | cons b bs ih=>simpa only [run_cons,step,h,Bool.true_eq,↓reduceIte] using ih

end UniformKServer.TypedStack

end

end OAI
