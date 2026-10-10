import Mathlib
import OAI.Combinatorics.UniformKServer.StackCompiler

namespace OAI

noncomputable section

namespace UniformKServer.StackCompiler
open scoped Classical

private theorem write_none (t : BitTape) (ht : t.head=none) :
    {t with head:=none}=t := by
  cases t with
  | mk l h r =>
    change h=none at ht
    subst h
    rfl

def beginOp {g : ℕ} (o : Op g) (t : BitTape) : BitTape :=
  match o with
  | .keep=>t
  | .push _=>t.shift .left
  | .pop=>StackTape.pop t

def finishOp {g : ℕ} (o : Op g) (j : Fin g) (t : BitTape) : BitTape :=
  match o with
  | .push a=>{t with head:=some (code a j)}
  | _=>t

def middle {q m g : ℕ} (P : Processor q m g) (a : Action q m g)
    (z : MachineState (machine P)) : MachineState (machine P) where
  control:=ctl q m g (.inr a)
  input:=z.input.shift a.inputMove
  work:=fun v=>beginOp (a.stackOp (((wire m g).symm v).1)) (z.work v)
  outputRev:=z.outputRev
  yielded:=false

def last {q m g : ℕ} (P : Processor q m g) (a : Action q m g)
    (z : MachineState (machine P)) : MachineState (machine P) where
  control:=ctl q m g (.inl a.control)
  input:=z.input
  work:=fun v=>finishOp (a.stackOp (((wire m g).symm v).1)) (((wire m g).symm v).2) (z.work v)
  outputRev:=match a.emit with | none=>z.outputRev | some b=>b::z.outputRev
  yielded:=a.yield

theorem first_step {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (z : MachineState (machine P)) (h : Matches P s z) (hs : s.yielded=false) (coin : Bool) :
    (machine P).step z coin = middle P
      (P.transition s.control s.input.head (fun i=>(s.store i).head?) coin) z := by
  have hh : (fun i=>decode (fun j=>(z.work (wire m g (i,j))).head))=
      fun i=>(s.store i).head? := funext (matches_heads P s z h)
  simp only [BitMachine.step,h.yielded,hs,Bool.false_eq_true,↓reduceIte,
    machine,h.control,Equiv.symm_apply_apply,h.input,hh]
  unfold middle
  congr 1
  · rw [h.input]
  · funext v
    cases hp:(P.transition s.control s.input.head (fun i=>(s.store i).head?) coin).stackOp
        (((wire m g).symm v).1) with
    | keep => rfl
    | push a => rfl
    | pop =>
      simp only [beginOp,StackTape.pop]
      split_ifs with ht
      · simp only [BitTape.shift]
        exact write_none (z.work v) ht
      · rfl

theorem last_step {q m g : ℕ} (P : Processor q m g) (a : Action q m g)
    (z : MachineState (machine P)) (coin : Bool) :
    (machine P).step (middle P a z) coin = last P a (middle P a z) := by
  simp only [BitMachine.step,middle,Bool.false_eq_true,↓reduceIte,machine,
    Equiv.symm_apply_apply,last,BitTape.shift]
  congr 1
  funext v
  cases a.stackOp (((wire m g).symm v).1) <;> rfl

theorem op_rep {g : ℕ} (o : Op g) (j : Fin g) (l : List (Fin g)) (t : BitTape)
    (h : StackTape.Rep (l.map (fun a=>code a j)) t) :
    StackTape.Rep ((applyOp o l).map (fun a=>code a j)) (finishOp o j (beginOp o t)) := by
  cases o with
  | keep=>exact h
  | push a=>exact StackTape.push_rep (code a j) h
  | pop=>simpa only [applyOp,List.map_tail,beginOp,finishOp] using StackTape.pop_rep h

theorem matches_step {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (z : MachineState (machine P)) (h : Matches P s z) (coin unused : Bool) :
    Matches P (step P s coin) ((machine P).step ((machine P).step z coin) unused) := by
  cases hs:s.yielded with
  | true=> simpa [step,hs,BitMachine.step,h.yielded] using h
  | false=>
    rw [first_step P s z h hs,last_step]
    let a:=P.transition s.control s.input.head (fun i=>(s.store i).head?) coin
    change Matches P (step P s coin) (last P a (middle P a z))
    refine ⟨?_,?_,?_,?_,?_⟩
    · simp only [last,step,hs,Bool.false_eq_true,↓reduceIte]
      rfl
    · simp only [last,middle,step,hs,Bool.false_eq_true,↓reduceIte,h.input]
      rfl
    · simp only [last,middle,step,hs,Bool.false_eq_true,↓reduceIte,h.output]
      rfl
    · simp only [last,step,hs,Bool.false_eq_true,↓reduceIte]
      rfl
    · intro i j
      simpa only [last,middle,step,hs,Bool.false_eq_true,↓reduceIte,
        Equiv.symm_apply_apply] using op_rep (a.stackOp i) j (s.store i) _ (h.work i j)
end UniformKServer.StackCompiler

end

end OAI
