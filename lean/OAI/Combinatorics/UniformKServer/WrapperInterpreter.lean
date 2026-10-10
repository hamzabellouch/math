import Mathlib
import OAI.Combinatorics.UniformKServer.WrapperAlgebra

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa q' : ℕ}
variable (C : StackCompiler.Processor qc (Fintype.card K') g)
  (A : StackCompiler.Processor qa (Fintype.card K') g)

def inside (q : Control qc qa) (i : BitTape)
    (s : StackCompiler.State q' (Fintype.card K') g) (y : Bool) : State qc qa :=
  ⟨q,i,fun k=>match k with | .base k=>s.store (FlatTM2.keys k) | _=>[],[],y⟩

def constructState (s : StackCompiler.State qc (Fintype.card K') g) (i : BitTape) : State qc qa :=
  inside (bif s.yielded then .pad else .construct s.control) i s true

def activeState (s : StackCompiler.State qa (Fintype.card K') g) (i : BitTape) : State qc qa :=
  inside (bif s.yielded then .emit else .active s.control) i s false

theorem construct_step (hC : StackPrimitive.Deterministic C)
    (s : StackCompiler.State qc (Fintype.card K') g) (hy : s.yielded=false)
    (i : BitTape) (coin : Bool) :
    TypedStack.step (processor C A) {constructState (qa:=qa) s i with yielded:=false} coin=
      constructState (StackCompiler.step C s false) i := by
  unfold StackPrimitive.Deterministic at hC
  unfold TypedStack.step constructState inside
  simp only [hy,Bool.false_eq_true,↓reduceIte,Bool.cond_false,processor,lift,
    Equiv.apply_symm_apply,BitTape.shift,StackCompiler.step,hC]
  apply wordState_ext <;> try rfl
  intro k;cases k <;> rfl

theorem active_step (hA : StackPrimitive.Deterministic A)
    (s : StackCompiler.State qa (Fintype.card K') g) (hy : s.yielded=false)
    (i : BitTape) (coin : Bool) :
    TypedStack.step (processor C A) (activeState (qc:=qc) s i) coin=
      activeState (StackCompiler.step A s false) i := by
  unfold StackPrimitive.Deterministic at hA
  unfold TypedStack.step activeState inside
  simp only [hy,Bool.false_eq_true,↓reduceIte,Bool.cond_false,processor,lift,
    Equiv.apply_symm_apply,BitTape.shift,StackCompiler.step,hA]
  apply wordState_ext <;> try rfl
  intro k;cases k <;> rfl

theorem cap_succ (P : StackCompiler.Processor q' (Fintype.card K') g)
    (s : StackCompiler.State q' (Fintype.card K') g) (t : ℕ) :
    StackCompiler.run P s (List.replicate (t+1) false)=
      StackCompiler.step P (StackCompiler.run P s (List.replicate t false)) false := by
  rw [show t+1=t+1 from rfl,List.replicate_add,StackCompiler.run_append]
  rfl

theorem active_run (hA : StackPrimitive.Deterministic A)
    (s : StackCompiler.State qa (Fintype.card K') g) (t : ℕ)
    (ht : ∀j<t,(StackCompiler.run A s (List.replicate j false)).yielded=false) (i : BitTape) :
    UniformRun (processor C A) (activeState s i) t
      (activeState (StackCompiler.run A s (List.replicate t false)) i) := by
  induction t with
  | zero=>exact uniform_zero _ _
  | succ t ih=>
    have h₁:=ih (fun j hj=>ht j (by omega))
    have h₂:=uniform_step _ _ _ (active_step C A hA _ (ht t (by omega)) i)
    rw [cap_succ]
    exact h₁.trans h₂

theorem literal_input (c : Turing.ToPartrec.Code) (v : List ℕ) (i : BitTape) :
    activeState (qc:=qc) (LiteralPartrec.input c v) i=
      wordState (.active (LiteralPartrec.processor c).start) i ((trList v).map FlatTM2.letters) [] [] := by
  have h:=LiteralInput.input_config c v
  have hc:=congrArg (fun s=>s.1) h
  have hs:=congrArg (fun s=>s.2.1) h
  have hy:=congrArg (fun s=>s.2.2) h
  change (LiteralPartrec.input c v).control=(LiteralPartrec.processor c).start at hc
  change (LiteralPartrec.input c v).yielded=false at hy
  apply wordState_ext
  · simp only [activeState,inside,hy,Bool.cond_false,hc,wordState]
  · rfl
  · intro k
    cases k with
    | base k=>
      change (LiteralPartrec.input c v).store (FlatTM2.keys k)=_
      have hh:=congrFun hs (FlatTM2.keys k)
      change (LiteralPartrec.input c v).store (FlatTM2.keys k)=
        (if FlatTM2.keys k=FlatTM2.keys K'.main then (trList v).map FlatTM2.letters else []) at hh
      rw [hh]
      cases k <;> simp [wordState]
    | pay=>rfl
    | buf=>rfl
  · rfl
  · rfl

theorem literal_output {c : Turing.ToPartrec.Code} {v w : List ℕ}
    {t : ℕ} (hy : (StackCompiler.run (LiteralPartrec.processor c) (LiteralPartrec.input c v)
      (List.replicate t false)).yielded=true)
    (hs : ∀i,(StackCompiler.run (LiteralPartrec.processor c) (LiteralPartrec.input c v)
      (List.replicate t false)).store i=((halt w).stk (FlatTM2.keys.symm i)).map FlatTM2.letters)
    (i : BitTape) :
    activeState (qc:=qc) (StackCompiler.run (LiteralPartrec.processor c) (LiteralPartrec.input c v)
      (List.replicate t false)) i=wordState .emit i ((trList w).map FlatTM2.letters) [] [] := by
  apply wordState_ext
  · simp only [activeState,inside,hy,Bool.cond_true,wordState]
  · rfl
  · intro k;cases k with
    | base k=>
      simp only [activeState,inside,hs,Equiv.symm_apply_apply,halt,wordState]
      cases k <;> rfl
    | pay=>rfl
    | buf=>rfl
  · rfl
  · rfl

end UniformKServer.UniformWrapper

end

end OAI
