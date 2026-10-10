import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.Program

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

lemma embedStacks_empty {K L : Type} (e : K ↪ L) :
    embedStacks e (fun _ => []) = fun _ => [] := by
  classical
  funext l
  simp only [embedStacks]
  split <;> rfl

lemma embedStacks_pure {K L : Type} [DecidableEq K] [DecidableEq L]
    (e : K ↪ L) (k : K) (bits : List Bool) :
    embedStacks e (Function.update (fun _ => []) k bits) =
      Function.update (fun _ => []) (e k) bits := by
  rw [embedStacks_update,embedStacks_empty]

lemma initList_bool (p : Program) (bits : List Bool) :
    initList p.machine bits = ⟨some p.main,p.initial,Function.update (fun _ => []) p.input bits⟩ := by
  unfold initList
  congr 1
  funext k
  simp only [Program.machine,Function.update_apply]
  split <;> rfl

lemma haltList_bool (p : Program) (bits : List Bool) :
    haltList p.machine bits = ⟨none,p.initial,Function.update (fun _ => []) p.output bits⟩ := by
  unfold haltList
  congr 1
  funext k
  simp only [Program.machine,Function.update_apply]
  split <;> rfl

namespace Composition
variable (p q : Program)

abbrev Stack := p.K ⊕ {k : q.K // k ≠ q.input}

def leftStack : p.K ↪ Stack p q := ⟨Sum.inl,Sum.inl_injective⟩

def rightStack : q.K ↪ Stack p q where
  toFun k := if h : k = q.input then Sum.inl p.output else Sum.inr ⟨k,h⟩
  inj' := by
    intro k j h
    by_cases hk : k = q.input <;> by_cases hj : j = q.input
    · exact hk.trans hj.symm
    · simp only [dite_eq_left hk,dite_eq_right hj] at h
      contradiction
    · simp only [dite_eq_right hk,dite_eq_left hj] at h
      contradiction
    · simp only [dite_eq_right hk,dite_eq_right hj,Sum.inr.injEq,Subtype.mk.injEq] at h
      exact h

@[simp] lemma rightStack_input : rightStack p q q.input = Sum.inl p.output := by
  simp [rightStack]

noncomputable abbrev program : Program where
  K := Stack p q
  input := Sum.inl p.input
  output := rightStack p q q.output
  Label := p.Label ⊕ q.Label
  main := Sum.inl p.main
  State := p.State × q.State
  initial := (p.initial,q.initial)
  code := fun l => match l with
    | .inl l => renameStmt (leftStack p q) Sum.inl (fun s => (s,q.initial)) Prod.fst
        (some (Sum.inr q.main)) (p.code l)
    | .inr l => renameStmt (rightStack p q) Sum.inr (fun s => (p.initial,s)) Prod.snd
        none (q.code l)

noncomputable def leftCfg : p.machine.Cfg → (program p q).machine.Cfg :=
  renameCfg (leftStack p q) Sum.inl (fun s => (s,q.initial)) (some (Sum.inr q.main))

noncomputable def rightCfg : q.machine.Cfg → (program p q).machine.Cfg :=
  renameCfg (rightStack p q) Sum.inr (fun s => (p.initial,s)) none

lemma left_step (s t : p.machine.Cfg) (h : p.machine.step s = some t) :
    (program p q).machine.step (leftCfg p q s) = some (leftCfg p q t) := by
  rcases s with ⟨l,v,stk⟩
  cases l with
  | none => simp only [FinTM2.step,TM2.step] at h; contradiction
  | some l =>
    simp only [FinTM2.step,TM2.step] at h
    have ht := Option.some.inj h
    subst t
    change some (TM2.stepAux (renameStmt (leftStack p q) Sum.inl
      (fun s => (s,q.initial)) Prod.fst (some (Sum.inr q.main)) (p.code l))
        (v,q.initial) (embedStacks (leftStack p q) stk)) = _
    rw [stepAux_rename _ _ _ _ (fun _ => rfl)]
    rfl

lemma right_step (s t : q.machine.Cfg) (h : q.machine.step s = some t) :
    (program p q).machine.step (rightCfg p q s) = some (rightCfg p q t) := by
  rcases s with ⟨l,v,stk⟩
  cases l with
  | none => simp only [FinTM2.step,TM2.step] at h; contradiction
  | some l =>
    simp only [FinTM2.step,TM2.step] at h
    have ht := Option.some.inj h
    subst t
    change some (TM2.stepAux (renameStmt (rightStack p q) Sum.inr
      (fun s => (p.initial,s)) Prod.snd none (q.code l))
        (p.initial,v) (embedStacks (rightStack p q) stk)) = _
    rw [stepAux_rename _ _ _ _ (fun _ => rfl)]
    rfl

lemma left_initial (bits : List Bool) :
    leftCfg p q (initList p.machine bits) = initList (program p q).machine bits := by
  rw [initList_bool,initList_bool]
  change (⟨some (Sum.inl p.main),(p.initial,q.initial),
      embedStacks (leftStack p q) (Function.update (fun _ => []) p.input bits)⟩ : (program p q).machine.Cfg) = _
  rw [embedStacks_pure]
  rfl

lemma handoff (bits : List Bool) :
    leftCfg p q (haltList p.machine bits) = rightCfg p q (initList q.machine bits) := by
  rw [haltList_bool,initList_bool]
  change (⟨some (Sum.inr q.main),(p.initial,q.initial),
    embedStacks (leftStack p q) (Function.update (fun _ => []) p.output bits)⟩ : (program p q).machine.Cfg) =
    ⟨some (Sum.inr q.main),(p.initial,q.initial),
    embedStacks (rightStack p q) (Function.update (fun _ => []) q.input bits)⟩
  rw [embedStacks_pure,embedStacks_pure,rightStack_input]
  rfl

lemma right_final (bits : List Bool) :
    rightCfg p q (haltList q.machine bits) = haltList (program p q).machine bits := by
  rw [haltList_bool,haltList_bool]
  change (⟨none,(p.initial,q.initial),
      embedStacks (rightStack p q) (Function.update (fun _ => []) q.output bits)⟩ : (program p q).machine.Cfg) = _
  rw [embedStacks_pure]

noncomputable def outputs {x y z : List Bool} {m n : ℕ}
    (hp : TM2OutputsInTime p.machine x (some y) m)
    (hq : TM2OutputsInTime q.machine y (some z) n) :
    TM2OutputsInTime (program p q).machine x (some z) (n+m) := by
  have h1 := iterate_transfer p.machine.step (program p q).machine.step (leftCfg p q)
    (left_step p q) hp.steps (initList p.machine x) (haltList p.machine y) hp.evals_in_steps
  have h2 := iterate_transfer q.machine.step (program p q).machine.step (rightCfg p q)
    (right_step p q) hq.steps (initList q.machine y) (haltList q.machine z) hq.evals_in_steps
  rw [left_initial,handoff] at h1
  rw [right_final] at h2
  refine ⟨⟨hq.steps+hp.steps,?_⟩,Nat.add_le_add hq.steps_le_m hp.steps_le_m⟩
  change (fun x : Option (program p q).machine.Cfg => x.bind (program p q).machine.step)^[hq.steps+hp.steps]
    (some (initList (program p q).machine x)) = some (haltList (program p q).machine z)
  rw [Function.iterate_add_apply,h1,h2]

end Composition
end MetricKMedianRecovery.BitMachine

end OAI
