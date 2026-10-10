import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.StepThen

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace SameIO
variable (p : Program)

abbrev Stack := p.K ⊕ Unit

def baseStack : p.K ↪ Stack p := ⟨Sum.inl,Sum.inl_injective⟩
def firstStack : Bool ↪ Stack p where
  toFun b := cond b (Sum.inr ()) (Sum.inl p.output)
  inj' := by intro a b h; cases a <;> cases b <;> simp_all
def secondStack : Bool ↪ Stack p where
  toFun b := cond b (Sum.inl p.input) (Sum.inr ())
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

noncomputable abbrev program : Program where
  K := Stack p
  input := Sum.inl p.input
  output := Sum.inl p.input
  Label := p.Label ⊕ Bool
  main := Sum.inl p.main
  State := p.State × Option Bool
  initial := (p.initial,none)
  code l := match l with
    | .inl l => renameStmt (baseStack p) Sum.inl (fun s => (s,none)) Prod.fst
        (some (Sum.inr false)) (p.code l)
    | .inr false => renameStmt (firstStack p) (fun _ => Sum.inr false)
        (fun s => (p.initial,s)) Prod.snd (some (Sum.inr true)) (reverseProgram.code ())
    | .inr true => renameStmt (secondStack p) (fun _ => Sum.inr true)
        (fun s => (p.initial,s)) Prod.snd none (reverseProgram.code ())

noncomputable def baseCfg : p.machine.Cfg → (program p).machine.Cfg :=
  renameCfg (baseStack p) Sum.inl (fun s => (s,none)) (some (Sum.inr false))
noncomputable def firstCfg : reverseProgram.machine.Cfg → (program p).machine.Cfg :=
  renameCfg (firstStack p) (fun _ => Sum.inr false) (fun s => (p.initial,s)) (some (Sum.inr true))
noncomputable def secondCfg : reverseProgram.machine.Cfg → (program p).machine.Cfg :=
  renameCfg (secondStack p) (fun _ => Sum.inr true) (fun s => (p.initial,s)) none

lemma base_step (s t : p.machine.Cfg) (h : p.machine.step s = some t) :
    (program p).machine.step (baseCfg p s) = some (baseCfg p t) := by
  rcases s with ⟨l,v,stk⟩
  cases l with
  | none => simp only [FinTM2.step,TM2.step] at h; contradiction
  | some l =>
    simp only [FinTM2.step,TM2.step] at h
    have ht := Option.some.inj h
    subst t
    change some (TM2.stepAux (renameStmt (baseStack p) Sum.inl (fun s => (s,none)) Prod.fst
      (some (Sum.inr false)) (p.code l)) (v,none) (embedStacks (baseStack p) stk)) = _
    rw [stepAux_rename _ _ _ _ (fun _ => rfl)]
    rfl

lemma first_step (s t : reverseProgram.machine.Cfg) (h : reverseProgram.machine.step s = some t) :
    (program p).machine.step (firstCfg p s) = some (firstCfg p t) := by
  rcases s with ⟨l,v,stk⟩
  cases l with
  | none => simp only [FinTM2.step,TM2.step] at h; contradiction
  | some l =>
    cases l
    simp only [FinTM2.step,TM2.step] at h
    have ht := Option.some.inj h
    subst t
    change some (TM2.stepAux (renameStmt (firstStack p) (fun _ => Sum.inr false)
      (fun s => (p.initial,s)) Prod.snd (some (Sum.inr true)) (reverseProgram.code ()))
      (p.initial,v) (embedStacks (firstStack p) stk)) = _
    rw [stepAux_rename _ _ _ _ (fun _ => rfl)]
    rfl

lemma second_step (s t : reverseProgram.machine.Cfg) (h : reverseProgram.machine.step s = some t) :
    (program p).machine.step (secondCfg p s) = some (secondCfg p t) := by
  rcases s with ⟨l,v,stk⟩
  cases l with
  | none => simp only [FinTM2.step,TM2.step] at h; contradiction
  | some l =>
    cases l
    simp only [FinTM2.step,TM2.step] at h
    have ht := Option.some.inj h
    subst t
    change some (TM2.stepAux (renameStmt (secondStack p) (fun _ => Sum.inr true)
      (fun s => (p.initial,s)) Prod.snd none (reverseProgram.code ()))
      (p.initial,v) (embedStacks (secondStack p) stk)) = _
    rw [stepAux_rename _ _ _ _ (fun _ => rfl)]
    rfl

lemma base_initial (bits : List Bool) :
    baseCfg p (initList p.machine bits) = initList (program p).machine bits := by
  rw [initList_bool,initList_bool]
  change (⟨some (Sum.inl p.main),(p.initial,none),
    embedStacks (baseStack p) (Function.update (fun _ => []) p.input bits)⟩ : (program p).machine.Cfg) = _
  rw [embedStacks_pure]
  rfl

lemma first_handoff (bits : List Bool) :
    baseCfg p (haltList p.machine bits) = firstCfg p (initList reverseProgram.machine bits) := by
  rw [haltList_bool,initList_bool]
  change (⟨some (Sum.inr false),(p.initial,none),
    embedStacks (baseStack p) (Function.update (fun _ => []) p.output bits)⟩ : (program p).machine.Cfg) =
    ⟨some (Sum.inr false),(p.initial,none),
    embedStacks (firstStack p) (Function.update (fun _ => []) false bits)⟩
  rw [embedStacks_pure,embedStacks_pure]
  rfl

lemma second_handoff (bits : List Bool) :
    firstCfg p (haltList reverseProgram.machine bits) = secondCfg p (initList reverseProgram.machine bits) := by
  rw [haltList_bool,initList_bool]
  change (⟨some (Sum.inr true),(p.initial,none),
    embedStacks (firstStack p) (Function.update (fun _ => []) true bits)⟩ : (program p).machine.Cfg) =
    ⟨some (Sum.inr true),(p.initial,none),
    embedStacks (secondStack p) (Function.update (fun _ => []) false bits)⟩
  rw [embedStacks_pure,embedStacks_pure]
  rfl

lemma second_final (bits : List Bool) :
    secondCfg p (haltList reverseProgram.machine bits) = haltList (program p).machine bits := by
  rw [haltList_bool,haltList_bool]
  change (⟨none,(p.initial,none),
    embedStacks (secondStack p) (Function.update (fun _ => []) true bits)⟩ : (program p).machine.Cfg) = _
  rw [embedStacks_pure]
  rfl

noncomputable def outputs {x y : List Bool} {m : ℕ}
    (h : TM2OutputsInTime p.machine x (some y) m) :
    TM2OutputsInTime (program p).machine x (some y) (m+2*(y.length+1)) := by
  have h1 := reverse_computes.outputs y
  have h2 := reverse_computes.outputs y.reverse
  have h0' := iterate_transfer p.machine.step (program p).machine.step (baseCfg p) (base_step p)
    h.steps (initList p.machine x) (haltList p.machine y) h.evals_in_steps
  have h1' := iterate_transfer reverseProgram.machine.step (program p).machine.step (firstCfg p) (first_step p)
    h1.steps (initList reverseProgram.machine y) (haltList reverseProgram.machine y.reverse) h1.evals_in_steps
  have h2' := iterate_transfer reverseProgram.machine.step (program p).machine.step (secondCfg p) (second_step p)
    h2.steps (initList reverseProgram.machine y.reverse) (haltList reverseProgram.machine y.reverse.reverse) h2.evals_in_steps
  rw [base_initial,first_handoff] at h0'
  rw [second_handoff] at h1'
  rw [second_final] at h2'
  simp only [List.reverse_reverse] at h2'
  refine ⟨⟨h2.steps+(h1.steps+h.steps),?_⟩,?_⟩
  · change (fun s : Option (program p).machine.Cfg => s.bind (program p).machine.step)^[h2.steps+(h1.steps+h.steps)]
      (some (initList (program p).machine x)) = some (haltList (program p).machine y)
    rw [Function.iterate_add_apply,Function.iterate_add_apply,h0',h1',h2']
  · change h2.steps+(h1.steps+h.steps) ≤ m+2*(y.length+1)
    have hm0 := h.steps_le_m
    have hm1 := h1.steps_le_m
    have hm2 := h2.steps_le_m
    simp only [reverse_computes,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,List.length_reverse] at hm1 hm2
    omega

end SameIO

noncomputable def PolyComputes.sameIO {f : List Bool → List Bool} (h : PolyComputes f) : PolyComputes f where
  program := SameIO.program h.program
  time := h.time+2*(Polynomial.X+h.time*Polynomial.C h.program.maxPush+1)
  outputs x := by
    have hh := SameIO.outputs h.program (h.outputs x)
    refine ⟨hh.toEvalsTo,?_⟩
    apply hh.steps_le_m.trans
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_ofNat,
      Polynomial.eval_one]
    have hl := h.program.output_length (h.outputs x)
    omega

end MetricKMedianRecovery.BitMachine

end OAI
