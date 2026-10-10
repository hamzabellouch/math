import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.StepThen

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

def extractPrefix : List Bool → List Bool
  | true :: b :: bits => b :: extractPrefix bits
  | _ => []

lemma extractPrefix_pair (x y : List Bool) :
    extractPrefix (x.flatMap (fun b => [true,b]) ++ [false] ++ y) = x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    simpa only [List.flatMap_cons,List.cons_append,List.nil_append,extractPrefix] using congrArg (List.cons b) ih

abbrev headProgram : Program where
  K := Bool
  input := false
  output := true
  Label := Bool
  main := false
  State := Option Bool
  initial := none
  code l := if l then
    .pop false (fun _ b => b)
      (.branch Option.isSome
        (.load (fun _ => none) (.goto (fun _ => true)))
        (.load (fun _ => none) .halt))
    else
    .pop false (fun _ b => b)
      (.branch (fun s => decide (s = some true))
        (.pop false (fun _ b => b)
          (.branch Option.isSome
            (.push true (fun b => b.getD false) (.load (fun _ => none) (.goto (fun _ => false))))
            (.load (fun _ => none) .halt)))
        (.load (fun _ => none) (.goto (fun _ => true))))

def headCfg (l : Bool) (xs ys : List Bool) : headProgram.machine.Cfg :=
  ⟨some l,none,twoStacks xs ys⟩
def headEnd (ys : List Bool) : headProgram.machine.Cfg :=
  ⟨none,none,twoStacks [] ys⟩

lemma head_initial (xs : List Bool) : initList headProgram.machine xs = headCfg false xs [] := by
  exact (initList_bool headProgram xs).trans
    (congrArg (fun stk : Stacks Bool => (⟨some false,none,stk⟩ : headProgram.machine.Cfg))
      (twoStacks_pure_false xs))

lemma head_final (xs : List Bool) : haltList headProgram.machine xs = headEnd xs := by
  exact (haltList_bool headProgram xs).trans
    (congrArg (fun stk : Stacks Bool => (⟨none,none,stk⟩ : headProgram.machine.Cfg))
      (twoStacks_pure_true xs))

lemma head_clear_nil (ys : List Bool) :
    headProgram.machine.step (headCfg true [] ys) = some (headEnd ys) := by
  simp [FinTM2.step,headCfg,headEnd,headProgram,TM2.step,TM2.stepAux,twoStacks_update_false]
  rfl

lemma head_clear_cons (b : Bool) (xs ys : List Bool) :
    headProgram.machine.step (headCfg true (b::xs) ys) = some (headCfg true xs ys) := by
  simp [FinTM2.step,headCfg,headProgram,TM2.step,TM2.stepAux,twoStacks_update_false]
  rfl

noncomputable def head_clear_outputs (xs ys : List Bool) :
    EvalsToInTime headProgram.machine.step (headCfg true xs ys) (some (headEnd ys)) (xs.length+1) := by
  induction xs with
  | nil => exact one_step (head_clear_nil ys)
  | cons b xs ih => exact step_then (head_clear_cons b xs ys) ih

lemma head_step_nil (ys : List Bool) :
    headProgram.machine.step (headCfg false [] ys) = some (headCfg true [] ys) := by
  simp [FinTM2.step,headCfg,headProgram,TM2.step,TM2.stepAux,twoStacks_update_false]
  rfl

lemma head_step_one (ys : List Bool) :
    headProgram.machine.step (headCfg false [true] ys) = some (headEnd ys) := by
  simp [FinTM2.step,headCfg,headEnd,headProgram,TM2.step,TM2.stepAux,twoStacks_update_false]
  rfl

lemma head_step_false (xs ys : List Bool) :
    headProgram.machine.step (headCfg false (false::xs) ys) = some (headCfg true xs ys) := by
  simp [FinTM2.step,headCfg,headProgram,TM2.step,TM2.stepAux,twoStacks_update_false]
  rfl

lemma head_step_true (b : Bool) (xs ys : List Bool) :
    headProgram.machine.step (headCfg false (true::b::xs) ys) = some (headCfg false xs (b::ys)) := by
  simp [FinTM2.step,headCfg,headProgram,TM2.step,TM2.stepAux,twoStacks_update_false,twoStacks_update_true]
  rfl

noncomputable def head_outputs (xs ys : List Bool) :
    EvalsToInTime headProgram.machine.step (headCfg false xs ys)
      (some (headEnd ((extractPrefix xs).reverse++ys))) (xs.length+2) := by
  induction xs using List.twoStepInduction generalizing ys with
  | nil => exact step_then (head_step_nil ys) (one_step (head_clear_nil ys))
  | singleton b =>
    cases b with
    | false => exact time_mono (step_then (head_step_false [] ys) (head_clear_outputs [] ys)) (by decide)
    | true => exact time_mono (one_step (head_step_one ys)) (by decide)
  | cons_cons b c xs ih _ =>
    cases b with
    | false =>
      exact time_mono (step_then (head_step_false (c::xs) ys) (head_clear_outputs (c::xs) ys)) (by simp)
    | true =>
      have hh := step_then (head_step_true c xs ys) (ih (c::ys))
      simp only [extractPrefix,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp)

noncomputable def extractReverse_computes : PolyComputes (fun xs => (extractPrefix xs).reverse) where
  program := headProgram
  time := Polynomial.X+2
  outputs xs := by
    simpa only [TM2OutputsInTime,Option.map_some,head_initial,head_final,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat,List.append_nil] using head_outputs xs []

noncomputable def extractPrefix_computes : PolyComputes extractPrefix := by
  have hh := extractReverse_computes.comp reverse_computes
  simpa only [Function.comp_def,List.reverse_reverse] using hh

end MetricKMedianRecovery.BitMachine

end OAI
