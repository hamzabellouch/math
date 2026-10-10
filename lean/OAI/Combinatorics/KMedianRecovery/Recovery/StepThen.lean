import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.StackLength

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

lemma unit_update {α : Type} (f : Unit → α) (a : α) :
    Function.update f () a = fun _ => a := by
  funext u
  cases u
  simp only [Function.update_self]

noncomputable def step_then {S : Type} {f : S → Option S} {s t : S} {z : Option S} {n : ℕ}
    (h : f s = some t) (ht : EvalsToInTime f t z n) : EvalsToInTime f s z (n+1) := by
  refine ⟨⟨ht.steps+1,?_⟩,Nat.add_le_add_right ht.steps_le_m 1⟩
  rw [Function.iterate_succ_apply]
  change (fun x : Option S => x.bind f)^[ht.steps] (f s) = z
  rw [h]
  exact ht.evals_in_steps

noncomputable def time_mono {S : Type} {f : S → Option S} {s : S} {z : Option S} {m n : ℕ}
    (h : EvalsToInTime f s z m) (hm : m ≤ n) : EvalsToInTime f s z n :=
  ⟨h.toEvalsTo,h.steps_le_m.trans hm⟩

noncomputable def one_step {S : Type} {f : S → Option S} {s t : S}
    (h : f s = some t) : EvalsToInTime f s (some t) 1 :=
  ⟨⟨1,h⟩,le_rfl⟩

def discardPrefix : List Bool → List Bool
  | true :: _ :: bits => discardPrefix bits
  | true :: [] => []
  | false :: bits => bits
  | [] => []

lemma discardPrefix_pair (x y : List Bool) :
    discardPrefix (x.flatMap (fun b => [true,b]) ++ [false] ++ y) = y := by
  induction x with
  | nil => rfl
  | cons b x ih => simpa only [List.flatMap_cons,List.cons_append,List.nil_append,discardPrefix] using ih

abbrev tailProgram : Program where
  K := Unit
  input := ()
  output := ()
  Label := Unit
  main := ()
  State := Option Bool
  initial := none
  code _ := .pop () (fun _ b => b)
    (.branch (fun s => decide (s = some true))
      (.pop () (fun _ _ => none) (.goto (fun _ => ())))
      (.load (fun _ => none) .halt))

def tailCfg (xs : List Bool) : tailProgram.machine.Cfg := ⟨some (),none,fun _ => xs⟩
def tailEnd (xs : List Bool) : tailProgram.machine.Cfg := ⟨none,none,fun _ => xs⟩

lemma tail_initial (xs : List Bool) : initList tailProgram.machine xs = tailCfg xs := by
  exact (initList_bool tailProgram xs).trans
    (congrArg (fun stk : Unit → List Bool => (⟨some (),none,stk⟩ : tailProgram.machine.Cfg))
      (unit_update (fun _ => []) xs))

lemma tail_final (xs : List Bool) : haltList tailProgram.machine xs = tailEnd xs := by
  exact (haltList_bool tailProgram xs).trans
    (congrArg (fun stk : Unit → List Bool => (⟨none,none,stk⟩ : tailProgram.machine.Cfg))
      (unit_update (fun _ => []) xs))

lemma tail_step_nil : tailProgram.machine.step (tailCfg []) = some (tailEnd []) := by
  simp [FinTM2.step,tailCfg,tailEnd,tailProgram,TM2.step,TM2.stepAux]
  rfl

lemma tail_step_false (xs : List Bool) :
    tailProgram.machine.step (tailCfg (false::xs)) = some (tailEnd xs) := by
  simp [FinTM2.step,tailCfg,tailEnd,tailProgram,TM2.step,TM2.stepAux,unit_update]
  rfl

lemma tail_step_true (xs : List Bool) :
    tailProgram.machine.step (tailCfg (true::xs)) = some (tailCfg xs.tail) := by
  simp [FinTM2.step,tailCfg,tailProgram,TM2.step,TM2.stepAux,unit_update]
  rfl

noncomputable def tail_outputs (xs : List Bool) :
    EvalsToInTime tailProgram.machine.step (tailCfg xs) (some (tailEnd (discardPrefix xs)))
      (xs.length+1) := by
  induction xs using List.twoStepInduction with
  | nil => exact one_step tail_step_nil
  | singleton b =>
    cases b with
    | false => exact time_mono (one_step (tail_step_false [])) (by decide)
    | true => exact step_then (tail_step_true []) (one_step tail_step_nil)
  | cons_cons b c xs ih _ihc =>
    cases b with
    | false => exact time_mono (one_step (tail_step_false (c::xs))) (by simp)
    | true =>
      have hh := step_then (tail_step_true (c::xs)) ih
      exact time_mono hh (by simp)

noncomputable def discardPrefix_computes : PolyComputes discardPrefix where
  program := tailProgram
  time := Polynomial.X+1
  outputs xs := by
    simpa only [TM2OutputsInTime,Option.map_some,tail_initial,tail_final,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using tail_outputs xs

def twoStacks (xs ys : List Bool) : Stacks Bool := fun k => cond k ys xs

@[simp] lemma twoStacks_false (xs ys : List Bool) : twoStacks xs ys false = xs := rfl
@[simp] lemma twoStacks_true (xs ys : List Bool) : twoStacks xs ys true = ys := rfl

lemma twoStacks_update_false (xs ys zs : List Bool) :
    Function.update (twoStacks xs ys) false zs = twoStacks zs ys := by
  funext b
  cases b <;> rfl

lemma twoStacks_update_true (xs ys zs : List Bool) :
    Function.update (twoStacks xs ys) true zs = twoStacks xs zs := by
  funext b
  cases b <;> rfl

lemma twoStacks_pure_false (xs : List Bool) :
    Function.update (fun _ : Bool => []) false xs = twoStacks xs [] := by
  funext b
  cases b <;> rfl

lemma twoStacks_pure_true (xs : List Bool) :
    Function.update (fun _ : Bool => []) true xs = twoStacks [] xs := by
  funext b
  cases b <;> rfl

abbrev reverseProgram : Program where
  K := Bool
  input := false
  output := true
  Label := Unit
  main := ()
  State := Option Bool
  initial := none
  code _ := .pop false (fun _ b => b)
    (.branch Option.isSome
      (.push true (fun b => b.getD false) (.load (fun _ => none) (.goto (fun _ => ()))))
      (.load (fun _ => none) .halt))

def reverseCfg (xs ys : List Bool) : reverseProgram.machine.Cfg :=
  ⟨some (),none,twoStacks xs ys⟩
def reverseEnd (ys : List Bool) : reverseProgram.machine.Cfg :=
  ⟨none,none,twoStacks [] ys⟩

lemma reverse_initial (xs : List Bool) : initList reverseProgram.machine xs = reverseCfg xs [] := by
  exact (initList_bool reverseProgram xs).trans
    (congrArg (fun stk : Stacks Bool => (⟨some (),none,stk⟩ : reverseProgram.machine.Cfg))
      (twoStacks_pure_false xs))

lemma reverse_final (xs : List Bool) : haltList reverseProgram.machine xs = reverseEnd xs := by
  exact (haltList_bool reverseProgram xs).trans
    (congrArg (fun stk : Stacks Bool => (⟨none,none,stk⟩ : reverseProgram.machine.Cfg))
      (twoStacks_pure_true xs))

lemma reverse_step_nil (ys : List Bool) :
    reverseProgram.machine.step (reverseCfg [] ys) = some (reverseEnd ys) := by
  simp [FinTM2.step,reverseCfg,reverseEnd,reverseProgram,TM2.step,TM2.stepAux,twoStacks_update_false]
  rfl

lemma reverse_step_cons (b : Bool) (xs ys : List Bool) :
    reverseProgram.machine.step (reverseCfg (b::xs) ys) = some (reverseCfg xs (b::ys)) := by
  simp [FinTM2.step,reverseCfg,reverseProgram,TM2.step,TM2.stepAux,
    twoStacks_update_false,twoStacks_update_true]
  rfl

noncomputable def reverse_outputs (xs ys : List Bool) :
    EvalsToInTime reverseProgram.machine.step (reverseCfg xs ys) (some (reverseEnd (xs.reverse++ys)))
      (xs.length+1) := by
  induction xs generalizing ys with
  | nil => exact one_step (reverse_step_nil ys)
  | cons b xs ih =>
    have hh := step_then (reverse_step_cons b xs ys) (ih (b::ys))
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hh

noncomputable def reverse_computes : PolyComputes List.reverse where
  program := reverseProgram
  time := Polynomial.X+1
  outputs xs := by
    simpa only [List.append_nil,TM2OutputsInTime,Option.map_some,reverse_initial,reverse_final,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using reverse_outputs xs []

end MetricKMedianRecovery.BitMachine

end OAI
