import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineLookupSpec
import OAI.Combinatorics.IndependentSets.Machines.MachineLookupDiscard

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineLookup

open Turing
open MachineComposition

variable {K σ : Type} [DecidableEq K]

theorem guard_step_succ (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (i : Nat) (indexSuffix input output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program index source destination)
      ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord (i + 1) ++ indexSuffix) input output⟩ =
      some ⟨some .skip, (ambient, none), tapes index source destination base
        (encodeWord i ++ indexSuffix) input output⟩ := by
  change some (TM2.stepAux (program index source destination .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux,
    tapes_index, his, hid, encodeWord, List.replicate_succ, update_index]

theorem guard_step_zero (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (indexSuffix input output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program index source destination)
      ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) input output⟩ =
      some ⟨some .select, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) input output⟩ := by
  change some (TM2.stepAux (program index source destination .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux,
    tapes_index, his, hid, encodeWord]

theorem select_step_nonempty (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter input output : List Bool) (hinput : input ≠ [])
    (ambient : σ) (register : Option Bool) :
    TM2.step (program index source destination)
      ⟨some .select, (ambient, register),
        tapes index source destination base counter input output⟩ =
      some ⟨some .copy, (ambient, input.head?),
        tapes index source destination base counter input (false :: output)⟩ := by
  change some (TM2.stepAux (program index source destination .select) _ _) = _
  cases input with
  | nil => exact (hinput rfl).elim
  | cons head tail =>
    simp [program, select, Hastad.SourceMachine.fieldStart, TM2.stepAux,
      tapes_source, hsd, update_destination]

theorem select_step_empty (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step (program index source destination)
      ⟨some .select, (ambient, register),
        tapes index source destination base counter [] output⟩ =
      some ⟨some .rejected, (ambient, none),
        tapes index source destination base counter [] output⟩ := by
  change some (TM2.stepAux (program index source destination .select) _ _) = _
  simp [program, select, TM2.stepAux, tapes_source, hsd]

theorem copyTrace (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter : List Bool) (n : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[n + 1]
      (some ⟨some .copy, (ambient, register), tapes index source destination base
        counter (encodeWord n ++ suffix) (false :: output)⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        counter suffix (encodeWord n ++ output)⟩ := by
  have h := Hastad.SourceMachine.fieldLoopTrace source destination hsd
    Label.copy (some Label.accepted) (program index source destination) rfl
    (Function.update base index counter) n suffix (false :: output) ambient register
  simpa only [Hastad.SourceMachine.fieldTapes, tapes, encodeWord,
    List.append_assoc, List.singleton_append] using h

theorem selectTrace (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter : List Bool) (n : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[n + 2]
      (some ⟨some .select, (ambient, register), tapes index source destination base
        counter (encodeWord n ++ suffix) output⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        counter suffix (encodeWord n ++ output)⟩ := by
  rw [show n + 2 = (n + 1) + 1 by omega, Function.iterate_succ_apply]
  simp only [advance_some]
  rw [select_step_nonempty index source destination hsd base counter
    (encodeWord n ++ suffix) output (by simp [encodeWord]) ambient register]
  exact copyTrace index source destination hsd base counter n suffix output ambient _

theorem skipCycleTrace (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (i n : Nat) (indexSuffix suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[n + 2]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord (i + 1) ++ indexSuffix) (encodeWord n ++ suffix) output⟩) =
      some ⟨some .guard, (ambient, none), tapes index source destination base
        (encodeWord i ++ indexSuffix) suffix output⟩ := by
  rw [show n + 2 = (n + 1) + 1 by omega, Function.iterate_succ_apply]
  simp only [advance_some]
  rw [guard_step_succ index source destination his hid]
  have h := discardTrace source Label.skip Label.guard
    (program index source destination) rfl
    (tapes index source destination base (encodeWord i ++ indexSuffix)
      (encodeWord n ++ suffix) output) n suffix (by simp [hsd]) ambient none
  simpa only [update_source index source destination hsd] using h

theorem emptyCycleTrace (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (i : Nat) (indexSuffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[2]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord (i + 1) ++ indexSuffix) [] output⟩) =
      some ⟨some .guard, (ambient, none), tapes index source destination base
        (encodeWord i ++ indexSuffix) [] output⟩ := by
  rw [show 2 = 1 + 1 from rfl, Function.iterate_succ_apply]
  simp only [Function.iterate_one, advance_some]
  rw [guard_step_succ index source destination his hid]
  exact discard_empty_step source Label.skip Label.guard (program index source destination)
    rfl (tapes index source destination base (encodeWord i ++ indexSuffix) [] output)
    (by simp [hsd]) ambient none

theorem successPrefixTrace (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (prior : List Nat) (value : Nat)
    (indexSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[
        (encodeWords prior).length + prior.length + value + 3]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord prior.length ++ indexSuffix)
        (encodeWords prior ++ (encodeWord value ++ suffix)) output⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) suffix (encodeWord value ++ output)⟩ := by
  induction prior generalizing register with
  | nil =>
    simp only [encodeWords, List.length_nil, Nat.zero_add, List.nil_append]
    rw [show value + 3 = (value + 2) + 1 by omega, Function.iterate_succ_apply]
    simp only [advance_some]
    rw [guard_step_zero index source destination his hid]
    exact selectTrace index source destination hsd base _ value suffix output ambient none
  | cons n prior ih =>
    simp only [encodeWords, List.length_cons, List.length_append, encodeWord_length]
    rw [show n + 1 + (encodeWords prior).length + (prior.length + 1) + value + 3 =
      ((encodeWords prior).length + prior.length + value + 3) + (n + 2) by omega,
      Function.iterate_add_apply]
    rw [List.append_assoc,
      skipCycleTrace index source destination his hid hsd base prior.length n]
    exact ih none

theorem lookupTrace_some (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i value : Nat)
    (selected : values[i]? = some value)
    (indexSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[MachineLookupSpec.steps values i]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord i ++ indexSuffix) (encodeWords values ++ suffix) output⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)) ++ suffix)
        (encodeWord value ++ output)⟩ := by
  have hi := (List.getElem?_eq_some_iff.mp selected).1
  have hlength : (values.take i).length = i := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hsource : encodeWords (values.take i) ++
      (encodeWord value ++ (encodeWords (values.drop (i + 1)) ++ suffix)) =
      encodeWords values ++ suffix := by
    rw [MachineLookupSpec.encoded_selected_split values i value selected]
    simp only [List.append_assoc]
  have htime : MachineLookupSpec.steps values i =
      (encodeWords (values.take i)).length + i + value + 3 := by
    rw [MachineLookupSpec.steps_eq_scannedBits_of_some values i value selected,
      MachineLookupSpec.scannedBits_of_some values i value selected]
    omega
  have h := successPrefixTrace index source destination his hid hsd base (values.take i)
    value indexSuffix (encodeWords (values.drop (i + 1)) ++ suffix) output ambient register
  rw [hlength, hsource] at h
  simpa only [htime] using h

theorem emptyTrace (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (i : Nat) (indexSuffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[2 * i + 2]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord i ++ indexSuffix) [] output⟩) =
      some ⟨some .rejected, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) [] output⟩ := by
  induction i generalizing register with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [show 2 = 1 + 1 from rfl, Function.iterate_succ_apply]
    simp only [Function.iterate_one, advance_some]
    rw [guard_step_zero index source destination his hid]
    exact select_step_empty index source destination hsd base _ output ambient none
  | succ i ih =>
    rw [show 2 * (i + 1) + 2 = (2 * i + 2) + 2 by omega,
      Function.iterate_add_apply, emptyCycleTrace index source destination his hid hsd]
    exact ih none

theorem lookupTrace_invalid (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i : Nat) (invalid : values.length ≤ i)
    (indexSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[MachineLookupSpec.steps values i]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord i ++ indexSuffix) (encodeWords values) output⟩) =
      some ⟨some .rejected, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) [] output⟩ := by
  induction values generalizing i register with
  | nil =>
    simpa only [MachineLookupSpec.steps, encodeWords] using
      emptyTrace index source destination his hid hsd base i indexSuffix output ambient register
  | cons n values ih =>
    cases i with
    | zero => simp at invalid
    | succ i =>
      simp only [MachineLookupSpec.steps, encodeWords]
      rw [Nat.add_comm (n + 2), Function.iterate_add_apply,
        skipCycleTrace index source destination his hid hsd]
      exact ih i (by simpa using invalid) none

def resultLabel (values : List Nat) (i : Nat) : Label :=
  match values[i]? with
  | some _ => .accepted
  | none => .rejected

def resultOutput (values : List Nat) (i : Nat) (output : List Bool) : List Bool :=
  match values[i]? with
  | some value => encodeWord value ++ output
  | none => output

theorem lookupTrace (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i : Nat)
    (indexSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[MachineLookupSpec.steps values i]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord i ++ indexSuffix) (encodeWords values) output⟩) =
      some ⟨some (resultLabel values i), (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)))
        (resultOutput values i output)⟩ := by
  cases selected : values[i]? with
  | some value =>
    simpa only [List.append_nil, resultLabel, resultOutput, selected] using
      lookupTrace_some index source destination his hid hsd base values i value selected
        indexSuffix [] output ambient register
  | none =>
    have invalid : values.length ≤ i := List.getElem?_eq_none_iff.mp selected
    have hdrop : values.drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
    simpa only [resultLabel, resultOutput, selected, hdrop, encodeWords] using
      lookupTrace_invalid index source destination his hid hsd base values i invalid
        indexSuffix output ambient register

def lookupInTime (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i : Nat)
    (indexSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program index source destination))
      ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord i ++ indexSuffix) (encodeWords values) output⟩
      (some ⟨some (resultLabel values i), (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)))
        (resultOutput values i output)⟩)
      ((encodeWords values).length + 2 * (encodeWord i).length) where
  steps := MachineLookupSpec.steps values i
  evals_in_steps := lookupTrace index source destination his hid hsd base values i
    indexSuffix output ambient register
  steps_le_m := MachineLookupSpec.steps_le_input_encoding_size values i

theorem lookupHaltTrace (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i : Nat)
    (indexSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[MachineLookupSpec.steps values i + 1]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord i ++ indexSuffix) (encodeWords values) output⟩) =
      some ⟨none, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)))
        (resultOutput values i output)⟩ := by
  rw [Function.iterate_succ_apply', lookupTrace index source destination his hid hsd]
  simp only [advance_some]
  cases selected : values[i]? <;> simp [resultLabel, selected, TM2.step, program, TM2.stepAux]

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 2 * Polynomial.X + 1

theorem timePolynomial_bounds (values : List Nat) (i : Nat) :
    MachineLookupSpec.steps values i + 1 ≤
      timePolynomial.eval ((encodeWords values).length + (encodeWord i).length) := by
  have h := MachineLookupSpec.steps_le_input_encoding_size values i
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one]
  omega

def machineInTime (base : Fin 3 → List Bool) (values : List Nat) (i : Nat)
    (indexSuffix output : List Bool) (register : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      ⟨some .guard, ((), register), tapes (K := Fin 3) 0 1 2 base
        (encodeWord i ++ indexSuffix) (encodeWords values) output⟩
      (some ⟨none, ((), none), tapes (K := Fin 3) 0 1 2 base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)))
        (resultOutput values i output)⟩)
      (timePolynomial.eval ((encodeWords values).length + (encodeWord i).length)) where
  steps := MachineLookupSpec.steps values i + 1
  evals_in_steps := lookupHaltTrace (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    base values i indexSuffix output () register
  steps_le_m := timePolynomial_bounds values i

end IndependentSetsGames.Foundations.Complexity.MachineLookup

end OAI
