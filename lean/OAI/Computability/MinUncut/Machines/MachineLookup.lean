import Mathlib
import OAI.Computability.MinUncut.Machines.Input

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineLookup

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

end MinUncutGames.Foundations.Complexity.MachineLookup

end
section
namespace MinUncutGames.Foundations.Complexity.MachineFixedBlockMap

open Turing

abbrev Buffer (N : Nat) := Fin N → Bool

def emptyBuffer (N : Nat) : Buffer N := fun _ => false

section Chains

variable {K Λ σ : Type} {N : Nat}

def readSlots (src : K) : List (Fin N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)
  | [], next => next
  | i :: slots, next =>
      .pop src (fun state head =>
        (state.1, Function.update state.2 i (head.getD false)))
        (readSlots src slots next)

def fill (slots : List (Fin N)) (bits buffer : Buffer N) : Buffer N :=
  slots.foldl (fun buffer i => Function.update buffer i (bits i)) buffer

theorem fill_apply (slots : List (Fin N)) (bits buffer : Buffer N) (i : Fin N) :
    fill slots bits buffer i = if i ∈ slots then bits i else buffer i := by
  induction slots generalizing buffer with
  | nil => simp [fill]
  | cons j slots ih =>
      change fill slots bits (Function.update buffer j (bits j)) i = _
      rw [ih]
      by_cases hm : i ∈ slots
      · simp [hm]
      · by_cases he : i = j <;> simp [hm, he]

@[simp] theorem fill_all (bits buffer : Buffer N) :
    fill (List.ofFn id) bits buffer = bits := by
  funext i
  simp [fill_apply, List.mem_ofFn]

variable [DecidableEq K]

theorem stepAux_readSlots (src : K) (slots : List (Fin N))
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (ambient : σ) (bits buffer : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool) :
    TM2.stepAux (readSlots src slots next) (ambient, buffer)
        (Function.update tapes src (slots.map bits ++ suffix)) =
      TM2.stepAux next (ambient, fill slots bits buffer)
        (Function.update tapes src suffix) := by
  induction slots generalizing buffer tapes with
  | nil => simp [readSlots, fill]
  | cons i slots ih =>
      simpa only [readSlots, List.map_cons, List.cons_append, TM2.stepAux,
        Function.update_self, List.head?_cons, Option.getD_some, List.tail_cons,
        Function.update_idem, fill, List.foldl_cons] using
        ih (Function.update buffer i (bits i)) tapes

theorem stepAux_readAll (src : K)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool) (hinput : tapes src = List.ofFn bits ++ suffix) :
    TM2.stepAux (readSlots src (List.ofFn id) next) state tapes =
      TM2.stepAux next (state.1, bits) (Function.update tapes src suffix) := by
  have h := stepAux_readSlots src (List.ofFn id) next state.1 bits state.2 tapes suffix
  have hin : Function.update tapes src ((List.ofFn id).map bits ++ suffix) = tapes := by
    simpa only [List.map_ofFn, Function.comp_id, ← hinput] using
      Function.update_eq_self src tapes
  rw [hin, fill_all] at h
  exact h

omit [DecidableEq K] in
theorem statementPushBound_readSlots (src : K) (slots : List (Fin N))
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)) :
    Runtime.statementPushBound (readSlots src slots next) =
      Runtime.statementPushBound next := by
  induction slots with
  | nil => rfl
  | cons i slots ih => exact ih

def writeSlots {M : Nat} (dst : K) (emit : σ → Buffer M) : List (Fin M) →
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | [], next => next
  | i :: slots, next => .push dst (fun state => emit state i) (writeSlots dst emit slots next)

theorem stepAux_writeSlots {M : Nat} (dst : K) (emit : σ → Buffer M)
    (slots : List (Fin M)) (next : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (writeSlots dst emit slots next) state tapes =
      TM2.stepAux next state
        (Function.update tapes dst ((slots.map (emit state)).reverse ++ tapes dst)) := by
  induction slots generalizing tapes with
  | nil => simp [writeSlots]
  | cons i slots ih =>
      simp only [writeSlots, TM2.stepAux]
      rw [ih]
      simp only [Function.update_self, Function.update_idem, List.map_cons,
        List.reverse_cons, List.append_assoc, List.singleton_append]

omit [DecidableEq K] in
theorem statementPushBound_writeSlots {M : Nat} (dst : K) (emit : σ → Buffer M)
    (slots : List (Fin M)) (next : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    Runtime.statementPushBound (writeSlots dst emit slots next) =
      slots.length + Runtime.statementPushBound next := by
  induction slots with
  | nil => simp [writeSlots]
  | cons i slots ih =>
      simp only [writeSlots, Runtime.statementPushBound, ih, List.length_cons]
      omega

end Chains

section Block

variable {K Λ σ : Type} {N M : Nat}

def blockStmt (src dst : K) (F : Buffer N → Buffer M)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) :=
  readSlots src (List.ofFn id)
    (writeSlots dst (fun state => F state.2) (List.ofFn id).reverse
      (.load (fun state => (state.1, emptyBuffer N)) next))

def finishAt (exit : Option Λ) : TM2.Stmt (fun _ : K => Bool) Λ σ :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def blockMapAt (src dst : K) (F : Buffer N → Buffer M) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) :=
  blockStmt src dst F (finishAt exit)

theorem statementPushBound_blockStmt (src dst : K) (F : Buffer N → Buffer M)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)) :
    Runtime.statementPushBound (blockStmt src dst F next) =
      M + Runtime.statementPushBound next := by
  simp only [blockStmt, statementPushBound_readSlots, statementPushBound_writeSlots,
    Runtime.statementPushBound, List.length_reverse, List.length_ofFn]

theorem statementPushBound_blockMapAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ) :
    Runtime.statementPushBound (blockMapAt (σ := σ) src dst F exit) = M := by
  cases exit <;> simp [blockMapAt, statementPushBound_blockStmt, finishAt,
    Runtime.statementPushBound]

variable [DecidableEq K]

theorem stepAux_blockStmt (src dst : K) (F : Buffer N → Buffer M)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = List.ofFn bits ++ suffix) :
    TM2.stepAux (blockStmt src dst F next) state tapes =
      TM2.stepAux next (state.1, emptyBuffer N)
        (Function.update (Function.update tapes src suffix) dst
          (List.ofFn (F bits) ++ tapes dst)) := by
  unfold blockStmt
  rw [stepAux_readAll src _ state bits tapes suffix hinput, stepAux_writeSlots]
  simp only [List.map_reverse, List.map_ofFn, Function.comp_id, List.reverse_reverse,
    Function.update_of_ne (Ne.symm hne), TM2.stepAux]

theorem stepAux_blockMapAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ) (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = List.ofFn bits ++ suffix) :
    TM2.stepAux (blockMapAt src dst F exit) state tapes =
      { l := exit, var := (state.1, emptyBuffer N),
        stk := Function.update (Function.update tapes src suffix) dst
          (List.ofFn (F bits) ++ tapes dst) } := by
  rw [blockMapAt, stepAux_blockStmt src dst F _ hne bits suffix state tapes hinput]
  cases exit <;> rfl

theorem step_blockMapAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (label : Λ) (hprogram : program label = blockMapAt src dst F exit)
    (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = List.ofFn bits ++ suffix) :
    TM2.step program { l := some label, var := state, stk := tapes } =
      some { l := exit
             var := (state.1, emptyBuffer N)
             stk := Function.update (Function.update tapes src suffix) dst
               (List.ofFn (F bits) ++ tapes dst) } := by
  simp only [TM2.step, hprogram,
    stepAux_blockMapAt src dst F exit hne bits suffix state tapes hinput]

end Block

def machine {N M : Nat} (F : Buffer N → Buffer M) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Unit × Buffer N
  initialState := ((), emptyBuffer N)
  m _ := blockMapAt false true F none

theorem machine_statementPushBound {N M : Nat} (F : Buffer N → Buffer M) :
    Runtime.statementPushBound ((machine F).m ()) = M :=
  statementPushBound_blockMapAt false true F none

end MinUncutGames.Foundations.Complexity.MachineFixedBlockMap

end
section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.Lookup

open Turing
open MinUncutGames.Foundations.Complexity
open MachineComposition GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def skipBits (source : K) : Nat →
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) →
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | 0, next => .load (fun state => (state.1, none)) next
  | count + 1, next =>
      let rest := skipBits source count next
      .pop source (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.pop source (fun state _ => (state.1, none)) rest)
          (.load (fun state => (state.1, none)) rest))

theorem stepAux_skipBits (source : K) (bits : List Bool)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (skipBits source bits.length next) (ambient, register)
        (Function.update base source (encodeWords (bits.map bitWord) ++ suffix)) =
      TM2.stepAux next (ambient, none) (Function.update base source suffix) := by
  induction bits generalizing register with
  | nil => simp [skipBits, encodeWords, TM2.stepAux]
  | cons bit bits ih =>
    cases bit <;>
      simpa only [List.length_cons, skipBits, List.map_cons, bitWord, Bool.false_eq_true,
        ite_false, ite_true, encodeWords, encodeWord, List.replicate_zero,
        List.replicate_succ, List.nil_append, List.cons_append, List.singleton_append,
        TM2.stepAux, Function.update_self, List.head?_cons, List.tail_cons,
        Option.getD_some, Bool.cond_false, Bool.cond_true, Function.update_idem] using
          ih none

theorem stepAux_skipBits_fromTapes (source : K) (bits : List Bool)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (base : K → List Bool) (suffix : List Bool)
    (hinput : base source = encodeWords (bits.map bitWord) ++ suffix)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (skipBits source bits.length next) (ambient, register) base =
      TM2.stepAux next (ambient, none) (Function.update base source suffix) := by
  have h := stepAux_skipBits source bits next base suffix ambient register
  have hbase : Function.update base source (encodeWords (bits.map bitWord) ++ suffix) =
      base := by rw [← hinput]; exact Function.update_eq_self source base
  rw [hbase] at h
  exact h

omit [DecidableEq K] in
theorem skipBits_pushBound (source : K) (count : Nat)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)) :
    Runtime.statementPushBound (skipBits source count next) =
      Runtime.statementPushBound next := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [skipBits, Runtime.statementPushBound, ih, max_self]

inductive Label
  | guard | skipTail | skipReverse | skipPredicate | select | copy
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.guard, .skipTail, .skipReverse, .skipPredicate,
  .select, .copy]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def statement (q : Nat) (counter source destination : K) (labels : Label → Λ)
    (exit : Option Λ) : Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .guard => MachineUnaryCounter.guard counter (labels .skipTail) (labels .select)
  | .skipTail => MachineLookup.discard source (labels .skipTail) (labels .skipReverse)
  | .skipReverse => MachineLookup.discard source (labels .skipReverse) (labels .skipPredicate)
  | .skipPredicate => skipBits source (q * q) (.goto fun _ => labels .guard)
  | .select => Hastad.SourceMachine.fieldStart destination (labels .copy)
  | .copy => Hastad.SourceMachine.fieldLoop source destination (labels .copy) exit

def program (q : Nat) (counter source destination : K) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool) :=
  statement q counter source destination id none

def rowBits {q n m : Nat} (row : DartRow q n m) : List Bool := encodeWords (rowWords row)

theorem rowBits_eq {q n m : Nat} (row : DartRow q n m) :
    rowBits row = encodeWord row.tail.val ++
      (encodeWord row.reverseIndex.val ++ encodeWords (relationWords row.relation)) := by
  simp [rowBits, rowWords, encodeWords]

def rowsBits {q n m : Nat} (rows : List (DartRow q n m)) : List Bool :=
  encodeWords (rows.flatMap rowWords)

@[simp] theorem rowsBits_nil {q n m : Nat} : rowsBits ([] : List (DartRow q n m)) = [] := rfl

@[simp] theorem rowsBits_cons {q n m : Nat} (row : DartRow q n m)
    (rows : List (DartRow q n m)) : rowsBits (row :: rows) = rowBits row ++ rowsBits rows := by
  simp only [rowsBits, List.flatMap_cons, encodeWords_append, rowBits]

def skipCost {q n m : Nat} (row : DartRow q n m) : Nat :=
  row.tail.val + row.reverseIndex.val + 4

def prefixCost {q n m : Nat} (rows : List (DartRow q n m)) : Nat :=
  (rows.map skipCost).sum

def lookupCost {q n m : Nat} (prior : List (DartRow q n m)) (row : DartRow q n m) : Nat :=
  prefixCost prior + row.tail.val + 3

section Ambient

variable {q n m : Nat} (counter source destination : K) (labels : Label → Λ)
  (exit : Option Λ)
  (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
  (atStatement : ∀ label, P (labels label) = statement q counter source destination labels exit label)

include atStatement

theorem skipRowTrace (base : K → List Bool) (row : DartRow q n m) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[row.tail.val + row.reverseIndex.val + 3]
      (some ⟨some (labels .skipTail), (ambient, register),
        Function.update base source (rowBits row ++ suffix)⟩) =
      some ⟨some (labels .guard), (ambient, none), Function.update base source suffix⟩ := by
  have ht := MachineLookup.discardTrace_update source (labels .skipTail) (labels .skipReverse)
    P (atStatement .skipTail) base row.tail.val
    (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
    ambient register
  have hr := MachineLookup.discardTrace_update source (labels .skipReverse) (labels .skipPredicate)
    P (atStatement .skipReverse) base row.reverseIndex.val
    (encodeWords (relationWords row.relation) ++ suffix) ambient none
  have hp : TM2.step P
      ⟨some (labels .skipPredicate), (ambient, none), Function.update base source
        (encodeWords (relationWords row.relation) ++ suffix)⟩ =
      some ⟨some (labels .guard), (ambient, none), Function.update base source suffix⟩ := by
    change some (TM2.stepAux (P (labels .skipPredicate)) _ _) = _
    rw [atStatement .skipPredicate]
    have h := congrArg some (stepAux_skipBits source row.relation.toList
      (.goto fun _ => labels .guard) base suffix ambient none)
    simpa only [statement, Vector.length_toList, relationWords, TM2.stepAux] using h
  rw [rowBits_eq]
  simp only [List.append_assoc]
  rw [show row.tail.val + row.reverseIndex.val + 3 =
    1 + ((row.reverseIndex.val + 1) + (row.tail.val + 1)) by omega,
    Function.iterate_add_apply, Function.iterate_add_apply, ht, hr,
    Function.iterate_one, advance_some, hp]

theorem skipRowTrace_fromTapes (base : K → List Bool) (row : DartRow q n m)
    (suffix : List Bool) (hinput : base source = rowBits row ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[row.tail.val + row.reverseIndex.val + 3]
      (some ⟨some (labels .skipTail), (ambient, register), base⟩) =
      some ⟨some (labels .guard), (ambient, none), Function.update base source suffix⟩ := by
  have h := skipRowTrace counter source destination labels exit P atStatement
    base row suffix ambient register
  have hb : Function.update base source (rowBits row ++ suffix) = base := by
    rw [← hinput]
    exact Function.update_eq_self source base
  rw [hb] at h
  exact h

theorem selectTrace (hsd : source ≠ destination) (base : K → List Bool)
    (row : DartRow q n m) (suffix : List Bool)
    (hinput : base source = rowBits row ++ suffix) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[row.tail.val + 2]
      (some ⟨some (labels .select), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), Hastad.SourceMachine.fieldTapes source destination base
        (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
        (encodeWord row.tail.val ++ base destination)⟩ := by
  let ht := Hastad.SourceMachine.fieldInTime source destination hsd
    (labels .select) (labels .copy) exit P (atStatement .select) (atStatement .copy)
    base row.tail.val
    (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
    (by simpa only [rowBits_eq, List.append_assoc] using hinput) ambient register
  have hsteps : ht.steps = row.tail.val + 2 := rfl
  have htrace := ht.evals_in_steps
  rw [hsteps] at htrace
  exact htrace

theorem lookupTailTrace
    (hcs : counter ≠ source) (hcd : counter ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (prior : List (DartRow q n m)) (row : DartRow q n m)
    (counterSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[lookupCost prior row]
      (some ⟨some (labels .guard), (ambient, register),
        MachineLookup.tapes counter source destination base
          (encodeWord prior.length ++ counterSuffix)
          (rowsBits prior ++ (rowBits row ++ suffix)) output⟩) =
      some ⟨exit, (ambient, none),
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix)
          (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
          (encodeWord row.tail.val ++ output)⟩ := by
  induction prior generalizing register with
  | nil =>
    simp only [lookupCost, prefixCost, List.map_nil, List.sum_nil, Nat.zero_add,
      List.length_nil, rowsBits_nil, List.nil_append]
    rw [show row.tail.val + 3 = (row.tail.val + 2) + 1 by omega,
      Function.iterate_succ_apply]
    have hg := MachineUnaryCounter.guardStep_zero counter (labels .guard)
      (labels .skipTail) (labels .select) P (atStatement .guard)
      (MachineLookup.tapes counter source destination base
        (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output)
      counterSuffix ambient register
    have hcounter : MachineUnaryCounter.counterTapes counter
        (MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output) 0 counterSuffix =
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output := by
      simp only [MachineUnaryCounter.counterTapes, MachineLookup.update_index _ _ _ hcs hcd]
    rw [hcounter] at hg
    simp only [advance_some]
    rw [hg]
    have hs := selectTrace counter source destination labels exit P atStatement hsd
      (MachineLookup.tapes counter source destination base
        (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output)
      row suffix (by simp [hsd]) ambient none
    simpa only [MachineLookup.tapes_destination,
      MachineLookup.fieldTapes_eq _ _ _ hsd] using hs
  | cons first prior ih =>
    simp only [lookupCost, prefixCost, List.map_cons, List.sum_cons, List.length_cons,
      rowsBits_cons, List.append_assoc]
    rw [show skipCost first + (prior.map skipCost).sum + row.tail.val + 3 =
      ((prior.map skipCost).sum + row.tail.val + 3) +
        (first.tail.val + first.reverseIndex.val + 3) + 1 by simp only [skipCost]; omega,
      Function.iterate_succ_apply]
    have hg := MachineUnaryCounter.guardStep_succ counter (labels .guard)
      (labels .skipTail) (labels .select) P (atStatement .guard)
      (MachineLookup.tapes counter source destination base
        (encodeWord prior.length ++ counterSuffix)
        (rowBits first ++ (rowsBits prior ++ (rowBits row ++ suffix))) output)
      prior.length counterSuffix ambient register
    simp only [MachineUnaryCounter.counterTapes,
      MachineLookup.update_index _ _ _ hcs hcd] at hg
    simp only [advance_some]
    rw [hg, Function.iterate_add_apply]
    have hs := skipRowTrace_fromTapes counter source destination labels exit P atStatement
      (MachineLookup.tapes counter source destination base
        (encodeWord prior.length ++ counterSuffix)
        (rowBits first ++ (rowsBits prior ++ (rowBits row ++ suffix))) output)
      first (rowsBits prior ++ (rowBits row ++ suffix)) (by simp [hsd]) ambient none
    rw [hs]
    simp only [MachineLookup.update_source _ _ _ hsd]
    exact ih none

end Ambient

theorem lookupCost_le {q n m : Nat} (prior : List (DartRow q n m)) (row : DartRow q n m) :
    lookupCost prior row ≤ (rowsBits prior ++ rowBits row).length +
      2 * (encodeWord prior.length).length + 1 := by
  have hp : prefixCost prior ≤ (rowsBits prior).length + 2 * prior.length := by
    induction prior with
    | nil => simp [prefixCost]
    | cons first prior ih =>
      have hb : skipCost first ≤ (rowBits first).length + 2 := by
        simp only [skipCost, rowBits_eq, List.length_append, encodeWord_length]
        omega
      simp only [prefixCost, List.map_cons, List.sum_cons, rowsBits_cons,
        List.length_append, List.length_cons] at *
      omega
  have hr : row.tail.val + 1 ≤ (rowBits row).length := by
    simp only [rowBits_eq, List.length_append, encodeWord_length]
    omega
  simp only [lookupCost, List.length_append, encodeWord_length]
  omega

def lookupTailInTime {q n m : Nat}
    (counter source destination : K) (labels : Label → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStatement : ∀ label, P (labels label) = statement q counter source destination labels exit label)
    (hcs : counter ≠ source) (hcd : counter ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (prior : List (DartRow q n m)) (row : DartRow q n m)
    (counterSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (labels .guard), (ambient, register),
        MachineLookup.tapes counter source destination base
          (encodeWord prior.length ++ counterSuffix)
          (rowsBits prior ++ (rowBits row ++ suffix)) output⟩
      (some ⟨exit, (ambient, none),
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix)
          (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
          (encodeWord row.tail.val ++ output)⟩)
      ((rowsBits prior ++ rowBits row).length + 2 * (encodeWord prior.length).length + 1) where
  steps := lookupCost prior row
  evals_in_steps := lookupTailTrace counter source destination labels exit P atStatement
    hcs hcd hsd base prior row counterSuffix suffix output ambient register
  steps_le_m := lookupCost_le prior row

theorem tableTailTrace {q : Nat}
    (counter source destination : K) (labels : Label → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStatement : ∀ label, P (labels label) = statement q counter source destination labels exit label)
    (hcs : counter ≠ source) (hcd : counter ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (table : Table q) (e : Fin table.darts)
    (counterSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[lookupCost ((rowList table).take e.val) table.rows[e]]
      (some ⟨some (labels .guard), (ambient, register),
        MachineLookup.tapes counter source destination base
          (encodeWord e.val ++ counterSuffix) (rowsBits (rowList table) ++ suffix) output⟩) =
      some ⟨exit, (ambient, none),
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix)
          (encodeWord table.rows[e].reverseIndex.val ++
            (encodeWords (relationWords table.rows[e].relation) ++
              (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix)))
          (encodeWord table.rows[e].tail.val ++ output)⟩ := by
  have h := lookupTailTrace counter source destination labels exit P atStatement
    hcs hcd hsd base ((rowList table).take e.val) table.rows[e] counterSuffix
    (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix) output ambient register
  have hlength : ((rowList table).take e.val).length = e.val := by
    simp only [List.length_take, rowList_length, Nat.min_eq_left (Nat.le_of_lt e.isLt)]
  have hsplit : rowsBits (rowList table) ++ suffix =
      rowsBits ((rowList table).take e.val) ++
        (rowBits table.rows[e] ++ (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix)) := by
    have hrow : table.rows[e.val] = table.rows[e] := rfl
    simpa only [rowsBits, rowBits, rowList, Vector.getElem_toList, hrow] using
      Input.rowsBits_append_split (rowList table) e.val (by simp) suffix
  rw [hlength, ← hsplit] at h
  exact h

theorem fullTableTailTrace {q : Nat}
    (counter source destination : K) (labels : Label → Λ) (exit : Option Λ)
    (headerVertices headerDarts : Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStatement : ∀ label, P (labels label) = statement q counter source destination labels exit label)
    (atVertices : P headerVertices = MachineLookup.discard source headerVertices headerDarts)
    (atDarts : P headerDarts = MachineLookup.discard source headerDarts (labels .guard))
    (hcs : counter ≠ source) (hcd : counter ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (table : Table q) (e : Fin table.darts)
    (counterSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[lookupCost ((rowList table).take e.val) table.rows[e] +
        (table.darts + 1) + (table.vertices + 1)]
      (some ⟨some headerVertices, (ambient, register),
        MachineLookup.tapes counter source destination base
          (encodeWord e.val ++ counterSuffix) (tableBits table ++ suffix) output⟩) =
      some ⟨exit, (ambient, none),
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix)
          (encodeWord table.rows[e].reverseIndex.val ++
            (encodeWords (relationWords table.rows[e].relation) ++
              (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix)))
          (encodeWord table.rows[e].tail.val ++ output)⟩ := by
  have hv := MachineLookup.discardTrace source headerVertices headerDarts P atVertices
    (MachineLookup.tapes counter source destination base
      (encodeWord e.val ++ counterSuffix) (tableBits table ++ suffix) output)
    table.vertices (encodeWord table.darts ++ (rowsBits (rowList table) ++ suffix))
    (by simp only [MachineLookup.tapes_source _ _ _ hsd, Input.tableBits_header,
      rowsBits, List.append_assoc]) ambient register
  rw [Function.iterate_add_apply, hv]
  simp only [MachineLookup.update_source _ _ _ hsd]
  have hd := MachineLookup.discardTrace source headerDarts (labels .guard) P atDarts
    (MachineLookup.tapes counter source destination base
      (encodeWord e.val ++ counterSuffix)
      (encodeWord table.darts ++ (rowsBits (rowList table) ++ suffix)) output)
    table.darts (rowsBits (rowList table) ++ suffix) (by simp [hsd]) ambient none
  rw [Function.iterate_add_apply, hd]
  simp only [MachineLookup.update_source _ _ _ hsd]
  exact tableTailTrace counter source destination labels exit P atStatement hcs hcd hsd
    base table e counterSuffix suffix output ambient none

theorem lookup_frame (counter source destination other : K)
    (hc : other ≠ counter) (hs : other ≠ source) (hd : other ≠ destination)
    (base : K → List Bool) (counterBits input output : List Bool) :
    MachineLookup.tapes counter source destination base counterBits input output other = base other :=
  MachineLookup.tapes_other counter source destination other hc hs hd base counterBits input output

def tableTailCost {q : Nat} (table : Table q) (e : Fin table.darts) : Nat :=
  lookupCost ((rowList table).take e.val) table.rows[e] +
    (table.darts + 1) + (table.vertices + 1)

theorem tableTailCost_le {q : Nat} (table : Table q) (e : Fin table.darts) :
    tableTailCost table e ≤ (tableBits table).length + 2 * (encodeWord e.val).length + 1 := by
  have htake : ((rowList table).take e.val).length = e.val := by
    simp only [List.length_take, rowList_length, Nat.min_eq_left (Nat.le_of_lt e.isLt)]
  have hrow : table.rows[e.val] = table.rows[e] := rfl
  have hsplit : rowsBits (rowList table) = rowsBits ((rowList table).take e.val) ++
      (rowBits table.rows[e] ++ rowsBits ((rowList table).drop (e.val + 1))) := by
    simpa only [rowsBits, rowBits, rowList, Vector.getElem_toList, hrow] using
      Input.rowsBits_split (rowList table) e.val (by simp)
  have hp : (rowsBits ((rowList table).take e.val) ++ rowBits table.rows[e]).length ≤
      (rowsBits (rowList table)).length := by
    rw [hsplit]
    simp only [List.length_append]
    omega
  have hb := lookupCost_le ((rowList table).take e.val) table.rows[e]
  rw [htake] at hb
  have hh := congrArg List.length (Input.tableBits_header table)
  change (tableBits table).length =
    (encodeWord table.vertices ++ (encodeWord table.darts ++ rowsBits (rowList table))).length at hh
  simp only [List.length_append, encodeWord_length] at hh
  unfold tableTailCost
  omega

def headIndex {q : Nat} (table : Table q) (e : Fin table.darts) : Fin table.darts :=
  table.rows[e].reverseIndex

def headValue {q : Nat} (table : Table q) (e : Fin table.darts) : Nat :=
  table.rows[headIndex table e].tail.val

theorem headValue_eq_semantics {q : Nat} (table : Table q) (e : Fin table.darts) :
    headValue table e = ((semantics table).head e).val := rfl

abbrev HeadTapes (K : Type) := Fin 6 → K

def headLookupTapes {q : Nat} (tape : HeadTapes K) (base : K → List Bool)
    (table : Table q) (e : Fin table.darts) : K → List Bool :=
  MachineLookup.tapes (tape 3) (tape 2) (tape 4) base
    (encodeWord 0 ++ base (tape 3))
    (encodeWord table.rows[headIndex table e].reverseIndex.val ++
      (encodeWords (relationWords table.rows[headIndex table e].relation) ++
        (rowsBits ((rowList table).drop ((headIndex table e).val + 1)) ++ base (tape 2))))
    (encodeWord (headValue table e))

def headLookupCost {q : Nat} (table : Table q) (e : Fin table.darts) : Nat :=
  2 * ((tableBits table).length + 1) +
    2 * ((encodeWord (headIndex table e).val).length + 1) + tableTailCost table (headIndex table e)

theorem headLookupCost_le {q : Nat} (table : Table q) (e : Fin table.darts) :
    headLookupCost table e ≤ 7 * (tableBits table).length + 5 := by
  have hi : (encodeWord (headIndex table e).val).length ≤ (tableBits table).length := by
    rw [encodeWord_length]
    exact (Nat.succ_le_of_lt (headIndex table e).isLt).trans (darts_le_tableBits_length table)
  have hl := tableTailCost_le table (headIndex table e)
  unfold headLookupCost
  omega

noncomputable def headTimePolynomial : Polynomial Nat :=
  Polynomial.C 7 * Polynomial.X + Polynomial.C 5

def headLookupInTime {q : Nat}
    (tape : HeadTapes K) (hinj : Function.Injective tape)
    (tableFirst tableSecond indexFirst indexSecond headerVertices headerDarts : Λ)
    (labels : Label → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atTableFirst : P tableFirst = Reduction.MachineTransfer.loopAt
      (tape 0) (tape 5) id false tableFirst (some tableSecond))
    (atTableSecond : P tableSecond = MachineCopy.forkLoop
      (tape 5) (tape 0) (tape 2) false tableSecond (some indexFirst))
    (atIndexFirst : P indexFirst = Reduction.MachineTransfer.loopAt
      (tape 1) (tape 5) id false indexFirst (some indexSecond))
    (atIndexSecond : P indexSecond = MachineCopy.forkLoop
      (tape 5) (tape 1) (tape 3) false indexSecond (some headerVertices))
    (atVertices : P headerVertices = MachineLookup.discard (tape 2) headerVertices headerDarts)
    (atDarts : P headerDarts = MachineLookup.discard (tape 2) headerDarts (labels .guard))
    (atStatement : ∀ label,
      P (labels label) = statement q (tape 3) (tape 2) (tape 4) labels exit label)
    (base : K → List Bool) (table : Table q) (e : Fin table.darts)
    (hTable : base (tape 0) = tableBits table)
    (hReverse : base (tape 1) = encodeWord (headIndex table e).val)
    (hHead : base (tape 4) = []) (hScratch : base (tape 5) = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some tableFirst, (ambient, register), base⟩
      (some ⟨exit, (ambient, none), headLookupTapes tape base table e⟩)
      (headTimePolynomial.eval (tableBits table).length) := by
  have hne (i j : Fin 6) (h : i ≠ j) : tape i ≠ tape j := fun heq => h (hinj heq)
  let t₁ := Function.update base (tape 2) (tableBits table ++ base (tape 2))
  let t₂ := Function.update t₁ (tape 3) (encodeWord (headIndex table e).val ++ base (tape 3))
  have run₁ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some tableFirst, (ambient, register), base⟩
      (some ⟨some indexFirst, (ambient, none), t₁⟩)
      (2 * ((tableBits table).length + 1)) := by
    simpa only [hTable, t₁] using MachineCopy.copyInTime (tape 0) (tape 2) (tape 5)
      (hne 0 2 (by decide)) (hne 0 5 (by decide)) (hne 2 5 (by decide)) false
      tableFirst tableSecond (some indexFirst) P atTableFirst atTableSecond
      base hScratch ambient register
  have hsrc : t₁ (tape 1) = encodeWord (headIndex table e).val := by
    simp only [t₁, Function.update_of_ne (hne 1 2 (by decide)), hReverse]
  have hdst : t₁ (tape 3) = base (tape 3) := by
    simp only [t₁, Function.update_of_ne (hne 3 2 (by decide))]
  have hscratch₁ : t₁ (tape 5) = [] := by
    simp only [t₁, Function.update_of_ne (hne 5 2 (by decide)), hScratch]
  have run₂ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some indexFirst, (ambient, none), t₁⟩
      (some ⟨some headerVertices, (ambient, none), t₂⟩)
      (2 * ((encodeWord (headIndex table e).val).length + 1)) := by
    simpa only [hsrc, hdst, t₂] using MachineCopy.copyInTime (tape 1) (tape 3) (tape 5)
      (hne 1 3 (by decide)) (hne 1 5 (by decide)) (hne 3 5 (by decide)) false
      indexFirst indexSecond (some headerVertices) P atIndexFirst atIndexSecond
      t₁ hscratch₁ ambient none
  have ht₂ : t₂ = MachineLookup.tapes (tape 3) (tape 2) (tape 4) base
      (encodeWord (headIndex table e).val ++ base (tape 3))
      (tableBits table ++ base (tape 2)) [] := by
    funext k
    by_cases hi : k = tape 3
    · subst k
      simp [t₂, MachineLookup.tapes, hne 3 2 (by decide), hne 3 4 (by decide)]
    · by_cases hs : k = tape 2
      · subst k
        simp [t₂, t₁, MachineLookup.tapes, hne 2 3 (by decide), hne 2 4 (by decide)]
      · by_cases hh : k = tape 4
        · subst k
          simp [t₂, t₁, MachineLookup.tapes, hne 4 3 (by decide),
            hne 4 2 (by decide), hHead]
        · simp [t₂, t₁, MachineLookup.tapes, hi, hs, hh]
  let run₃ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some headerVertices, (ambient, none), t₂⟩
      (some ⟨exit, (ambient, none), headLookupTapes tape base table e⟩)
      (tableTailCost table (headIndex table e)) := {
    steps := tableTailCost table (headIndex table e)
    evals_in_steps := by
      change (advance (TM2.step P))^[tableTailCost table (headIndex table e)]
        (some ⟨some headerVertices, (ambient, none), t₂⟩) =
          some ⟨exit, (ambient, none), headLookupTapes tape base table e⟩
      rw [ht₂]
      simpa only [headLookupTapes, headValue, tableTailCost, List.append_nil] using
        fullTableTailTrace (tape 3) (tape 2) (tape 4) labels exit
          headerVertices headerDarts P atStatement atVertices atDarts
          (hne 3 2 (by decide)) (hne 3 4 (by decide)) (hne 2 4 (by decide))
          base table (headIndex table e) (base (tape 3)) (base (tape 2)) [] ambient none
    steps_le_m := Nat.le_refl _ }
  let run₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁₂ run₃
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have ht := run.steps_le_m
  have hb := headLookupCost_le table e
  simp only [headTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  unfold headLookupCost at hb
  omega

theorem headLookupTapes_head {q : Nat} (tape : HeadTapes K) (base : K → List Bool)
    (table : Table q) (e : Fin table.darts) :
    headLookupTapes tape base table e (tape 4) = encodeWord (headValue table e) := by
  simp [headLookupTapes]

theorem headLookupTapes_frame {q : Nat} (tape : HeadTapes K) (base : K → List Bool)
    (table : Table q) (e : Fin table.darts) (other : K)
    (hc : other ≠ tape 3) (hs : other ≠ tape 2) (hh : other ≠ tape 4) :
    headLookupTapes tape base table e other = base other :=
  lookup_frame (tape 3) (tape 2) (tape 4) other hc hs hh base _ _ _

def readRowTapes {q n m : Nat} (source tail reverse : K) (base : K → List Bool)
    (row : DartRow q n m) (suffix : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base source suffix)
    tail (encodeWord row.tail.val)) reverse (encodeWord row.reverseIndex.val)

theorem readRowTapes_source {q n m : Nat} (source tail reverse : K)
    (hst : source ≠ tail) (hsr : source ≠ reverse)
    (base : K → List Bool) (row : DartRow q n m) (suffix : List Bool) :
    readRowTapes source tail reverse base row suffix source = suffix := by
  simp [readRowTapes, hst, hsr]

theorem readRowTapes_tail {q n m : Nat} (source tail reverse : K)
    (htr : tail ≠ reverse) (base : K → List Bool)
    (row : DartRow q n m) (suffix : List Bool) :
    readRowTapes source tail reverse base row suffix tail = encodeWord row.tail.val := by
  simp [readRowTapes, htr]

theorem readRowTapes_reverse {q n m : Nat} (source tail reverse : K)
    (base : K → List Bool) (row : DartRow q n m) (suffix : List Bool) :
    readRowTapes source tail reverse base row suffix reverse =
      encodeWord row.reverseIndex.val := by
  simp [readRowTapes]

theorem readRowTapes_frame {q n m : Nat} (source tail reverse other : K)
    (hs : other ≠ source) (ht : other ≠ tail) (hr : other ≠ reverse)
    (base : K → List Bool) (row : DartRow q n m) (suffix : List Bool) :
    readRowTapes source tail reverse base row suffix other = base other := by
  simp [readRowTapes, hs, ht, hr]

def readRowCost {q n m : Nat} (row : DartRow q n m) : Nat :=
  row.tail.val + row.reverseIndex.val + 5

theorem readRowCost_le {q n m : Nat} (row : DartRow q n m) :
    readRowCost row ≤ (rowBits row).length + 3 := by
  rw [rowBits_eq]
  simp only [List.length_append, encodeWord_length]
  unfold readRowCost
  omega

theorem readRowCost_table_le {q : Nat} (table : Table q) (e : Fin table.darts) :
    readRowCost table.rows[e] ≤ 2 * (tableBits table).length + 5 := by
  have ht := (Nat.le_of_lt table.rows[e].tail.isLt).trans
    (vertices_le_tableBits_length table)
  have hr := (Nat.le_of_lt table.rows[e].reverseIndex.isLt).trans
    (darts_le_tableBits_length table)
  unfold readRowCost
  omega

def readRowInTime {q n m : Nat} (source tail reverse : K)
    (hst : source ≠ tail) (hsr : source ≠ reverse) (htr : tail ≠ reverse)
    (tailStart tailLoop reverseStart reverseLoop readLabel exitLabel : Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (ReadRelation.State σ q))
    (atTailStart : P tailStart = Hastad.SourceMachine.fieldStart tail tailLoop)
    (atTailLoop : P tailLoop =
      Hastad.SourceMachine.fieldLoop source tail tailLoop (some reverseStart))
    (atReverseStart : P reverseStart = Hastad.SourceMachine.fieldStart reverse reverseLoop)
    (atReverseLoop : P reverseLoop =
      Hastad.SourceMachine.fieldLoop source reverse reverseLoop (some readLabel))
    (atRead : P readLabel = ReadRelation.parser source exitLabel)
    (base : K → List Bool) (row : DartRow q n m) (suffix : List Bool)
    (hinput : base source = rowBits row ++ suffix)
    (hTail : base tail = []) (hReverse : base reverse = [])
    (ambient : σ) (initial : RelationTable q) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some tailStart, ((ambient, initial), register), base⟩
      (some ⟨some exitLabel, ((ambient, row.relation), none),
        readRowTapes source tail reverse base row suffix⟩)
      (readRowCost row) := by
  let relationInput := encodeWords (relationWords row.relation) ++ suffix
  let reverseInput := encodeWord row.reverseIndex.val ++ relationInput
  let t₁ := Hastad.SourceMachine.fieldTapes source tail base reverseInput
    (encodeWord row.tail.val)
  let t₂ := Hastad.SourceMachine.fieldTapes source reverse t₁ relationInput
    (encodeWord row.reverseIndex.val)
  have hinput₁ : base source = encodeWord row.tail.val ++ reverseInput := by
    simpa only [rowBits_eq, List.append_assoc, reverseInput, relationInput] using hinput
  have run₁ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some tailStart, ((ambient, initial), register), base⟩
      (some ⟨some reverseStart, ((ambient, initial), none), t₁⟩)
      (row.tail.val + 2) := by
    simpa only [hTail, List.append_nil, t₁] using
      Hastad.SourceMachine.fieldInTime source tail hst tailStart tailLoop
        (some reverseStart) P atTailStart atTailLoop base row.tail.val reverseInput
        hinput₁ (ambient, initial) register
  have hinput₂ : t₁ source = encodeWord row.reverseIndex.val ++ relationInput := by
    simp only [t₁, Hastad.SourceMachine.fieldTapes_source source tail hst, reverseInput]
  have hreverse₁ : t₁ reverse = [] := by
    simp [t₁, Hastad.SourceMachine.fieldTapes, Ne.symm hsr, Ne.symm htr, hReverse]
  have run₂ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some reverseStart, ((ambient, initial), none), t₁⟩
      (some ⟨some readLabel, ((ambient, initial), none), t₂⟩)
      (row.reverseIndex.val + 2) := by
    simpa only [hreverse₁, List.append_nil, t₂] using
      Hastad.SourceMachine.fieldInTime source reverse hsr reverseStart reverseLoop
        (some readLabel) P atReverseStart atReverseLoop t₁ row.reverseIndex.val relationInput
        hinput₂ (ambient, initial) none
  have hinput₃ : t₂ source = encodeWords (relationWords row.relation) ++ suffix := by
    simp only [t₂, Hastad.SourceMachine.fieldTapes_source source reverse hsr, relationInput]
  have hrestore : Function.update t₂ source
      (encodeWords (relationWords row.relation) ++ suffix) = t₂ := by
    rw [← hinput₃]
    exact Function.update_eq_self source t₂
  have hfinal : Function.update t₂ source suffix =
      readRowTapes source tail reverse base row suffix := by
    funext k
    by_cases hs : k = source
    · subst k
      simp [readRowTapes, hst, hsr]
    · by_cases ht : k = tail
      · subst k
        simp [t₂, t₁, Hastad.SourceMachine.fieldTapes, readRowTapes, hs, htr]
      · by_cases hr : k = reverse
        · subst k
          simp [t₂, Hastad.SourceMachine.fieldTapes, readRowTapes, hs]
        · simp [t₂, t₁, Hastad.SourceMachine.fieldTapes, readRowTapes, hs, ht, hr]
  have run₃ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some readLabel, ((ambient, initial), none), t₂⟩
      (some ⟨some exitLabel, ((ambient, row.relation), none),
        readRowTapes source tail reverse base row suffix⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change (advance (TM2.step P))^[1] _ = _
      simpa only [hrestore, hfinal] using ReadRelation.parserTrace source readLabel exitLabel
        P atRead t₂ row.relation suffix ambient initial none
    steps_le_m := Nat.le_refl _ }
  let run₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁₂ run₃
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have ht := run.steps_le_m
  unfold readRowCost
  omega

def machine (q : Nat) : FinTM2 where
  K := Fin 3
  k₀ := 1
  k₁ := 2
  Γ _ := Bool
  Λ := Label
  main := .guard
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program q 0 1 2

end MinUncutGames.Foundations.PCP.AlphabetTable.Lookup

end

end OAI
