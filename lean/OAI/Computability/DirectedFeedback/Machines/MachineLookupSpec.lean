import Mathlib
import OAI.Computability.DirectedFeedback.Games.Product

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineLookupSpec

def skipWord : List Bool → List Bool
  | [] => []
  | true :: bs => skipWord bs
  | false :: bs => bs

@[simp] theorem skipWord_encodeWord (n : Nat) (bs : List Bool) :
    skipWord (encodeWord n ++ bs) = bs := by
  induction n with
  | zero => simp [encodeWord, skipWord]
  | succ n ih =>
    simpa [encodeWord, List.replicate_succ, skipWord] using ih

theorem skipWord_iterate_encodeWords (i : Nat) (values : List Nat) :
    (skipWord^[i]) (encodeWords values) = encodeWords (values.drop i) := by
  induction i generalizing values with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    cases values with
    | nil => simpa [encodeWords, skipWord] using ih []
    | cons n ns =>
      simpa only [encodeWords, skipWord_encodeWord, List.drop_succ_cons] using ih ns

def headWord : List Bool → Option (List Bool)
  | [] => none
  | false :: _ => some [false]
  | true :: bs => (headWord bs).map (true :: ·)

@[simp] theorem headWord_encodeWord (n : Nat) (bs : List Bool) :
    headWord (encodeWord n ++ bs) = some (encodeWord n) := by
  induction n with
  | zero => simp [encodeWord, headWord]
  | succ n ih =>
    simpa [encodeWord, List.replicate_succ, headWord] using
      congrArg (Option.map (true :: ·)) ih

@[simp] theorem headWord_encodeWords (values : List Nat) :
    headWord (encodeWords values) = values.head?.map encodeWord := by
  cases values with
  | nil => rfl
  | cons n ns => exact headWord_encodeWord n (encodeWords ns)

def lookupBits (i : Nat) (table : List Bool) : Option (List Bool) :=
  headWord ((skipWord^[i]) table)

@[simp] theorem lookupBits_encodeWords (i : Nat) (values : List Nat) :
    lookupBits i (encodeWords values) = values[i]?.map encodeWord := by
  rw [lookupBits, skipWord_iterate_encodeWords, headWord_encodeWords,
    List.head?_drop]

def lookupEncoded (index table : List Bool) : Option (List Bool) :=
  match decodeWords index with
  | some [i] => lookupBits i table
  | _ => none

@[simp] theorem decodeWords_encodeWord (i : Nat) :
    decodeWords (encodeWord i) = some [i] := by
  simpa [encodeWords] using decodeWords_encodeWords [i]

@[simp] theorem lookupEncoded_encode (i : Nat) (values : List Nat) :
    lookupEncoded (encodeWord i) (encodeWords values) =
      values[i]?.map encodeWord := by
  simp [lookupEncoded]

theorem lookupEncoded_some (i value : Nat) (values : List Nat)
    (h : values[i]? = some value) :
    lookupEncoded (encodeWord i) (encodeWords values) = some (encodeWord value) := by
  simp [h]

theorem lookupEncoded_none (i : Nat) (values : List Nat)
    (h : values.length ≤ i) :
    lookupEncoded (encodeWord i) (encodeWords values) = none := by
  simp [List.getElem?_eq_none h]

theorem encoded_selected_split (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    encodeWords values = encodeWords (values.take i) ++ encodeWord value ++
      encodeWords (values.drop (i + 1)) := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, hv⟩
  have hs : values = values.take i ++ value :: values.drop (i + 1) := by
    calc
      values = values.take i ++ values.drop i := (List.take_append_drop i values).symm
      _ = _ := by rw [List.drop_eq_getElem_cons hi, hv]
  simpa only [encodeWords_append, encodeWords, List.append_assoc] using
    congrArg encodeWords hs

def scannedBits (values : List Nat) (i : Nat) : Nat :=
  (encodeWords (values.take (i + 1))).length

theorem encoded_prefix_length_le (values : List Nat) (i : Nat) :
    (encodeWords (values.take i)).length ≤ (encodeWords values).length := by
  have hs : encodeWords (values.take i) ++ encodeWords (values.drop i) =
      encodeWords values := by
    rw [← encodeWords_append, List.take_append_drop]
  have hl := congrArg List.length hs
  simp only [List.length_append] at hl
  omega

theorem scannedBits_le (values : List Nat) (i : Nat) :
    scannedBits values i ≤ (encodeWords values).length :=
  encoded_prefix_length_le values (i + 1)

theorem scannedBits_of_some (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    scannedBits values i = (encodeWords (values.take i)).length + value + 1 := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, hv⟩
  simp [scannedBits, List.take_succ_eq_append_getElem hi, hv, encodeWords,
    Nat.add_assoc]

theorem selected_scan_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWords (values.take i)).length + value + 1 ≤
      (encodeWords values).length := by
  rw [← scannedBits_of_some values i value h]
  exact scannedBits_le values i

theorem output_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWord value).length ≤ (encodeWords values).length := by
  have hs := selected_scan_length_le values i value h
  rw [encodeWord_length]
  omega

theorem index_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWord i).length ≤ (encodeWords values).length := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, _⟩
  have hp : i ≤ (encodeWords (values.take i)).length := by
    simp only [encodeWords_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    omega
  have hs := selected_scan_length_le values i value h
  rw [encodeWord_length]
  omega

def steps : List Nat → Nat → Nat
  | [], i => 2 * i + 2
  | n :: _, 0 => n + 3
  | n :: ns, i + 1 => n + 2 + steps ns i

theorem steps_le_encoded_length_strong (values : List Nat) (i : Nat) :
    steps values i ≤ (encodeWords values).length + 2 * i + 2 := by
  induction values generalizing i with
  | nil => simp [steps, encodeWords]
  | cons n ns ih =>
    cases i with
    | zero =>
      simp only [steps, encodeWords, List.length_append, encodeWord_length]
      omega
    | succ i =>
      have ht := ih i
      simp only [steps, encodeWords, List.length_append, encodeWord_length]
      omega

theorem steps_le_encoded_length (values : List Nat) (i : Nat) :
    steps values i ≤ (encodeWords values).length + 2 * i + 3 := by
  have h := steps_le_encoded_length_strong values i
  omega

theorem steps_eq_scannedBits_of_lt (values : List Nat) (i : Nat)
    (h : i < values.length) :
    steps values i = scannedBits values i + i + 2 := by
  induction values generalizing i with
  | nil => simp at h
  | cons n ns ih =>
    cases i with
    | zero => simp [steps, scannedBits, encodeWords, Nat.add_assoc]
    | succ i =>
      have ht := ih i (by simpa using h)
      simp only [scannedBits] at ht
      simp only [steps, scannedBits, List.take_succ_cons, encodeWords,
        List.length_append, encodeWord_length]
      omega

theorem steps_eq_scannedBits_of_some (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    steps values i = scannedBits values i + i + 2 := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, _⟩
  exact steps_eq_scannedBits_of_lt values i hi

theorem steps_add_length_of_invalid (values : List Nat) (i : Nat)
    (h : values.length ≤ i) :
    steps values i + values.length = (encodeWords values).length + 2 * i + 2 := by
  induction values generalizing i with
  | nil => simp [steps, encodeWords]
  | cons n ns ih =>
    cases i with
    | zero => simp at h
    | succ i =>
      have ht := ih i (by simpa using h)
      simp only [steps, encodeWords, List.length_append, encodeWord_length,
        List.length_cons]
      omega

theorem steps_le_input_encoding_size (values : List Nat) (i : Nat) :
    steps values i ≤ (encodeWords values).length + 2 * (encodeWord i).length := by
  have h := steps_le_encoded_length_strong values i
  rw [encodeWord_length]
  omega

end DFVSGames.Foundations.Complexity.MachineLookupSpec


namespace DFVSGames.Foundations.Complexity.MachineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

private theorem discard_update_twice_inline_MachineLookupDiscard (source : K) (base : K → List Bool)
    (input replacement : List Bool) :
    Function.update (Function.update base source input) source replacement =
      Function.update base source replacement := by
  funext p
  by_cases hp : p = source
  · subst p; simp
  · simp [hp]

theorem discardStep_delimiter (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), Function.update base source (false :: suffix)⟩ =
      some ⟨some returnLabel, (ambient, none), Function.update base source suffix⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (Function.update base source (false :: suffix))) = _
  rw [atLoop]
  simp [discard, TM2.stepAux]

theorem discardStep_true (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (input : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), Function.update base source (true :: input)⟩ =
      some ⟨some loopLabel, (ambient, some true), Function.update base source input⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (Function.update base source (true :: input))) = _
  rw [atLoop]
  simp [discard, TM2.stepAux]

theorem discard_empty_step (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (hinput : base source = [])
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some loopLabel, (ambient, register), base⟩ =
      some ⟨some returnLabel, (ambient, none), base⟩ := by
  have hupdate : Function.update base source [] = base := by
    funext p
    by_cases hp : p = source
    · subst p; simp [hinput]
    · simp [hp]
  change some (TM2.stepAux (program loopLabel) (ambient, register) base) = _
  rw [atLoop]
  simp [discard, TM2.stepAux, hinput, hupdate]

theorem discardTrace_update (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some loopLabel, (ambient, register),
        Function.update base source (encodeWord n ++ suffix)⟩) =
      some ⟨some returnLabel, (ambient, none), Function.update base source suffix⟩ := by
  induction n generalizing register with
  | zero =>
    simpa only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some,
      encodeWord, List.replicate_zero, List.nil_append, List.singleton_append] using
      discardStep_delimiter source loopLabel returnLabel program atLoop
        base suffix ambient register
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    simp only [encodeWord, List.replicate_succ, List.cons_append]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (TM2.step program ⟨some loopLabel, (ambient, register),
        Function.update base source (true :: (encodeWord n ++ suffix))⟩) = _
    rw [discardStep_true source loopLabel returnLabel program atLoop, ih]

theorem discardTrace (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (hinput : base source = encodeWord n ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some loopLabel, (ambient, register), base⟩) =
      some ⟨some returnLabel, (ambient, none), Function.update base source suffix⟩ := by
  have hbase : Function.update base source (encodeWord n ++ suffix) = base := by
    funext p
    by_cases hp : p = source
    · subst p; simp [hinput]
    · simp [hp]
  have h := discardTrace_update source loopLabel returnLabel program atLoop
    base n suffix ambient register
  rw [hbase] at h
  exact h

def discardInTime (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (hinput : base source = encodeWord n ++ suffix)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, register), base⟩
      (some ⟨some returnLabel, (ambient, none), Function.update base source suffix⟩)
      (n + 1) where
  steps := n + 1
  evals_in_steps := discardTrace source loopLabel returnLabel program atLoop
    base n suffix hinput ambient register
  steps_le_m := Nat.le_refl _

end DFVSGames.Foundations.Complexity.MachineLookup


namespace DFVSGames.Foundations.Complexity.MachineLookup

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

end DFVSGames.Foundations.Complexity.MachineLookup


namespace DFVSGames.Foundations.Complexity.MachineSubroutine

open Turing

variable {K Λ Λ' σ : Type} {Γ : K → Type}

def label (labels : Λ → Λ') (exit : Option Λ') : Option Λ → Option Λ'
  | none => exit
  | some l => some (labels l)

def configuration (labels : Λ → Λ') (exit : Option Λ') (c : TM2.Cfg Γ Λ σ) :
    TM2.Cfg Γ Λ' σ := ⟨label labels exit c.l, c.var, c.stk⟩

def statement (labels : Λ → Λ') (exit : Option Λ') :
    TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ' σ
  | .push k f next => .push k f (statement labels exit next)
  | .peek k f next => .peek k f (statement labels exit next)
  | .pop k f next => .pop k f (statement labels exit next)
  | .load f next => .load f (statement labels exit next)
  | .branch f yes no => .branch f (statement labels exit yes) (statement labels exit no)
  | .goto f => .goto (fun s => labels (f s))
  | .halt => match exit with
      | none => .halt
      | some l => .goto (fun _ => l)

variable [DecidableEq K]

theorem stepAux_simulation (labels : Λ → Λ') (exit : Option Λ')
    (q : TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (statement labels exit q) state tapes =
      configuration labels exit (TM2.stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f next ih =>
      simpa only [statement, TM2.stepAux] using
        ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
      simpa only [statement, TM2.stepAux] using ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      simpa only [statement, TM2.stepAux] using
        ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih => simpa only [statement, TM2.stepAux] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
      cases h : f state with
      | false => simpa only [statement, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true => simpa only [statement, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto f => rfl
  | halt => cases exit <;> rfl

theorem step_simulation (labels : Λ → Λ') (exit : Option Λ')
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' σ)
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    (a b : TM2.Cfg Γ Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (configuration labels exit a) =
      some (configuration labels exit b) := by
  cases a with
  | mk l state tapes =>
      cases l with
      | none => simp [TM2.step] at h
      | some l =>
          have hb : TM2.stepAux (source l) state tapes = b := Option.some.inj h
          rw [← hb]
          change some (TM2.stepAux (target (labels l)) state tapes) = _
          rw [atLabels, stepAux_simulation]

theorem trace (labels : Λ → Λ') (exit : Option Λ')
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' σ)
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    (steps : Nat) (a b : TM2.Cfg Γ Λ σ)
    (run : (MachineComposition.advance (TM2.step source))^[steps] (some a) = some b) :
    (MachineComposition.advance (TM2.step target))^[steps]
      (some (configuration labels exit a)) = some (configuration labels exit b) :=
  MachineComposition.liftSuccessfulTrace (TM2.step source) (TM2.step target)
    (configuration labels exit) (step_simulation labels exit source target atLabels) steps a b run

def execution (labels : Λ → Λ') (exit : Option Λ')
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' σ)
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    {a b : TM2.Cfg Γ Λ σ} {budget : Nat}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step target)
      (configuration labels exit a) (some (configuration labels exit b)) budget :=
  MachineComposition.liftExecutionInTime (TM2.step source) (TM2.step target)
    (configuration labels exit) (step_simulation labels exit source target atLabels) run

end DFVSGames.Foundations.Complexity.MachineSubroutine


namespace DFVSGames.Foundations.Complexity.MachinePreservingLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def initialTapes (tape : Fin 5 → K) (base : K → List Bool)
    (index : Nat) (indexSuffix workSuffix output : List Bool) : K → List Bool :=
  MachineLookup.tapes (tape 1) (tape 2) (tape 3) base
    (encodeWord index ++ indexSuffix) workSuffix output

def finalTapes (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat)
    (indexSuffix workSuffix output : List Bool) : K → List Bool :=
  MachineLookup.tapes (tape 1) (tape 2) (tape 3) base
    (encodeWord 0 ++ indexSuffix)
    (encodeWords (values.drop (index + 1)) ++ workSuffix) (encodeWord value ++ output)

theorem lookupFramedHaltTrace_some (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i value : Nat)
    (selected : values[i]? = some value) (indexSuffix suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (MachineLookup.program index source destination)))^[
      MachineLookupSpec.steps values i + 1]
      (some ⟨some MachineLookup.Label.guard, (ambient,register),
        MachineLookup.tapes index source destination base (encodeWord i ++ indexSuffix)
          (encodeWords values ++ suffix) output⟩) =
      some ⟨none, (ambient,none), MachineLookup.tapes index source destination base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)) ++ suffix)
        (encodeWord value ++ output)⟩ := by
  rw [Function.iterate_succ_apply',
    MachineLookup.lookupTrace_some index source destination his hid hsd
      base values i value selected indexSuffix suffix output ambient register]
  simp only [advance_some, TM2.step, MachineLookup.program, TM2.stepAux]

theorem preservingLookupTrace (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (firstLabel secondLabel : Λ) (lookupLabels : MachineLookup.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atFirst : program firstLabel = Reduction.MachineTransfer.loopAt
      (tape 0) (tape 4) id false firstLabel (some secondLabel))
    (atSecond : program secondLabel = MachineCopy.forkLoop
      (tape 4) (tape 0) (tape 2) false secondLabel (some (lookupLabels .guard)))
    (atLookup : ∀ l, program (lookupLabels l) =
      MachineSubroutine.statement lookupLabels exit (MachineLookup.program (tape 1) (tape 2) (tape 3) l))
    (base : K → List Bool) (values : List Nat) (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = []) (i value : Nat) (selected : values[i]? = some value)
    (indexSuffix workSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[
      2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1]
      (some ⟨some firstLabel, (ambient,register),
        initialTapes tape base i indexSuffix workSuffix output⟩) =
      some ⟨exit, (ambient,none), finalTapes tape base values i value indexSuffix workSuffix output⟩ := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b := fun h => hne (distinct h)
  let start := initialTapes tape base i indexSuffix workSuffix output
  have htable : start (tape 0) = encodeWords values := by
    simpa only [start, initialTapes, MachineLookup.tapes_other _ _ _ _
      (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 0 3 (by decide))] using tableWord
  have hs : start (tape 4) = [] := by
    simpa only [start, initialTapes, MachineLookup.tapes_other _ _ _ _
      (hd 4 1 (by decide)) (hd 4 2 (by decide)) (hd 4 3 (by decide))] using scratchEmpty
  have hwork : start (tape 2) = workSuffix := by
    simp only [start, initialTapes, MachineLookup.tapes_source _ _ _ (hd 2 3 (by decide))]
  have hcopy := MachineCopy.copyTrace (tape 0) (tape 2) (tape 4)
    (hd 0 2 (by decide)) (hd 0 4 (by decide)) (hd 2 4 (by decide)) false
    firstLabel secondLabel (some (lookupLabels .guard)) program atFirst atSecond start hs ambient register
  rw [htable, hwork] at hcopy
  simp only [start, initialTapes, MachineLookup.update_source _ _ _ (hd 2 3 (by decide))] at hcopy
  have hlookup := MachineSubroutine.trace lookupLabels exit
    (MachineLookup.program (tape 1) (tape 2) (tape 3)) program atLookup
    (MachineLookupSpec.steps values i + 1) _ _
    (lookupFramedHaltTrace_some (tape 1) (tape 2) (tape 3)
      (hd 1 2 (by decide)) (hd 1 3 (by decide)) (hd 2 3 (by decide))
      base values i value selected indexSuffix workSuffix output ambient none)
  simp only [MachineSubroutine.configuration, MachineSubroutine.label] at hlookup
  rw [show 2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1 =
      (MachineLookupSpec.steps values i + 1) + 2 * ((encodeWords values).length + 1) by omega,
    Function.iterate_add_apply]
  change (advance (TM2.step program))^[MachineLookupSpec.steps values i + 1]
    ((advance (TM2.step program))^[2 * ((encodeWords values).length + 1)]
      (some ⟨some firstLabel, (ambient,register),
        MachineLookup.tapes (tape 1) (tape 2) (tape 3) base
          (encodeWord i ++ indexSuffix) workSuffix output⟩)) = _
  rw [hcopy]
  exact hlookup

theorem preservingLookup_steps_le (values : List Nat) (i value : Nat)
    (selected : values[i]? = some value) :
    2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1 ≤
      5 * (encodeWords values).length + 3 := by
  have ht := MachineLookupSpec.steps_le_input_encoding_size values i
  have hi := MachineLookupSpec.index_length_le values i value selected
  omega

def preservingLookupInTime (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (firstLabel secondLabel : Λ) (lookupLabels : MachineLookup.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atFirst : program firstLabel = Reduction.MachineTransfer.loopAt
      (tape 0) (tape 4) id false firstLabel (some secondLabel))
    (atSecond : program secondLabel = MachineCopy.forkLoop
      (tape 4) (tape 0) (tape 2) false secondLabel (some (lookupLabels .guard)))
    (atLookup : ∀ l, program (lookupLabels l) =
      MachineSubroutine.statement lookupLabels exit (MachineLookup.program (tape 1) (tape 2) (tape 3) l))
    (base : K → List Bool) (values : List Nat) (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = []) (i value : Nat) (selected : values[i]? = some value)
    (indexSuffix workSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some firstLabel, (ambient,register), initialTapes tape base i indexSuffix workSuffix output⟩
      (some ⟨exit, (ambient,none), finalTapes tape base values i value indexSuffix workSuffix output⟩)
      (5 * (encodeWords values).length + 3) where
  steps := 2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1
  evals_in_steps := preservingLookupTrace tape distinct firstLabel secondLabel lookupLabels exit
    program atFirst atSecond atLookup base values tableWord scratchEmpty i value selected
    indexSuffix workSuffix output ambient register
  steps_le_m := preservingLookup_steps_le values i value selected

inductive Label
  | copyFirst | copySecond | lookup (l : MachineLookup.Label)
  deriving DecidableEq, Fintype

def program (tape : Fin 5 → K) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool)
  | .copyFirst => Reduction.MachineTransfer.loopAt (tape 0) (tape 4) id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop (tape 4) (tape 0) (tape 2) false .copySecond (some (.lookup .guard))
  | .lookup l => MachineSubroutine.statement Label.lookup none
      (MachineLookup.program (tape 1) (tape 2) (tape 3) l)

def machine : FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Label
  main := .copyFirst
  σ := Unit × Option Bool
  initialState := ((),none)
  m := program id

end DFVSGames.Foundations.Complexity.MachinePreservingLookup

end OAI
