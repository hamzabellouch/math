import Mathlib
import OAI.Computability.MaxCut.Machines.MachineSubdivisionDynamicRows

namespace OAI

/-!
Finite control for destructive unary-indexed table lookup. The guard decreases
the index even when the table is exhausted. Selection tests for an empty table
before writing the destination. All tests inspect just one finite head register.
-/

namespace MaxCutGames.Foundations.Complexity.MachineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def discard (source : K) (loopLabel returnLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.goto fun _ => loopLabel)
      (.load (fun state => (state.1, none)) (.goto fun _ => returnLabel)))

/-- Check that a field exists before seeding its destination delimiter. -/
def select (source destination : K) (copyLabel rejected : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .peek source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (Hastad.SourceMachine.fieldStart destination copyLabel)
      (.load (fun state => (state.1, none)) (.goto fun _ => rejected)))

inductive Label
  | guard | skip | select | copy | accepted | rejected
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.guard, .skip, .select, .copy, .accepted,
  .rejected]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

/-- Six fixed labels and a single optional-bit register, independent of input. -/
def program (index source destination : K) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool)
  | .guard => MachineUnaryCounter.guard index .skip .select
  | .skip => discard source .skip .guard
  | .select => select source destination .copy .rejected
  | .copy => Hastad.SourceMachine.fieldLoop source destination .copy (some .accepted)
  | .accepted => .halt
  | .rejected => .halt

/-- Three caller tapes with every other tape retained verbatim. -/
def tapes (index source destination : K) (base : K → List Bool)
    (counter input output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base index counter) source input)
    destination output

@[simp] theorem tapes_index (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (counter input output : List Bool) :
    tapes index source destination base counter input output index = counter := by
  simp [tapes, his, hid]

@[simp] theorem tapes_source (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter input output : List Bool) :
    tapes index source destination base counter input output source = input := by
  simp [tapes, hsd]

@[simp] theorem tapes_destination (index source destination : K)
    (base : K → List Bool) (counter input output : List Bool) :
    tapes index source destination base counter input output destination = output := by
  simp [tapes]

theorem tapes_other (index source destination p : K)
    (hi : p ≠ index) (hs : p ≠ source) (hd : p ≠ destination)
    (base : K → List Bool) (counter input output : List Bool) :
    tapes index source destination base counter input output p = base p := by
  simp [tapes, hi, hs, hd]

theorem update_index (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (counter input output replacement : List Bool) :
    Function.update (tapes index source destination base counter input output) index replacement =
      tapes index source destination base replacement input output := by
  funext p
  by_cases hi : p = index
  · subst p; simp [tapes, his, hid]
  · by_cases hs : p = source
    · subst p; by_cases hs : source = destination <;> simp [tapes, hi, hs, Ne.symm hid]
    · by_cases hd : p = destination
      · subst p; simp [tapes, hi]
      · simp [tapes, hi, hs, hd]

theorem update_source (index source destination : K) (hsd : source ≠ destination)
    (base : K → List Bool) (counter input output replacement : List Bool) :
    Function.update (tapes index source destination base counter input output) source replacement =
      tapes index source destination base counter replacement output := by
  funext p
  by_cases hs : p = source
  · subst p; simp [tapes, hsd]
  · by_cases hd : p = destination
    · subst p; simp [tapes, hs]
    · simp [tapes, hs, hd]

theorem update_destination (index source destination : K)
    (base : K → List Bool) (counter input output replacement : List Bool) :
    Function.update (tapes index source destination base counter input output)
      destination replacement = tapes index source destination base counter input replacement := by
  simp [tapes]

theorem fieldTapes_eq (index source destination : K) (hsd : source ≠ destination)
    (base : K → List Bool) (counter input output input' output' : List Bool) :
    Hastad.SourceMachine.fieldTapes source destination
      (tapes index source destination base counter input output) input' output' =
      tapes index source destination base counter input' output' := by
  rw [Hastad.SourceMachine.fieldTapes, update_source _ _ _ hsd, update_destination]

/-- A concrete finite machine using exactly three binary stacks. Its table and
unary index may be supplied in a caller configuration; no list oracle is used. -/
def machine : FinTM2 where
  K := Fin 3
  k₀ := 1
  k₁ := 2
  Γ _ := Bool
  Λ := Label
  main := .guard
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program 0 1 2

end MaxCutGames.Foundations.Complexity.MachineLookup

/-!
Pure list specification for destructive zero-based unary table lookup.
These are serialization identities and bit-count bounds, not TM2 runtime
certificates. The connection to actual transitions is in `MachineLookup`.
-/
namespace MaxCutGames.Foundations.Complexity.MachineLookupSpec

/-- Saturating removal of one zero-delimited word. -/
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

/-- Iterated word removal agrees with zero-based list dropping, even after
running past the end of the table. -/
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

/-- Copy the next complete word, including its delimiter. Empty input and
unterminated words fail explicitly. -/
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

/-- The index is on a separate tape and must decode to exactly one word. -/
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

/-- Literal split at the selected word. -/
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

/-- This counts the bits through the selected word, capped at the whole table
when the index is invalid. It is not a machine step count. -/
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

/-! Bounds on the proposed lookup recurrence. A separate machine proof must
identify these counts with actual transition traces. -/

def steps : List Nat → Nat → Nat
  | [], i => 2 * i + 2
  | n :: _, 0 => n + 3
  | n :: ns, i + 1 => n + 2 + steps ns i

/-- A uniform bound, including indices beyond the end of the table. -/
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

/-- The requested recurrence bound with one further unit of slack. -/
theorem steps_le_encoded_length (values : List Nat) (i : Nat) :
    steps values i ≤ (encodeWords values).length + 2 * i + 3 := by
  have h := steps_le_encoded_length_strong values i
  omega

/-- Successful lookup uses exactly the consumed table prefix, one guard per
skipped word, and the two final control steps. -/
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

/-- A subtraction-free exact failure formula: the whole table has been
consumed, and every remaining unary index bit costs two steps. -/
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

/-- Linear in the combined encoded tape lengths. This is a bound for `steps`,
not yet a theorem about a concrete machine's execution. -/
theorem steps_le_input_encoding_size (values : List Nat) (i : Nat) :
    steps values i ≤ (encodeWords values).length + 2 * (encodeWord i).length := by
  have h := steps_le_encoded_length_strong values i
  rw [encodeWord_length]
  omega

end MaxCutGames.Foundations.Complexity.MachineLookupSpec

/-!
Execution of the destructive field-discard loop in an arbitrary ambient TM2
program. The scanner consumes a unary payload and its delimiter, preserves the
ambient state and other tapes, and clears its head register on return. At EOF it
returns immediately, leaving the tapes unchanged.
-/

namespace MaxCutGames.Foundations.Complexity.MachineLookup

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

/-- EOF returns to the guard in one transition, without changing any tape. -/
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

/-- A normalized tape form for the field-discard trace. -/
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

/-- Discard exactly the first encoded field, in one transition per payload bit
plus one transition for its delimiter. No condition is imposed on other tapes. -/
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

/-- The same exact trace packaged for composition with ambient machine phases. -/
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

end MaxCutGames.Foundations.Complexity.MachineLookup

/-!
Actual traces for the fixed unary lookup machine. Successful lookup preserves
an arbitrary unread table suffix. Rejection relative to a list's end is stated
only for its complete, unframed encoding, so no hidden endpoint is assumed.
-/

namespace MaxCutGames.Foundations.Complexity.MachineLookup

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

/-- A successful positional lookup scans precisely its prior and selected
field. The suffix is arbitrary and is retained byte for byte. -/
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

/-- Successful array access, with explicit selected value and preserved framing. -/
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

/-- Invalid indices reject on a complete encoded table, after consuming that
table and all positive index bits. The output and other tapes are unchanged. -/
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

/-- The two explicit control outcomes on a complete encoded table. -/
def resultLabel (values : List Nat) (i : Nat) : Label :=
  match values[i]? with
  | some _ => .accepted
  | none => .rejected

/-- Successful lookup prefixes a complete unary word; failure writes nothing. -/
def resultOutput (values : List Nat) (i : Nat) (output : List Bool) : List Bool :=
  match values[i]? with
  | some value => encodeWord value ++ output
  | none => output

/-- A total execution statement for every natural index and complete table.
No bound or validity assumption on the index is needed. -/
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

/-- A proved linear transition budget in the lengths of the encoded table and
index, including invalid indices. The witness is the actual trace above. -/
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

/-- The final control label executes a genuine halt in one more transition. -/
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

/-- A single polynomial in the combined two input lengths. -/
noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 2 * Polynomial.X + 1

theorem timePolynomial_bounds (values : List Nat) (i : Nat) :
    MachineLookupSpec.steps values i + 1 ≤
      timePolynomial.eval ((encodeWords values).length + (encodeWord i).length) := by
  have h := MachineLookupSpec.steps_le_input_encoding_size values i
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one]
  omega

/-- The same exact computation as a certificate for the concrete finite
three-stack machine. Both valid and invalid indices terminate with reset local
state, retaining the zero index delimiter and all other stated tape contents. -/
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

end MaxCutGames.Foundations.Complexity.MachineLookup

end OAI
