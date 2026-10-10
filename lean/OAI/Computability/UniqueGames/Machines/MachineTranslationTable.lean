import OAI.Computability.UniqueGames.Machines.MachineFiniteAlphabet
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.Reduction.EncodingLemmas
import OAI.Computability.UniqueGames.Reduction.MachineTransducer

namespace OAI

section

/-!
Full forward permutation-table emission for a fixed binary-vector alphabet.

The input to this component is the zero-delimited unary index of one offset
in `F₂^s`; this is an internal finite label, not a binary 3SAT variable name.
The output is the serialization of every forward image of the translation.
A finite-state transducer counts up to `2^s`, emits the fixed literal table
at the delimiter, and resets. The state bound and emission table depend only
on the fixed dimension, and the polynomial-time certificate is obtained from
the proved actual TM2 transducer and reversal programs.

This component supplies neither an occurrence-list loop nor a whole reduction.
-/

namespace UniqueGamesTheorem.MachineTranslationTable

open Turing
open UniqueGamesTheorem.Foundations
open Complexity
open UniqueGamesTheorem.Integration.BinaryLinear

open UniqueGamesTheorem.Reduction

/-- Both the forward and inverse arrays have one entry for every alphabet label. -/
def table {s : Nat} (offset : Vector s) : Target.PermutationTable (2 ^ s) :=
  Encoding.translationTable 0 offset

@[simp] theorem table_images {s : Nat} (offset label : Vector s) :
    (table offset).images[Encoding.alphabetEquiv s label] =
      Encoding.alphabetEquiv s (label + offset) := by
  simpa only [table, add_zero] using Encoding.translationTable_images (0 : Vector s) offset label

@[simp] theorem table_inverseImages {s : Nat} (offset label : Vector s) :
    (table offset).inverseImages[Encoding.alphabetEquiv s label] =
      Encoding.alphabetEquiv s (label + offset) := by
  simpa only [table, add_zero] using
    Encoding.translationTable_inverseImages (0 : Vector s) offset label

theorem table_satisfied_iff {s : Nat} (offset left right : Vector s) :
    (table offset).images[Encoding.alphabetEquiv s left] =
      Encoding.alphabetEquiv s right ↔ right = left + offset := by
  rw [table_images, (Encoding.alphabetEquiv s).injective.eq_iff, eq_comm]

def tableBits {s : Nat} (offset : Vector s) : List Bool :=
  encodeWords (tableWords (table offset))

@[simp] theorem decode_tableBits {s : Nat} (offset : Vector s) :
    (decodeWords (tableBits offset) >>= parsePermutation (2 ^ s)) = some (table offset) := by
  simp [tableBits]

@[simp] theorem tableWords_length {s : Nat} (offset : Vector s) :
    (Complexity.tableWords (table offset)).length = 2 ^ s := by simp

/-- The last finite-control value is an overflow sentinel. -/
abbrev State (s : Nat) := Fin (2 ^ s + 1)

def initial (s : Nat) : State s := ⟨0, Nat.zero_lt_succ _⟩

def increment {s : Nat} (state : State s) : State s :=
  ⟨min (state.val + 1) (2 ^ s), Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

def transition {s : Nat} (state : State s) (symbol : Bool) : State s :=
  if symbol then increment state else initial s

/-- Every entry is a fixed finite output word, indexed by the fixed control state. -/
def emission {s : Nat} (state : State s) (symbol : Bool) : List Bool :=
  if symbol then []
  else if valid : state.val < 2 ^ s then
    tableBits ((Encoding.alphabetEquiv s).symm ⟨state.val, valid⟩)
  else []

def output (s : Nat) : List Bool → List Bool :=
  MachineTransducer.output (transition (s := s)) emission (initial s)

private theorem output_word_from {s : Nat} (state : State s) (count : Nat)
    (valid : state.val + count < 2 ^ s) (rest : List Bool) :
    MachineTransducer.output (transition (s := s)) emission state (encodeWord count ++ rest) =
      tableBits ((Encoding.alphabetEquiv s).symm ⟨state.val + count, valid⟩) ++
        output s rest := by
  induction count generalizing state with
  | zero =>
    have hv : state.val < 2 ^ s := by omega
    simp [encodeWord, MachineTransducer.output, transition, emission, hv, output]
  | succ count ih =>
    have hb : state.val + 1 ≤ 2 ^ s := by omega
    have hi : (increment state).val = state.val + 1 := Nat.min_eq_left hb
    have hv : (increment state).val + count < 2 ^ s := by omega
    simp only [encodeWord, List.replicate_succ, List.cons_append,
      MachineTransducer.output, transition, ↓reduceIte, emission,
      List.nil_append]
    have h := ih (increment state) hv
    simpa only [encodeWord, hi, Nat.add_assoc, Nat.add_comm 1 count] using h

/-- One serialized finite offset produces the complete forward table in order. -/
theorem output_encoded_append {s : Nat} (offset : Vector s) (rest : List Bool) :
    output s (encodeWord (Encoding.alphabetEquiv s offset).val ++ rest) =
      tableBits offset ++ output s rest := by
  have valid : (initial s).val + (Encoding.alphabetEquiv s offset).val < 2 ^ s := by
    simpa only [initial, Nat.zero_add] using (Encoding.alphabetEquiv s offset).isLt
  have h := output_word_from (initial s) (Encoding.alphabetEquiv s offset).val valid rest
  have index : (⟨(initial s).val + (Encoding.alphabetEquiv s offset).val, valid⟩ : Fin (2 ^ s)) =
      Encoding.alphabetEquiv s offset := by
    apply Fin.ext
    simp [initial]
  rw [index, Encoding.alphabetEquiv_symm_apply_apply] at h
  exact h

@[simp] theorem output_encoded {s : Nat} (offset : Vector s) :
    output s (encodeWord (Encoding.alphabetEquiv s offset).val) = tableBits offset := by
  simpa [output, MachineTransducer.output] using output_encoded_append offset []

/-- Complete tables are concatenated in the input occurrence order. -/
theorem output_encoded_list {s : Nat} (offsets : List (Vector s)) :
    output s (offsets.flatMap (fun offset =>
      encodeWord (Encoding.alphabetEquiv s offset).val)) = offsets.flatMap tableBits := by
  induction offsets with
  | nil => rfl
  | cons offset offsets ih =>
    simp only [List.flatMap_cons, output_encoded_append, ih]

private noncomputable def forwardComposition (s : Nat) :=
  MachineSequential.composeBits
    (MachineTransducer.reversedComputableInPolyTime (initial s) transition emission)
    MachineReverse.computableInPolyTime

/-- A total actual polynomial-time machine, including on malformed input words.
The record retains the literal composed machine, without a cast of its machine
field when simplifying the two reversals in the semantic output. -/
noncomputable def computableInPolyTime (s : Nat) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) id (output s) where
  toTM2ComputableAux := (forwardComposition s).toTM2ComputableAux
  time := (forwardComposition s).time
  outputsFun input := by
    simpa only [List.reverse_reverse, output] using (forwardComposition s).outputsFun input

/-- All physical tapes of the actual composed machine have finite alphabets. -/
theorem computation_finiteAlphabet (s : Nat) :
    MachineFiniteAlphabet.FiniteAlphabet (computableInPolyTime s).tm := by
  change MachineFiniteAlphabet.FiniteAlphabet
    (MachineSequential.composeBits
      (MachineTransducer.reversedComputableInPolyTime (initial s) transition emission)
      UniqueGamesTheorem.Reduction.MachineReverse.computableInPolyTime).tm
  apply MachineFiniteAlphabet.composeBits
  · exact MachineFiniteAlphabet.of_bool _ (fun _ => rfl)
  · exact MachineFiniteAlphabet.of_bool _ (fun _ => rfl)

/-- The same machine, specialized to the actual offset and full-table encodings. -/
noncomputable def offsetComputableInPolyTime (s : Nat) :
    TM2ComputableInPolyTime
      (fun offset : Vector s => encodeWord (Encoding.alphabetEquiv s offset).val)
      tableBits (id : Vector s → Vector s) where
  toTM2ComputableAux := (computableInPolyTime s).toTM2ComputableAux
  time := (computableInPolyTime s).time
  outputsFun offset := by
    simpa only [id_eq, output_encoded] using
      (computableInPolyTime s).outputsFun
        (encodeWord (Encoding.alphabetEquiv s offset).val)

end UniqueGamesTheorem.MachineTranslationTable

end

end OAI
