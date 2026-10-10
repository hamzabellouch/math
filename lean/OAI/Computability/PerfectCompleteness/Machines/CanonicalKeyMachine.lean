import Mathlib.Algebra.BigOperators.Fin
import OAI.Computability.PerfectCompleteness.Machines.FiniteBlockMachineLemmas
import OAI.Computability.PerfectCompleteness.Machines.KeyMetadataMachine
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas

namespace OAI


namespace PerfectCompleteness.CanonicalKeyMachine


open Turing UniqueGamesTheorem.Foundations.Complexity MachineComposition
open CanonicalKeys CanonicalKeyShape ClauseSupport MixedSupport
open scoped BigOperators Classical

noncomputable section

variable {n : Nat}

def actualSlots (shapes : Fin n → Shape) (occurrences : Fin n → Nat)
    (variableIDs : Fin n → Fin 3 → Nat) : Fin n → Slot :=
  fun i => KeyMetadataMachine.actualSlot (shapes i) (occurrences i) (variableIDs i)

def recoveredKey (shapes : Fin n → Shape) (modes : Fin n → SupportMode) (side : Side)
    (partition : Set (Set (Fin n → ReducedValue)))
    (occurrences : Fin n → Nat) (variableIDs : Fin n → Fin 3 → Nat) : Key n where
  side := side
  retained := retained (actualSlots shapes occurrences variableIDs) modes
  partition := partition

def prefixBits (side : Side) (partition : Set (Set (Fin n → ReducedValue))) : List Bool :=
  encodeWords (CanonicalKeyEncoding.sideWord side :: CanonicalKeyEncoding.partitionWords partition)

def payload (shapes : Fin n → Shape) (modes : Fin n → SupportMode) (side : Side)
    (partition : Set (Set (Fin n → ReducedValue)))
    (occurrences : Fin n → Nat) (variableIDs : Fin n → Fin 3 → Nat) : List Bool :=
  CanonicalKeyEncoding.bits (recoveredKey shapes modes side partition occurrences variableIDs) ++ [true]

private theorem metadata_words (slots : Fin n → Slot) (modes : Fin n → SupportMode)
    (positions : List (Fin n)) :
    KeyMetadataEncoding.metadataWords
        ((positions.map (fun i => (i, recover (slots i) (modes i)))).filter
          (fun entry => decide (entry.2 ≠ .dropped))) =
      positions.flatMap (fun i => KeyMetadataMachine.retainedWords i (slots i) (modes i)) := by
  induction positions with
  | nil => rfl
  | cons i positions ih =>
    by_cases h : recover (slots i) (modes i) = .dropped
    · simp [KeyMetadataEncoding.metadataWords, KeyMetadataMachine.retainedWords, h] at ih ⊢
      exact ih
    · simpa only [List.map_cons, List.filter_cons, h, ne_eq, not_false_eq_true,
        decide_true, Bool.cond_true, ite_true, KeyMetadataEncoding.metadataWords_cons,
        KeyMetadataMachine.retainedWords, ite_false, List.flatMap_cons] using
        congrArg (KeyMetadataEncoding.entryWords (i, recover (slots i) (modes i)) ++ ·) ih

private theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem payload_eq (shapes : Fin n → Shape) (modes : Fin n → SupportMode) (side : Side)
    (partition : Set (Set (Fin n → ReducedValue)))
    (occurrences : Fin n → Nat) (variableIDs : Fin n → Fin 3 → Nat) :
    payload shapes modes side partition occurrences variableIDs =
      prefixBits side partition ++
        (List.finRange n).flatMap (fun i => KeyMetadataMachine.retainedBits i
          (KeyMetadataMachine.actualSlot (shapes i) (occurrences i) (variableIDs i)) (modes i)) ++
        [true] := by
  change encodeWords
    ((CanonicalKeyEncoding.sideWord side :: CanonicalKeyEncoding.partitionWords partition) ++
      KeyMetadataEncoding.metadataWords (retained (actualSlots shapes occurrences variableIDs) modes)) ++
      [true] = _
  rw [encodeWords_append]
  unfold retained
  rw [metadata_words, encodeWords_flatMap]
  rfl

inductive Command (n : Nat)
  | terminal
  | metadata (position : Fin n)
  | header
  deriving DecidableEq, Fintype

def LocalLabel : Command n → Type
  | .terminal => Unit
  | .metadata _ => KeyMetadataMachine.Label
  | .header => Unit

instance localLabelFintype (command : Command n) : Fintype (LocalLabel command) := by
  cases command <;> unfold LocalLabel <;> infer_instance

instance localLabelDecidableEq (command : Command n) : DecidableEq (LocalLabel command) := by
  cases command <;> unfold LocalLabel <;> infer_instance

def main : (command : Command n) → LocalLabel command
  | .terminal => ()
  | .metadata _ => .suffix
  | .header => ()

def commands (n : Nat) : List (Command n) :=
  .terminal :: ((List.finRange n).reverse.map .metadata ++ [.header])

abbrev Label (n : Nat) := MachineFiniteSequence.Label LocalLabel (commands n)

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := KeyMetadataMachine.State σ

def localInstruction (shapes : Fin n → Shape) (modes : Fin n → SupportMode) (side : Side)
    (partition : Set (Set (Fin n → ReducedValue))) (tape : Fin n → Fin 6 → K) (output : K) :
    (command : Command n) → (LocalLabel command → Λ) → Option Λ →
      LocalLabel command → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .terminal, _, exit, _ => KeyMetadataMachine.literal output [true] exit
  | .metadata i, labels, exit, label =>
      KeyMetadataMachine.instruction i (shapes i) (modes i) (tape i) labels exit label
  | .header, _, exit, _ => KeyMetadataMachine.literal output (prefixBits side partition) exit

def entry (labels : Label n → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry LocalLabel main (commands n) labels exit

def instruction (shapes : Fin n → Shape) (modes : Fin n → SupportMode) (side : Side)
    (partition : Set (Set (Fin n → ReducedValue))) (tape : Fin n → Fin 6 → K) (output : K)
    (labels : Label n → Λ) (exit : Option Λ) :
    Label n → TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  MachineFiniteSequence.instruction LocalLabel main
    (localInstruction shapes modes side partition tape output) (commands n) labels exit

def commandBits (shapes : Fin n → Shape) (modes : Fin n → SupportMode) (side : Side)
    (partition : Set (Set (Fin n → ReducedValue)))
    (occurrences : Fin n → Nat) (variableIDs : Fin n → Fin 3 → Nat) : Command n → List Bool
  | .terminal => [true]
  | .metadata i => KeyMetadataMachine.retainedBits i
      (KeyMetadataMachine.actualSlot (shapes i) (occurrences i) (variableIDs i)) (modes i)
  | .header => prefixBits side partition

def commandCost (shapes : Fin n → Shape) (modes : Fin n → SupportMode)
    (tape : Fin n → Fin 6 → K) (base : K → List Bool) : Command n → Nat
  | .terminal => 1
  | .metadata i => match KeyMetadataMachine.sourceField (shapes i) (modes i) with
      | none => 1
      | some field => 2 * ((base (KeyMetadataMachine.idTape (tape i) field)).length + 1) + 2
  | .header => 1

def sourceLength (tape : Fin n → Fin 6 → K) (base : K → List Bool) : Nat :=
  ∑ i, KeyMetadataMachine.sourceLength (tape i) base

private theorem resultOf_prepend {α : Type} (bits : α → List Bool)
    (cs : List α) (out : List Bool) :
    MachineFiniteSequence.resultOf (fun c acc => bits c ++ acc) cs out =
      cs.reverse.flatMap bits ++ out := by
  induction cs generalizing out with
  | nil => rfl
  | cons c cs ih =>
    rw [MachineFiniteSequence.resultOf, ih]
    simp only [List.reverse_cons, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.append_assoc]

private theorem steps_constant {α Data : Type} (result : α → Data → Data) (cost : α → Nat)
    (cs : List α) (data : Data) :
    MachineFiniteSequence.steps result (fun c _ => cost c) cs data = (cs.map cost).sum := by
  induction cs generalizing data with
  | nil => rfl
  | cons c cs ih => simp only [MachineFiniteSequence.steps, List.map_cons, List.sum_cons, ih]

theorem commands_bits (shapes : Fin n → Shape) (modes : Fin n → SupportMode) (side : Side)
    (partition : Set (Set (Fin n → ReducedValue)))
    (occurrences : Fin n → Nat) (variableIDs : Fin n → Fin 3 → Nat) :
    (commands n).reverse.flatMap (commandBits shapes modes side partition occurrences variableIDs) =
      payload shapes modes side partition occurrences variableIDs := by
  rw [payload_eq]
  simp only [commands, List.reverse_cons, List.reverse_append, List.reverse_nil,
    List.map_reverse, List.reverse_reverse, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.flatMap_map, commandBits, List.nil_append, List.append_nil, List.append_assoc]

omit [DecidableEq K] in
theorem commandCost_metadata_le (shapes : Fin n → Shape) (modes : Fin n → SupportMode)
    (tape : Fin n → Fin 6 → K) (base : K → List Bool) (i : Fin n) :
    commandCost shapes modes tape base (.metadata i) ≤
      2 * KeyMetadataMachine.sourceLength (tape i) base + 4 := by
  cases h : KeyMetadataMachine.sourceField (shapes i) (modes i) with
  | none => simp only [commandCost, h]; omega
  | some field =>
    have hb := KeyMetadataMachine.selected_length_le (tape i) base field
    simp only [commandCost, h]
    omega

private theorem commands_cost (cost : Command n → Nat) :
    ((commands n).map cost).sum = cost .terminal + (∑ i, cost (.metadata i)) + cost .header := by
  simp only [commands, List.map_cons, List.map_append, List.map_map, List.map_reverse,
    List.sum_cons, List.sum_append, List.sum_reverse, List.map_nil, List.sum_nil, Nat.add_zero]
  rw [← Fin.sum_univ_def]
  simp only [Function.comp_def, Nat.add_assoc]

omit [DecidableEq K] in
theorem commands_cost_le (shapes : Fin n → Shape) (modes : Fin n → SupportMode)
    (tape : Fin n → Fin 6 → K) (base : K → List Bool) :
    ((commands n).map (commandCost shapes modes tape base)).sum ≤
      2 * sourceLength tape base + 4 * n + 2 := by
  have hsum : (∑ i, commandCost shapes modes tape base (.metadata i)) ≤
      ∑ i : Fin n, (2 * KeyMetadataMachine.sourceLength (tape i) base + 4) :=
    Finset.sum_le_sum (fun i _ => commandCost_metadata_le shapes modes tape base i)
  have htotal : (∑ i : Fin n, (2 * KeyMetadataMachine.sourceLength (tape i) base + 4)) =
      2 * sourceLength tape base + 4 * n := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [sourceLength, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul, Nat.mul_comm]
  rw [htotal] at hsum
  rw [commands_cost]
  change 1 + (∑ i, commandCost shapes modes tape base (.metadata i)) + 1 ≤ _
  omega

omit [DecidableEq K] in
private theorem source_ne_output (tape : Fin n → Fin 6 → K)
    (distinct : ∀ i, Function.Injective (tape i)) (output : K)
    (sharedOutput : ∀ i, tape i 5 = output) (i : Fin n) (field : Fin 4) :
    KeyMetadataMachine.idTape (tape i) field ≠ output := by
  intro h
  have hi : KeyMetadataMachine.idIndex field = (5 : Fin 6) :=
    distinct i (h.trans (sharedOutput i).symm)
  have hv := congrArg Fin.val hi
  have hf := field.isLt
  change field.val = 5 at hv
  omega

def keyInTime (shapes : Fin n → Shape) (modes : Fin n → SupportMode) (side : Side)
    (partition : Set (Set (Fin n → ReducedValue)))
    (occurrences : Fin n → Nat) (variableIDs : Fin n → Fin 3 → Nat)
    (tape : Fin n → Fin 6 → K) (distinct : ∀ i, Function.Injective (tape i))
    (scratch output : K) (scratchOutput : scratch ≠ output)
    (sharedScratch : ∀ i, tape i 4 = scratch) (sharedOutput : ∀ i, tape i 5 = output)
    (labels : Label n → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, program (labels label) =
      instruction shapes modes side partition tape output labels exit label)
    (base : K → List Bool)
    (sourceWords : ∀ i field, base (KeyMetadataMachine.idTape (tape i) field) =
      encodeWord (KeyMetadataMachine.fieldValue (occurrences i) (variableIDs i) field))
    (scratchEmpty : base scratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry labels exit, KeyMetadataMachine.clean ambient, base⟩
      (some ⟨exit, KeyMetadataMachine.clean ambient, Function.update base output
        (payload shapes modes side partition occurrences variableIDs ++ base output)⟩)
      (2 * sourceLength tape base + 4 * n + 2) := by
  let bits := commandBits shapes modes side partition occurrences variableIDs
  let result : Command n → List Bool → List Bool := fun command out => bits command ++ out
  let cost := commandCost shapes modes tape base
  let tapes : List Bool → K → List Bool := fun out => Function.update base output out
  have source_preserved (out : List Bool) (i : Fin n) (field : Fin 4) :
      tapes out (KeyMetadataMachine.idTape (tape i) field) =
        base (KeyMetadataMachine.idTape (tape i) field) := by
    exact Function.update_of_ne (source_ne_output tape distinct output sharedOutput i field) out base
  have scratch_preserved (out : List Bool) (i : Fin n) : tapes out (tape i 4) = [] := by
    rw [sharedScratch i]
    exact (Function.update_of_ne scratchOutput out base).trans scratchEmpty
  have localTrace : ∀ command ∈ commands n,
      ∀ (placed : LocalLabel command → Λ) (next : Option Λ),
      (∀ l, program (placed l) =
        localInstruction shapes modes side partition tape output command placed next l) →
      ∀ out : List Bool, True →
      (advance (TM2.step program))^[cost command]
        (some ⟨some (placed (main command)), KeyMetadataMachine.clean ambient, tapes out⟩) =
      some ⟨next, KeyMetadataMachine.clean ambient, tapes (result command out)⟩ := by
    intro command _ placed next atPlaced out _
    cases command with
    | terminal =>
      have h := KeyMetadataMachine.literal_step output [true] next program (placed ())
        (atPlaced ()) (tapes out) ambient
      simpa only [cost, commandCost, Function.iterate_one, advance_some, main,
        result, bits, commandBits, tapes, Function.update_self, Function.update_idem] using h
    | header =>
      have h := KeyMetadataMachine.literal_step output (prefixBits side partition) next
        program (placed ()) (atPlaced ()) (tapes out) ambient
      simpa only [cost, commandCost, Function.iterate_one, advance_some, main,
        result, bits, commandBits, tapes, Function.update_self, Function.update_idem] using h
    | metadata i =>
      have atMetadata : ∀ l, program (placed l) =
          KeyMetadataMachine.instruction i (shapes i) (modes i) (tape i) placed next l := atPlaced
      cases hfield : KeyMetadataMachine.sourceField (shapes i) (modes i) with
      | none =>
        have hbits : bits (.metadata i) = [] := by
          simp only [bits, commandBits, KeyMetadataMachine.retainedBits,
            KeyMetadataMachine.retainedWords_eq, hfield, encodeWords]
        have h := KeyMetadataMachine.droppedTrace i (shapes i) (modes i) hfield
          (tape i) placed next program atMetadata (tapes out) ambient
        simpa only [cost, commandCost, hfield, main, result, hbits, List.nil_append] using h
      | some field =>
        have hbits : bits (.metadata i) =
            encodeWords (KeyMetadataMachine.prefixWords i (shapes i) (modes i)) ++
              base (KeyMetadataMachine.idTape (tape i) field) ++
              encodeWords (KeyMetadataMachine.suffixWords (shapes i) (modes i)) := by
          rw [sourceWords i field]
          simp [bits, commandBits, KeyMetadataMachine.retainedBits,
            KeyMetadataMachine.retainedWords_eq, hfield, encodeWords, List.append_assoc]
        have h := KeyMetadataMachine.selectedTrace i (shapes i) (modes i) field hfield
          (tape i) (distinct i) placed next program atMetadata (tapes out)
          (scratch_preserved out i) ambient
        rw [source_preserved out i field, sharedOutput i] at h
        simpa only [cost, commandCost, hfield, main, result, hbits,
          tapes, Function.update_self, Function.update_idem] using h
  have run := MachineFiniteSequence.trace LocalLabel main
    (localInstruction shapes modes side partition tape output) result (fun command _ => cost command)
    program (fun _ : List Bool => True) (fun _ => KeyMetadataMachine.clean ambient) tapes
    (commands n) (fun _ _ _ _ => True.intro) localTrace labels exit atLabels (base output) True.intro
  have finalOutput : MachineFiniteSequence.resultOf result (commands n) (base output) =
      payload shapes modes side partition occurrences variableIDs ++ base output := by
    rw [resultOf_prepend]
    exact congrArg (· ++ base output) (commands_bits shapes modes side partition occurrences variableIDs)
  refine
    { steps := MachineFiniteSequence.steps result (fun command _ => cost command) (commands n) (base output)
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · rw [finalOutput] at run
    unfold MachineComposition.advance at run
    simpa only [entry, tapes, Function.update_eq_self, Function.flip_def,
      Option.bind_eq_bind] using run
  · rw [steps_constant]
    exact commands_cost_le shapes modes tape base

theorem output_frame (output : K) (base : K → List Bool) (bits : List Bool)
    (k : K) (hne : k ≠ output) :
    Function.update base output (bits ++ base output) k = base k := by
  simp only [Function.update_of_ne hne]

theorem output_sources (tape : Fin n → Fin 6 → K)
    (distinct : ∀ i, Function.Injective (tape i)) (output : K)
    (sharedOutput : ∀ i, tape i 5 = output) (base : K → List Bool) (bits : List Bool)
    (i : Fin n) (field : Fin 4) :
    Function.update base output (bits ++ base output) (KeyMetadataMachine.idTape (tape i) field) =
      base (KeyMetadataMachine.idTape (tape i) field) :=
  output_frame output base bits _ (source_ne_output tape distinct output sharedOutput i field)

theorem output_scratch (scratch output : K) (hne : scratch ≠ output)
    (base : K → List Bool) (bits : List Bool) (hempty : base scratch = []) :
    Function.update base output (bits ++ base output) scratch = [] :=
  (output_frame output base bits scratch hne).trans hempty

theorem label_finite : Finite (Label n) := inferInstance

theorem state_finite [Finite σ] : Finite (State σ) := inferInstance

end
end PerfectCompleteness.CanonicalKeyMachine

end OAI
