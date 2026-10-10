import OAI.Computability.PerfectCompleteness.Foundations.CanonicalEdgesLemmas
import OAI.Computability.PerfectCompleteness.Machines.FiniteBlockMachineLemmas
import OAI.Computability.PerfectCompleteness.Machines.SignedTupleBodyMachine
import OAI.Computability.PerfectCompleteness.Reduction.NormalizedTarget

namespace OAI


namespace PerfectCompleteness.SourceKeyBounds


open CanonicalKeys CanonicalKeyShape ClauseSupport MixedSupport
open UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

def SlotIDsLe (bound : Nat) : Slot → Prop
  | .clause occurrence variableIDs _ => occurrence ≤ bound ∧ ∀ i, variableIDs i ≤ bound
  | .bit variableID => variableID ≤ bound

theorem recover_entryID_le (bound : Nat) (slot : Slot) (support : SupportMode)
    (bounded : SlotIDsLe bound slot) : KeyMetadataEncoding.entryID (recover slot support) ≤ bound := by
  cases slot <;> cases support <;>
    simp_all [SlotIDsLe, recover, KeyMetadataEncoding.entryID]

theorem actualSlot_IDs_le (bound : Nat) (shape : Shape) (occurrence : Nat)
    (variableIDs : Fin 3 → Nat) (occurrenceBound : occurrence ≤ bound)
    (variableBounds : ∀ i, variableIDs i ≤ bound) :
    SlotIDsLe bound (KeyMetadataMachine.actualSlot shape occurrence variableIDs) := by
  cases shape <;> simp_all [KeyMetadataMachine.actualSlot, SlotIDsLe]

variable {width : Nat} {Y : Type*}

theorem retained_length_le (slots : Fin width → Slot) (support : Fin width → SupportMode) :
    (retained slots support).length ≤ width := by
  unfold retained
  exact (List.length_filter_le _ _).trans_eq (by simp)

theorem retained_entryID_le (slots : Fin width → Slot) (support : Fin width → SupportMode)
    (bound : Nat) (bounded : ∀ i, SlotIDsLe bound (slots i))
    (entry : Fin width × SlotKey) (present : entry ∈ retained slots support) :
    KeyMetadataEncoding.entryID entry.2 ≤ bound := by
  unfold retained at present
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp (List.mem_filter.mp present).1
  exact recover_entryID_le bound (slots i) (support i) (bounded i)

theorem key_retained_length (side : Side) (slots : Fin width → Slot)
    (f : Assignment slots → Y) : (CanonicalKeys.key side slots f).retained.length ≤ width := by
  change (retainedKeys slots f).length ≤ width
  rw [retainedKeys_recover]
  exact retained_length_le slots _

theorem key_entryID_le (side : Side) (slots : Fin width → Slot)
    (f : Assignment slots → Y) (bound : Nat) (bounded : ∀ i, SlotIDsLe bound (slots i))
    (entry : Fin width × SlotKey) (present : entry ∈ (CanonicalKeys.key side slots f).retained) :
    KeyMetadataEncoding.entryID entry.2 ≤ bound := by
  change entry ∈ retainedKeys slots f at present
  rw [retainedKeys_recover] at present
  exact retained_entryID_le slots _ bound bounded entry present

theorem variableCount_le_bits (input : NormalizedSourceInput.Input) :
    NormalizedSourceInput.variableCount input ≤ (NormalizedSourceInput.bits input).length := by
  rw [NormalizedSourceInput.bits_eq]
  simp only [List.length_append, encodeWord_length]
  omega

theorem clauseCount_le_bits (input : NormalizedSourceInput.Input) :
    NormalizedSourceInput.clauseCount input ≤ (NormalizedSourceInput.bits input).length := by
  rw [NormalizedSourceInput.bits_eq]
  simp only [List.length_append, encodeWord_length]
  omega

theorem source_variable_le_bits (input : NormalizedSourceInput.Input)
    (index : Fin (NormalizedSourceInput.clauseCount input)) (slot : Fin 3) :
    ((NormalizedSourceInput.clauses input index).variable slot).val ≤
      (NormalizedSourceInput.bits input).length :=
  (Nat.le_of_lt ((NormalizedSourceInput.clauses input index).variable slot).isLt).trans
    (variableCount_le_bits input)

variable {branch : Nat → Nat} {n t : Nat}

theorem numberedSlots_IDs_le (input : NormalizedSourceInput.Input)
    (source : PreliminarySampler.Questions branch n t (NormalizedSourceInput.clauseCount input))
    (position : Fin (TreeCanonical.locationCount branch n t)) :
    SlotIDsLe (NormalizedSourceInput.bits input).length
      (TreeCanonical.numberedSlots
        (MetadataFreeSampler.sourceSlots (NormalizedSourceInput.clauses input) source) position) := by
  let indices := SourceQuestionOrder.questionToTuple source
  have restored : NormalizedTarget.tupleQuestion input indices = source :=
    SourceQuestionOrder.tupleToQuestion_questionToTuple source
  have slotsEq := NormalizedTarget.numberedSlots_eq input indices position
  rw [restored] at slotsEq
  rw [slotsEq]
  apply actualSlot_IDs_le
  · exact (Nat.le_of_lt (indices position).isLt).trans (clauseCount_le_bits input)
  · intro slot
    rw [NormalizedTarget.parsedVariableIDs_eq]
    exact source_variable_le_bits input (indices position) slot

theorem source_key_retained_length (input : NormalizedSourceInput.Input)
    (source : PreliminarySampler.Questions branch n t (NormalizedSourceInput.clauseCount input))
    (side : Side)
    (f : TreeSourceSpaces.Domain
      (MetadataFreeSampler.sourceSlots (NormalizedSourceInput.clauses input) source) → Y) :
    (TreeCanonical.key side
      (MetadataFreeSampler.sourceSlots (NormalizedSourceInput.clauses input) source) f).retained.length ≤
        TreeCanonical.locationCount branch n t :=
  key_retained_length side _ _

theorem source_key_entryID_le (input : NormalizedSourceInput.Input)
    (source : PreliminarySampler.Questions branch n t (NormalizedSourceInput.clauseCount input))
    (side : Side)
    (f : TreeSourceSpaces.Domain
      (MetadataFreeSampler.sourceSlots (NormalizedSourceInput.clauses input) source) → Y)
    (entry : Fin (TreeCanonical.locationCount branch n t) × SlotKey)
    (present : entry ∈ (TreeCanonical.key side
      (MetadataFreeSampler.sourceSlots (NormalizedSourceInput.clauses input) source) f).retained) :
    KeyMetadataEncoding.entryID entry.2 ≤ (NormalizedSourceInput.bits input).length :=
  key_entryID_le side _ _ _ (numberedSlots_IDs_le input source) entry present


variable (input : NormalizedSourceInput.Input) (rows repeats : Nat → Nat)

local notation "clauses" => NormalizedSourceInput.clauses input
local notation "F" => FinitePreliminaryCompletion.blockFamily clauses branch n t rows repeats
local notation "family" => PreliminarySampler.family clauses branch n t rows repeats

theorem left_retained_length (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    (CanonicalGame.leftKey F e).retained.length ≤ TreeCanonical.locationCount branch n t := by
  rw [HierarchicalGame.leftKey_eq family e]
  exact source_key_retained_length input e.1.1 .left _

theorem right_retained_length (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    (CanonicalGame.rightKey F e).retained.length ≤ TreeCanonical.locationCount branch n t := by
  rw [HierarchicalGame.rightKey_eq family e]
  exact source_key_retained_length input e.1.1 .right _

theorem left_entryID_le (e : PreliminarySampler.Raw clauses branch n t rows repeats)
    (entry : Fin (TreeCanonical.locationCount branch n t) × SlotKey)
    (present : entry ∈ (CanonicalGame.leftKey F e).retained) :
    KeyMetadataEncoding.entryID entry.2 ≤ (NormalizedSourceInput.bits input).length := by
  rw [HierarchicalGame.leftKey_eq family e] at present
  exact source_key_entryID_le input e.1.1 .left _ entry present

theorem right_entryID_le (e : PreliminarySampler.Raw clauses branch n t rows repeats)
    (entry : Fin (TreeCanonical.locationCount branch n t) × SlotKey)
    (present : entry ∈ (CanonicalGame.rightKey F e).retained) :
    KeyMetadataEncoding.entryID entry.2 ≤ (NormalizedSourceInput.bits input).length := by
  rw [HierarchicalGame.rightKey_eq family e] at present
  exact source_key_entryID_le input e.1.1 .right _ entry present

end

end PerfectCompleteness.SourceKeyBounds



namespace PerfectCompleteness.SignedSourceCost


open UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat} {Extra : Type} [DecidableEq Extra]

local notation "width" => TreeCanonical.locationCount branch n t

theorem fieldValue_le_bits (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (position : Fin width) (field : Fin 4) :
    KeyMetadataMachine.fieldValue
      (SignedTupleLayout.ids input.formula indices position)
      (SignedTupleLayout.vars input.formula indices position) field ≤
        (NormalizedSourceInput.bits input).length := by
  refine Fin.cases ?_ (fun slot => ?_) field
  · change (indices position).val ≤ (NormalizedSourceInput.bits input).length
    exact (Nat.le_of_lt (indices position).isLt).trans
      (SourceKeyBounds.clauseCount_le_bits input)
  · change (SignedTupleLayout.vars input.formula indices position slot) ≤
      (NormalizedSourceInput.bits input).length
    exact SourceKeyBounds.source_variable_le_bits input (indices position) slot

theorem prepared_metadata (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (base : SignedTupleLayout.Tape width Extra → List Bool)
    (hinput : SignedTupleLayout.Input input.formula indices base)
    (data : SignedTupleBodyMachine.Data width) (position : Fin width) (field : Fin 4) :
    SignedTupleBodyMachine.tapes SignedTupleLayout.Tape.edgeWork
      SignedTupleLayout.Tape.edgeCount
      (SignedTupleLayout.preparedTapes input.formula indices base) data
      (KeyMetadataMachine.idTape (SignedTupleLayout.metadata position) field) =
        encodeWord (KeyMetadataMachine.fieldValue
          (SignedTupleLayout.ids input.formula indices position)
          (SignedTupleLayout.vars input.formula indices position) field) := by
  have unchanged :
      SignedTupleBodyMachine.tapes SignedTupleLayout.Tape.edgeWork
        SignedTupleLayout.Tape.edgeCount
        (SignedTupleLayout.preparedTapes input.formula indices base) data
        (KeyMetadataMachine.idTape (SignedTupleLayout.metadata position) field) =
      SignedTupleLayout.preparedTapes input.formula indices base
        (KeyMetadataMachine.idTape (SignedTupleLayout.metadata position) field) := by
    apply SignedTupleBodyMachine.tapes_frame
    all_goals
      fin_cases field <;>
        simp [KeyMetadataMachine.idTape, KeyMetadataMachine.idIndex, SignedTupleLayout.metadata]
  exact unchanged.trans
    (SignedTupleLayout.prepared_metadata input.formula indices base hinput position field)

theorem prepared_sourceLength_le (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (base : SignedTupleLayout.Tape width Extra → List Bool)
    (hinput : SignedTupleLayout.Input input.formula indices base)
    (data : SignedTupleBodyMachine.Data width) :
    CanonicalKeyMachine.sourceLength SignedTupleLayout.metadata
      (SignedTupleBodyMachine.tapes SignedTupleLayout.Tape.edgeWork
        SignedTupleLayout.Tape.edgeCount
        (SignedTupleLayout.preparedTapes input.formula indices base) data) ≤
      4 * width * ((NormalizedSourceInput.bits input).length + 1) := by
  calc
    CanonicalKeyMachine.sourceLength SignedTupleLayout.metadata
        (SignedTupleBodyMachine.tapes SignedTupleLayout.Tape.edgeWork
          SignedTupleLayout.Tape.edgeCount
          (SignedTupleLayout.preparedTapes input.formula indices base) data) ≤
        ∑ _ : Fin width, ∑ _ : Fin 4, ((NormalizedSourceInput.bits input).length + 1) := by
      unfold CanonicalKeyMachine.sourceLength KeyMetadataMachine.sourceLength
      apply Finset.sum_le_sum
      intro position _
      apply Finset.sum_le_sum
      intro field _
      rw [prepared_metadata input indices base hinput data position field, encodeWord_length]
      exact Nat.add_le_add_right (fieldValue_le_bits input indices position field) 1
    _ = 4 * width * ((NormalizedSourceInput.bits input).length + 1) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

end
end PerfectCompleteness.SignedSourceCost

end OAI
