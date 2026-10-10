import OAI.Computability.PerfectCompleteness.Decoding.CleanLeftDecoderLemmas
import OAI.Computability.PerfectCompleteness.Repetition.CleanPhysicalReplay
import OAI.Computability.PerfectCompleteness.Repetition.CleanRecordObservation

namespace OAI

section

namespace PerfectCompleteness.CleanRecordDecoderInput

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

variable {branch : Nat → Nat} {n h t v m : Nat} [NeZero m]
  (rows repeats : Nat → Nat) (upper : Nodes branch n)
  (d : HierarchicalFrozenTables.LowerNodes upper (h + 1))
  (cut : OwnInputReference.Cut upper (HierarchicalLeftDecoder.LowerNode upper (h + 1) d))

abbrev path := CleanRightDecoder.fullPath upper
  (HierarchicalLeftDecoder.LowerNode upper (h + 1) d) cut
  (CleanDecoderContext.lowerHeight upper d)

variable (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

abbrev Record := CleanPhysicalReplay.Record (t := t) rows repeats (path upper d cut) clauses designated
abbrev Sample := CleanPhysicalReplay.Sample (t := t) rows repeats (path upper d cut) clauses designated
abbrev Exterior := CleanPhysicalReplay.Exterior rows repeats (path upper d cut) outside placeholder

def exposed (record : Record (t := t) rows repeats upper d cut clauses designated)
    (external : Exterior rows repeats upper d cut outside placeholder) :
    CleanDecoderContext.Exposed branch rows repeats n h t v m upper d where
  clauses := clauses
  designated := designated
  clean := CleanRecordChildBlocks.clean rows clauses designated record
  visible := CleanRecordChildBlocks.visible rows clauses designated record
  projected := CleanRecordChildBlocks.projected rows clauses designated record
  cleanProjected := CleanSourceRecord.clean_projected designated
    (SourceChildKernel.Factors (C := WholeCutCalls.Index rows repeats (path upper d cut))
      (t := t) rows clauses designated) record
  cut := cut
  outside := outside
  leftTape := CleanPhysicalReplay.leftRecord rows repeats (path upper d cut) outside placeholder
    clauses designated record external
  rightTape := CleanPhysicalReplay.rightRecord rows repeats (path upper d cut) outside placeholder
    clauses designated record external

abbrev observe (x : Sample (t := t) rows repeats upper d cut clauses designated) :
    Record (t := t) rows repeats upper d cut clauses designated :=
  CleanRecordObservation.observe rows clauses designated x

omit [NeZero m] in
@[simp] theorem event_observe (x : Sample (t := t) rows repeats upper d cut clauses designated) :
    CleanRecordChildBlocks.event rows clauses designated
      (observe rows repeats upper d cut clauses designated x) x = true :=
  CleanRecordObservation.event_observe rows clauses designated x

def leftQuestions (record : Record (t := t) rows repeats upper d cut clauses designated)
    (x : Sample (t := t) rows repeats upper d cut clauses designated) :=
  CleanRecordObservation.leftQuestions rows clauses designated record x

def rightQuestions (record : Record (t := t) rows repeats upper d cut clauses designated)
    (x : Sample (t := t) rows repeats upper d cut clauses designated) :=
  CleanRecordObservation.rightQuestions rows clauses designated record x

def sources (record : Record (t := t) rows repeats upper d cut clauses designated)
    (x : Sample (t := t) rows repeats upper d cut clauses designated) :
    {i : Fin (branch h) // CleanRecordChildBlocks.clean rows clauses designated record i} →
      SourceOddLists.Occurrences m t := fun i => (x i.val).1

omit [NeZero m] in
theorem leftQuestions_sources (record : Record (t := t) rows repeats upper d cut clauses designated)
    (x : Sample (t := t) rows repeats upper d cut clauses designated) :
    leftQuestions rows repeats upper d cut clauses designated record x =
      fun i => SourceOddLists.left (sources rows repeats upper d cut clauses designated record x i) := rfl

omit [NeZero m] in
theorem rightQuestions_sources (record : Record (t := t) rows repeats upper d cut clauses designated)
    (x : Sample (t := t) rows repeats upper d cut clauses designated) :
    rightQuestions rows repeats upper d cut clauses designated record x =
      fun i => SourceOddLists.right clauses
        (sources rows repeats upper d cut clauses designated record x i) := rfl

theorem leftSlots_eq (record : Record (t := t) rows repeats upper d cut clauses designated)
    (external : Exterior rows repeats upper d cut outside placeholder)
    (x : Sample (t := t) rows repeats upper d cut clauses designated)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true) :
    CleanDecoderContext.leftSlots
      (exposed rows repeats upper d cut outside placeholder clauses designated record external)
      (leftQuestions rows repeats upper d cut clauses designated record x) =
    CutSlotAssembly.fill (path upper d cut) outside
      (CleanPhysicalReplay.leftInside rows repeats (path upper d cut) clauses designated x) := by
  exact congrArg (CutSlotAssembly.fill (path upper d cut) outside)
    (CleanRecordObservation.leftInside_eq rows clauses designated record x hevent)

theorem rightSlots_eq (record : Record (t := t) rows repeats upper d cut clauses designated)
    (external : Exterior rows repeats upper d cut outside placeholder)
    (x : Sample (t := t) rows repeats upper d cut clauses designated)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true) :
    CleanDecoderContext.rightSlots
      (exposed rows repeats upper d cut outside placeholder clauses designated record external)
      (rightQuestions rows repeats upper d cut clauses designated record x) =
    CutSlotAssembly.fill (path upper d cut) outside
      (CleanPhysicalReplay.rightInside rows repeats (path upper d cut) clauses designated x) := by
  exact congrArg (CutSlotAssembly.fill (path upper d cut) outside)
    (CleanRecordObservation.rightInside_eq rows clauses designated record x hevent)

end
end PerfectCompleteness.CleanRecordDecoderInput

end

end OAI
