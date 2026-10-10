import OAI.Computability.PerfectCompleteness.Repetition.CleanRecordChildBlocks
import OAI.Computability.PerfectCompleteness.Repetition.CutChildCleanLawLemmas

namespace OAI

section

namespace PerfectCompleteness.CleanRecordObservation

noncomputable section

open scoped Classical
open RecursiveSpaces TreeSourceSpaces SourceQuestionReconstruction

variable {branch : Nat → Nat} {h t v m : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

abbrev Record := CleanRecordChildBlocks.Record (C := C) (t := t) rows clauses designated
abbrev Sample := SourceChildKernel.Sample (C := C) (t := t) rows clauses designated

def observe (x : Sample (C := C) (t := t) rows clauses designated) :
    Record (C := C) (t := t) rows clauses designated :=
  UniformCleanSoundness.observations
    (D := SourceChildKernel.D (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.zero (C := C) (t := t) rows clauses designated) x

theorem event_eq (record : Record (C := C) (t := t) rows clauses designated)
    (x : Sample (C := C) (t := t) rows clauses designated) :
    CleanRecordChildBlocks.event rows clauses designated record x =
      decide (observe rows clauses designated x = record) :=
  congrFun (UniformCleanSoundness.recordEvent_eq
    (D := SourceChildKernel.D (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.zero (C := C) (t := t) rows clauses designated) record) x

@[simp] theorem event_observe (x : Sample (C := C) (t := t) rows clauses designated) :
    CleanRecordChildBlocks.event rows clauses designated
      (observe rows clauses designated x) x = true := by
  rw [event_eq]
  exact decide_eq_true rfl

def leftQuestions (record : Record (C := C) (t := t) rows clauses designated)
    (x : Sample (C := C) (t := t) rows clauses designated) :
    {i : Fin (branch h) // CleanRecordChildBlocks.clean rows clauses designated record i} →
      Fin t → Fin m :=
  fun i k => ((x i.val).1 k).1

def rightQuestions (record : Record (C := C) (t := t) rows clauses designated)
    (x : Sample (C := C) (t := t) rows clauses designated) :
    {i : Fin (branch h) // CleanRecordChildBlocks.clean rows clauses designated record i} →
      Fin t → Fin v :=
  fun i k => SourceClause.occurrenceVariable clauses ((x i.val).1 k)

theorem leftInside_eq (record : Record (C := C) (t := t) rows clauses designated)
    (x : Sample (C := C) (t := t) rows clauses designated)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true) :
    CleanEndpointSlots.leftInside clauses designated
      (CleanRecordChildBlocks.clean rows clauses designated record)
      (CleanRecordChildBlocks.visible rows clauses designated record)
      (leftQuestions rows clauses designated record x) =
    SourceChildKernel.parentLeftSlots clauses designated
      (fun i => ((x i).1, (x i).2.1)) := by
  have h := CleanSourceRecord.reconstructLeft_eq designated
    (D := SourceChildKernel.D (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.zero (C := C) (t := t) rows clauses designated)
    (v := v) record x hevent
  funext s k
  exact congrArg (fun f => SourceKeys.slot clauses (f s.1 s.2 k)) h

theorem rightInside_eq (record : Record (C := C) (t := t) rows clauses designated)
    (x : Sample (C := C) (t := t) rows clauses designated)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true) :
    CleanEndpointSlots.rightInside clauses designated
      (CleanRecordChildBlocks.clean rows clauses designated record)
      (CleanRecordChildBlocks.visible rows clauses designated record)
      (CleanRecordChildBlocks.projected rows clauses designated record)
      (rightQuestions rows clauses designated record x) =
    SourceChildKernel.parentRightSlots rows clauses designated
      (fun i => ((x i).1, (x i).2.1)) (fun i => (x i).2.2) := by
  have h := CleanSourceRecord.reconstructRight_eq designated
    (D := SourceChildKernel.D (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.zero (C := C) (t := t) rows clauses designated)
    clauses record x hevent
  funext s k
  refine (congrArg (fun f => SourceKeys.slot clauses (f s.1 s.2 k)) h).trans ?_
  have hflag : CleanSourceRecord.rawProjected designated
      (D := SourceChildKernel.D (C := C) (t := t) rows clauses designated)
      (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
      s.1 (x s.1).2.2 =
        SourceChildKernel.rawProjected rows clauses designated s.1 (x s.1).2.2 := by
    cases (x s.1).2.2 <;> rfl
  exact (congrArg (fun projected : Bool => SourceKeys.slot clauses
    (rightTuple clauses projected
      (CleanSourceRecord.sourceTree designated
        (D := SourceChildKernel.D (C := C) (t := t) rows clauses designated)
        (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated) x s.1 s.2) k)) hflag).trans
    (SourceChildKernel.mixedSlots_eq_rightTuple clauses designated s.1
      ((x s.1).1, (x s.1).2.1)
      (SourceChildKernel.rawProjected rows clauses designated s.1 (x s.1).2.2) s.2 k).symm

end
end PerfectCompleteness.CleanRecordObservation

end

end OAI
