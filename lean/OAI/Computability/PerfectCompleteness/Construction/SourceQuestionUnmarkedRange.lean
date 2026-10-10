import OAI.Computability.PerfectCompleteness.Decoding.ProjectedNativeCollision
import OAI.Computability.PerfectCompleteness.Foundations.CutNativeForms
import OAI.Computability.PerfectCompleteness.Sampling.SourceChildMarkedLaw

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionUnmarkedRange

open scoped Classical
open RecursiveSpaces TreeSourceSpaces SourceChildKernel

noncomputable section

variable {branch : Nat → Nat} {height t v m : Nat}

private theorem unmarked_range_cast
    {left native right : Slots branch (height + 1) → Fin t → MixedSupport.Slot}
    (h : left = native)
    (p : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (mask : Fin (branch height) → Bool)
    (hin : ChildUnmarkedSpace.space left mask ≤ LinearMap.range (HPullback p)) :
    ChildUnmarkedSpace.space native mask ≤
      LinearMap.range (HPullback (CutNativeForms.projectionCast h rfl p)) := by
  cases h
  exact hin

variable (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch height) → Slots branch height)
  (q : SourceChildMarkedLaw.Questions (branch := branch) (n := height) (t := t) (m := m))
  (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := height) (t := t))

theorem leftSlots_eq :
    parentLeftSlots clauses designated (SourceQuestionKernelJoint.sources designated q choices) =
      SourceChildMarkedLaw.questionSlots clauses q :=
  SourceQuestionPositionSplit.parentLeftSlots_join clauses designated q _

variable {C : Type*} [Fintype C]
  (raw : (i : Fin (branch height)) → Raw (C := C) (t := t) rows clauses designated i)

def projection : ∀ s k, MixedSupport.Projection
    (SourceChildMarkedLaw.questionSlots clauses q s k)
    (parentRightSlots rows clauses designated
      (SourceQuestionKernelJoint.sources designated q choices) raw s k) :=
  CutNativeForms.projectionCast (leftSlots_eq clauses designated q choices) rfl
    (parentProjection rows clauses designated
      (SourceQuestionKernelJoint.sources designated q choices) raw)

theorem unmarked_le_range :
    ChildUnmarkedSpace.space (SourceChildMarkedLaw.questionSlots clauses q)
        (fun i => rawProjected rows clauses designated i (raw i)) ≤
      LinearMap.range (HPullback (projection rows clauses designated q choices raw)) := by
  exact unmarked_range_cast (leftSlots_eq clauses designated q choices)
    (parentProjection rows clauses designated
      (SourceQuestionKernelJoint.sources designated q choices) raw)
    (fun i => rawProjected rows clauses designated i (raw i))
    (ProjectedNativeCollision.parent_unmarked_le_range clauses designated
      (SourceQuestionKernelJoint.sources designated q choices) raw)

end
end PerfectCompleteness.SourceQuestionUnmarkedRange

end

end OAI
