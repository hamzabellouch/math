import OAI.Computability.PerfectCompleteness.Construction.SourcePhysicalTaggedChildren
import OAI.Computability.PerfectCompleteness.Decoding.SourceQuestionProjectionWitness

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionTaggedProjection

noncomputable section

open scoped Classical
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]

omit [Fintype C] in
private theorem castRaw_apply (rows : Nat → Nat)
    {left native : Slots branch (n + 1) → Fin t → MixedSupport.Slot}
    (h : left = native) (block : CutChildGrouping.Raw (C := C) left rows)
    (i : Fin (branch n)) :
    (cast (congrArg (fun slots => CutChildGrouping.Raw (C := C) slots rows) h) block) i =
      cast (congrArg (fun slots => ChildCallNumbering.Raw (C := C) rows (childSlots slots i)) h)
        (block i) := by
  cases h
  rfl

omit [Fintype C] in
private theorem castRaw_pullback (rows : Nat → Nat)
    {left native right : Slots branch (n + 1) → Fin t → MixedSupport.Slot}
    (h : left = native)
    (p : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (block : CutChildGrouping.Raw (C := C) right rows) :
    cast (congrArg (fun slots => CutChildGrouping.Raw (C := C) slots rows) h)
        (ChildAssemblyProjection.rawPullback rows p block) =
      ChildAssemblyProjection.rawPullback rows (CutNativeForms.projectionCast h rfl p) block := by
  cases h
  rfl

variable (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)
  (q : SourceQuestionPositionSplit.Questions (branch := branch) (n := n) (t := t) (m := m))
  (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t))
  (raw : (i : Fin (branch n)) → SourceChildKernel.Raw (C := C) (t := t) rows clauses designated i)

theorem projection_observe :
    SourceProjectedTag.projection clauses designated q choices
        (fun i => SourceChildKernel.rawProjected rows clauses designated i (raw i)) =
      SourceQuestionUnmarkedRange.projection rows clauses designated q choices raw :=
  SourceQuestionProjectionWitness.projection_observe rows clauses designated q choices raw

theorem markedBlocks_snd_cast :
    (SourceChildMarkedLaw.markedBlocks rows clauses designated q choices raw).2 =
      cast (congrArg (fun slots => CutChildGrouping.Raw (C := C) slots rows)
        (SourceQuestionUnmarkedRange.leftSlots_eq clauses designated q choices))
        (SourceChildKernel.leftChildren rows clauses designated
          (SourceQuestionKernelJoint.sources designated q choices) raw) := by
  funext i
  rw [castRaw_apply rows
    (SourceQuestionUnmarkedRange.leftSlots_eq clauses designated q choices)]
  rfl

theorem markedBlocks_snd :
    (SourceChildMarkedLaw.markedBlocks rows clauses designated q choices raw).2 =
      ChildAssemblyProjection.rawPullback rows
        (SourceProjectedTag.projection clauses designated q choices
          (fun i => SourceChildKernel.rawProjected rows clauses designated i (raw i)))
        (SourcePhysicalTaggedChildren.observe rows clauses designated
          (SourceQuestionKernelJoint.sources designated q choices) raw).2 := by
  rw [projection_observe]
  rw [markedBlocks_snd_cast]
  exact castRaw_pullback rows
    (SourceQuestionUnmarkedRange.leftSlots_eq clauses designated q choices)
    (SourceChildKernel.parentProjection rows clauses designated
      (SourceQuestionKernelJoint.sources designated q choices) raw)
    (SourceChildKernel.rightChildren rows clauses designated
      (SourceQuestionKernelJoint.sources designated q choices) raw)

end
end PerfectCompleteness.SourceQuestionTaggedProjection

end

end OAI
