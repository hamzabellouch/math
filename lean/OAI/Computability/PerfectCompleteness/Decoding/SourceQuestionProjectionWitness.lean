import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionUnmarkedRange
import OAI.Computability.PerfectCompleteness.Foundations.SourceProjectedTag

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionProjectionWitness

noncomputable section

open scoped Classical
open RecursiveSpaces

variable {branch : Nat → Nat} {n t v m : Nat}

private theorem projectionCast_apply_heq
    {left native right : Slots branch (n + 1) → Fin t → MixedSupport.Slot}
    (h : left = native)
    (p : ∀ leaf k, MixedSupport.Projection (left leaf k) (right leaf k))
    (leaf : Slots branch (n + 1)) (k : Fin t) :
    HEq (CutNativeForms.projectionCast h rfl p leaf k) (p leaf k) := by
  cases h
  rfl

private theorem mpr_heq {α β : Sort _} (h : α = β) (x : β) :
    HEq (Eq.mpr h x) x := by
  cases h
  rfl

variable {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)
  (q : SourceQuestionPositionSplit.Questions (branch := branch) (n := n) (t := t) (m := m))
  (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t))
  (raw : (i : Fin (branch n)) → SourceChildKernel.Raw (C := C) (t := t) rows clauses designated i)

theorem projection_observe :
    SourceProjectedTag.projection clauses designated q choices
        (fun i => SourceChildKernel.rawProjected rows clauses designated i (raw i)) =
      SourceQuestionUnmarkedRange.projection rows clauses designated q choices raw := by
  funext leaf k
  have htag : HEq
      (SourceProjectedTag.projection clauses designated q choices
        (fun i => SourceChildKernel.rawProjected rows clauses designated i (raw i)) leaf k)
      (SourceChildKernel.parentProjection rows clauses designated
        (SourceQuestionKernelJoint.sources designated q choices) raw leaf k) := by
    unfold SourceProjectedTag.projection
    dsimp only [id]
    exact mpr_heq _ _
  have hnative := projectionCast_apply_heq
    (SourceQuestionUnmarkedRange.leftSlots_eq clauses designated q choices)
    (SourceChildKernel.parentProjection rows clauses designated
      (SourceQuestionKernelJoint.sources designated q choices) raw) leaf k
  exact eq_of_heq (htag.trans hnative.symm)

end
end PerfectCompleteness.SourceQuestionProjectionWitness

end

end OAI
