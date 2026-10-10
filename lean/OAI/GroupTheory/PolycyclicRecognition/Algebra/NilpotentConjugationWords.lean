import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentRationalConjugation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ActionWordFiltration

namespace OAI

/-! # A common dimension bound for mixed conjugation differences

Nilpotence of the group annihilates sufficiently long products even when
successive conjugating elements differ. The action filtration improves this
bound to the rational rank of the abelian normal subgroup.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative TensorProduct commutatorElement

variable {G : Type} [Group G] (H : Subgroup G) [H.Normal] [IsMulCommutative H]

theorem integralConjugationWord_mem (w : List G) (a : Additive H) :
    ((((w.map (integralConjugationDifference H)).prod) a).toMul : G) ∈
      (⊤ : Subgroup G).lowerCentralSeries w.length := by
  induction w with
  | nil => exact Subgroup.mem_top _
  | cons g w ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply,
      integralConjugationDifference_apply, List.length_cons,
      Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) ih

theorem integralConjugationWord_zero [Group.IsNilpotent G]
    (w : List G) (hw : w.length = Group.nilpotencyClass G) :
    (w.map (integralConjugationDifference H)).prod = 0 := by
  apply LinearMap.ext
  intro a
  have h := integralConjugationWord_mem H w a
  rw [hw, Subgroup.lowerCentralSeries_nilpotencyClass, Subgroup.mem_bot] at h
  apply Additive.toMul.injective
  apply Subtype.val_injective
  exact h

theorem rationalConjugationWord_baseChange (w : List G) :
    actionOperatorWord (fun g => (rationalConjugation H g).toLinearMap - 1) w =
      ((w.map (integralConjugationDifference H)).prod).baseChange ℚ := by
  induction w with
  | nil => simp [actionOperatorWord]
  | cons g w ih =>
    change ((rationalConjugation H g).toLinearMap - 1) *
      actionOperatorWord (fun g => (rationalConjugation H g).toLinearMap - 1) w = _
    rw [ih, rationalConjugationDifference_baseChange, ← LinearMap.baseChange_mul]
    rfl

theorem rationalConjugationWord_zero_at_rank [Group.IsNilpotent G]
    [Module.Finite ℚ (RationalAbelianSpace H)] :
    ∀ w : List G, w.length = Module.finrank ℚ (RationalAbelianSpace H) →
      actionOperatorWord (fun g => (rationalConjugation H g).toLinearMap - 1) w = 0 := by
  apply actionOperatorWord_zero_at_finrank
  refine ⟨Group.nilpotencyClass G, fun w hw => ?_⟩
  rw [rationalConjugationWord_baseChange, integralConjugationWord_zero H w hw,
    LinearMap.baseChange_zero]

end PolycyclicRecognition

end

end OAI
