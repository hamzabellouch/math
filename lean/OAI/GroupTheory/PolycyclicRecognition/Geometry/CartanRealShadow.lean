import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightRotationDerivation
import Mathlib.Algebra.Lie.SemiDirect

namespace OAI

/-! # The real shadow Lie algebra

Removing only the imaginary semisimple Cartan action gives a genuine Lie
algebra on the original vector space. Its bracket is obtained from a closed
graph in the derivation semidirect sum, so the Jacobi identity is inherited.
-/

noncomputable section
namespace PolycyclicRecognition
open LieAlgebra Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

/-- The graph of minus the imaginary semisimple derivation. -/
def cartanRealShadowSubalgebra :
    LieSubalgebra ℝ (L ⋊⁅(LieHom.id : LieDerivation ℝ L L →ₗ⁅ℝ⁆ LieDerivation ℝ L L)⁆
      LieDerivation ℝ L L) where
  carrier := {p | p.right = -T.weightImaginaryAction H p.left}
  zero_mem' := by simp
  add_mem' {p q} hp hq := by
    change p.right + q.right = -T.weightImaginaryAction H (p.left+q.left)
    rw [hp,hq,map_add,neg_add]
  smul_mem' r {p} hp := by
    change r • p.right = -T.weightImaginaryAction H (r • p.left)
    rw [hp,map_smul,smul_neg]
  lie_mem' {p q} hp hq := by
    change ⁅p.right,q.right⁆ = -T.weightImaginaryAction H
      (⁅p.left,q.left⁆ + p.right q.left - q.right p.left)
    rw [hp,hq]
    simp only [neg_lie,lie_neg,T.weightImaginaryAction_commute H,
      LieDerivation.neg_apply,map_add,map_sub,map_neg,
      T.weightImaginaryAction_lie H,T.weightImaginaryAction_annihilate H,
      neg_zero,add_zero,sub_zero]

abbrev CartanRealShadow := cartanRealShadowSubalgebra T H

/-- Only multiplication changes: the real vector space is unchanged. -/
def cartanRealShadowEquiv : L ≃ₗ[ℝ] CartanRealShadow T H where
  toFun x := ⟨⟨x,-T.weightImaginaryAction H x⟩,rfl⟩
  invFun p := p.val.left
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    apply SemiDirectSum.ext
    · rfl
    · exact p.property.symm
  map_add' x y := by
    apply Subtype.ext
    apply SemiDirectSum.ext
    · rfl
    · change -T.weightImaginaryAction H (x+y) =
        -T.weightImaginaryAction H x + -T.weightImaginaryAction H y
      rw [map_add,neg_add]
  map_smul' r x := by
    apply Subtype.ext
    apply SemiDirectSum.ext
    · rfl
    · change -T.weightImaginaryAction H (r • x) = r • -T.weightImaginaryAction H x
      rw [map_smul,smul_neg]

instance : FiniteDimensional ℝ (CartanRealShadow T H) :=
  (cartanRealShadowEquiv T H).finiteDimensional

/-- Exact bracket after removing the imaginary semisimple action. -/
theorem cartanRealShadow_bracket (x y : L) :
    (cartanRealShadowEquiv T H).symm ⁅cartanRealShadowEquiv T H x,
      cartanRealShadowEquiv T H y⁆ =
      ⁅x,y⁆ - T.weightImaginaryAction H x y + T.weightImaginaryAction H y x := by
  change ⁅x,y⁆ + (-T.weightImaginaryAction H x) y - (-T.weightImaginaryAction H y) x = _
  simp only [LieDerivation.neg_apply]
  abel

/-- The weight quotient of the modified bracket remains abelian. -/
theorem cartanRealShadow_bracket_weight (x y : L) :
    T.weightMap ((cartanRealShadowEquiv T H).symm
      ⁅cartanRealShadowEquiv T H x,cartanRealShadowEquiv T H y⁆) = 0 := by
  rw [cartanRealShadow_bracket,map_add,map_sub,T.weightMap_lie]
  change 0 - T.weightMap (realImaginaryOperator L H _ y) +
    T.weightMap (realImaginaryOperator L H _ x) = 0
  rw [T.weightMap_realImaginaryOperator H,T.weightMap_realImaginaryOperator H]
  simp

end PolycyclicRecognition

end

end OAI
