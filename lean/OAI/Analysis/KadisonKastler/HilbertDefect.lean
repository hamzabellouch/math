import OAI.Analysis.KadisonKastler.HilbertContractionFactor
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

namespace OAI

/-! # The defect isometry of a Hilbert-space contraction

The positive square root of `1 - A* A` completes a contraction to an
isometry. This is the geometric ingredient in finite block completion.
-/

namespace KadisonKastler

open scoped InnerProductSpace

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def operatorDefect (A : E →L[ℂ] F) : E →L[ℂ] E :=
  CFC.sqrt (1 - A.adjoint.comp A)

theorem operatorDefect_selfadjoint (A : E →L[ℂ] F) :
    IsSelfAdjoint (operatorDefect A) := (CFC.sqrt_nonneg _).isSelfAdjoint

theorem adjoint_comp_self_le_one (A : E →L[ℂ] F) (hA : ‖A‖ ≤ 1) :
    A.adjoint.comp A ≤ 1 := by
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr
      (ContinuousLinearMap.isPositive_adjoint_comp_self A))).mp
  rw [ContinuousLinearMap.norm_adjoint_comp_self]
  nlinarith [norm_nonneg A]

theorem operatorDefect_sq (A : E →L[ℂ] F) (hA : ‖A‖ ≤ 1) :
    operatorDefect A * operatorDefect A = 1 - A.adjoint.comp A :=
  CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr (adjoint_comp_self_le_one A hA))

theorem norm_operatorDefect_sq (A : E →L[ℂ] F) (hA : ‖A‖ ≤ 1) (x : E) :
    ‖operatorDefect A x‖ ^ 2 = ‖x‖ ^ 2 - ‖A x‖ ^ 2 := by
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]
  have he : (operatorDefect A).adjoint.comp (operatorDefect A) =
      1 - A.adjoint.comp A := by
    change star (operatorDefect A) * operatorDefect A = _
    rw [(operatorDefect_selfadjoint A).star_eq, operatorDefect_sq A hA]
  rw [he]
  simp only [sub_apply, one_apply_eq_self, inner_sub_right, map_sub]
  rw [inner_self_eq_norm_sq, ← ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]

/-- The first component is the original contraction; the second accounts
for exactly the lost squared norm. -/
def defectIsometry (A : E →L[ℂ] F) (hA : ‖A‖ ≤ 1) :
    E →ₗᵢ[ℂ] WithLp 2 (F × E) where
  toFun x := WithLp.toLp 2 (A x, operatorDefect A x)
  map_add' x y := by simp [← WithLp.toLp_add]
  map_smul' c x := by simp [← WithLp.toLp_smul]
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖A x‖ ^ 2 + ‖operatorDefect A x‖ ^ 2 = ‖x‖ ^ 2
    rw [norm_operatorDefect_sq A hA]
    ring

end

end KadisonKastler

end OAI
