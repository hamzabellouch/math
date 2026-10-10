import OAI.Analysis.KadisonKastler.HilbertContractionFactor
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! # Complementary projection of an isometric embedding

The formulas below retain the concrete adjoint of the embedding, as needed
for a contractive lift with prescribed first coordinate.
-/

namespace KadisonKastler

open scoped InnerProductSpace

noncomputable section

variable {E K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def isometryComplement (V : E →ₗᵢ[ℂ] K) : K →L[ℂ] K :=
  1 - V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint

theorem adjoint_isometry_apply (V : E →ₗᵢ[ℂ] K) (x : E) :
    V.toContinuousLinearMap.adjoint (V x) = x := by
  exact congrArg (fun T : E →L[ℂ] E => T x) V.adjoint_comp_self

theorem isometryComplement_adjoint (V : E →ₗᵢ[ℂ] K) :
    (isometryComplement V).adjoint = isometryComplement V := by
  simp [isometryComplement, ContinuousLinearMap.adjoint_one]

theorem adjoint_isometry_complement (V : E →ₗᵢ[ℂ] K) (z : K) :
    V.toContinuousLinearMap.adjoint (isometryComplement V z) = 0 := by
  simp only [isometryComplement, sub_apply, one_apply_eq_self,
    ContinuousLinearMap.comp_apply, map_sub]
  change V.toContinuousLinearMap.adjoint z -
    V.toContinuousLinearMap.adjoint (V (V.toContinuousLinearMap.adjoint z)) = 0
  rw [adjoint_isometry_apply, sub_self]

theorem norm_isometryComplement_sq (V : E →ₗᵢ[ℂ] K) (z : K) :
    ‖isometryComplement V z‖ ^ 2 = ‖z‖ ^ 2 - ‖V.toContinuousLinearMap.adjoint z‖ ^ 2 := by
  change ‖z - V (V.toContinuousLinearMap.adjoint z)‖ ^ 2 = _
  rw [norm_sub_sq (𝕜 := ℂ)]
  have hi : inner ℂ z (V (V.toContinuousLinearMap.adjoint z)) =
      inner ℂ (V.toContinuousLinearMap.adjoint z) (V.toContinuousLinearMap.adjoint z) :=
    (V.toContinuousLinearMap.adjoint_inner_left _ _).symm
  rw [hi, inner_self_eq_norm_sq, V.norm_map]
  ring

theorem isometryComplement_norm_le (V : E →ₗᵢ[ℂ] K) :
    ‖isometryComplement V‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_isometryComplement_sq]
  exact sub_le_self _ (sq_nonneg _)

end

end KadisonKastler

end OAI
