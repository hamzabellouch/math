import OAI.Analysis.OperatorAlgebra.IsometricCornerOperators

namespace OAI

/-! Normalized vector states under isometric corner compression. -/
noncomputable section
open scoped InnerProductSpace
namespace WeakPureInfiniteness

variable {K H : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma inner_normalized_corner (V : K →ₗᵢ[ℂ] H) (z : H) (a : K →L[ℂ] K) :
    (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * inner ℂ z (isometricCornerLift V a z) =
      inner ℂ (((‖z‖⁻¹ : ℝ) : ℂ) • V.toContinuousLinearMap.adjoint z)
        (a (((‖z‖⁻¹ : ℝ) : ℂ) • V.toContinuousLinearMap.adjoint z)) := by
  have hi : inner ℂ z (isometricCornerLift V a z) =
      inner ℂ (V.toContinuousLinearMap.adjoint z)
        (a (V.toContinuousLinearMap.adjoint z)) :=
    (ContinuousLinearMap.adjoint_inner_left V.toContinuousLinearMap _ z).symm
  have hc (r : ℝ) : (((r ^ 2)⁻¹ : ℝ) : ℂ) = ((r⁻¹ : ℝ) : ℂ) * ((r⁻¹ : ℝ) : ℂ) := by
    rw [← inv_pow, pow_two, Complex.ofReal_mul]
  rw [hi, map_smul, inner_smul_left, inner_smul_right]
  simp only [Complex.conj_ofReal]
  rw [hc]
  exact mul_assoc _ _ _

end WeakPureInfiniteness

end

end OAI
