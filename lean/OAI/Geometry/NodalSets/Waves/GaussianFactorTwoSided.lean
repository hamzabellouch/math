import OAI.Geometry.NodalSets.Waves.GaussianFactorBound

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
local notation "E" => EuclideanSpace ℝ ι

lemma exists_gaussian_factor_two_sided (T : F →L[ℝ] E) (a B : ℝ)
    (ha : 0 < a) (hB : 0 ≤ B)
    (hlo : ∀ v : E, a*‖v‖^2 ≤ ‖T.adjoint v‖^2)
    (hhi : ∀ v : E, ‖T.adjoint v‖^2 ≤ B^2*‖v‖^2) :
    ∃ L : E ≃L[ℝ] E,
      (stdGaussian F).map T = (stdGaussian E).map L ∧
      ‖L.symm.toContinuousLinearMap‖ ≤ (Real.sqrt a)⁻¹ ∧ ‖L.toContinuousLinearMap‖ ≤ B := by
  let L := (LinearEquiv.ofBijective (covarianceFactor T).toLinearMap
    (covarianceFactor_bijective T a ha hlo)).toContinuousLinearEquiv
  refine ⟨L,gaussian_covariance_factorization T,?_,?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    have hb := covarianceFactor_lower T a ha hlo (L.symm v)
    change Real.sqrt a*‖L.symm v‖ ≤ ‖L (L.symm v)‖ at hb
    rw [L.apply_symm_apply] at hb
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ (Real.sqrt_pos.mpr ha)).mpr (by simpa [mul_comm] using hb)
  · apply ContinuousLinearMap.opNorm_le_bound _ hB
    intro v
    change ‖covarianceFactor T v‖ ≤ B*‖v‖
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mp
    rw [covarianceFactor_norm_sq,mul_pow]
    exact hhi v

end
end Yau.Probability

end OAI
