import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousYSpace
import OAI.MathematicalPhysics.DefocusingNLS.Linear.LocalizationFourierEnergy

namespace OAI

/-! # Exact norm in the homogeneous completion

This identifies the weighted Fourier L² norm with the manuscript's two
homogeneous Sobolev energies, including the radian Plancherel constant.
-/

open MeasureTheory
open scoped SchwartzMap ENNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem integral_homogeneousFourierMeasure (a k : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (g : E → ℝ)
    (hlow : Integrable (fun ξ => ‖ξ‖ ^ (2 * (6 - a)) * g ξ))
    (hhigh : Integrable (fun ξ => ‖ξ‖ ^ (2 * k) * g ξ)) :
    (∫ ξ, g ξ ∂homogeneousFourierMeasure a k) =
      ((2 * Real.pi) ^ (12 : ℕ))⁻¹ *
        ((∫ ξ, ‖ξ‖ ^ (2 * (6 - a)) * g ξ) + (∫ ξ, ‖ξ‖ ^ (2 * k) * g ξ)) := by
  unfold homogeneousFourierMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (continuous_homogeneousFourierWeight a k ha1 hk).measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (homogeneousFourierWeight_nonneg a k _), smul_eq_mul]
  have heq (ξ : E) : homogeneousFourierWeight a k ξ * g ξ =
      ((2 * Real.pi) ^ (12 : ℕ))⁻¹ *
        (‖ξ‖ ^ (2 * (6 - a)) * g ξ + ‖ξ‖ ^ (2 * k) * g ξ) := by
    unfold homogeneousFourierWeight
    ring
  simp_rw [heq]
  rw [integral_const_mul, integral_add hlow hhigh]

private theorem integrable_homogeneousSchwartz (s : ℝ) (hs : 0 ≤ s) (χ : 𝓢(E, ℂ)) :
    Integrable (fun ξ => ‖ξ‖ ^ (2 * s) * ‖radianFourierKernel χ ξ‖ ^ 2) := by
  have h := integrable_localizedFourierPolynomial_energy s 1 hs zero_lt_one χ {0} (fun _ => 1)
  have heq : localizedFourierPolynomial 1 χ {0} (fun _ => 1) = (χ : E → ℂ) := by
    funext y
    simp [localizedFourierPolynomial]
  rw [heq] at h
  simpa only [radianFourierKernel_apply] using h

/-- The norm of the dense Schwartz embedding is exactly the norm defining Y. -/
theorem homogeneousSchwartzEmbedding_norm_sq (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (χ : 𝓢(E, ℂ)) :
    ‖homogeneousSchwartzEmbedding a k ha ha1 hk χ‖ ^ 2 =
      ((2 * Real.pi) ^ (12 : ℕ))⁻¹ *
        (homogeneousFourierEnergy (6 - a) χ + homogeneousFourierEnergy k χ) := by
  let := homogeneousFourierMeasure_temperate a k ha ha1 hk
  rw [homogeneousSchwartzEmbedding_apply]
  have hn := SchwartzMap.norm_toLp' (f := radianFourierKernel χ)
    (μ := homogeneousFourierMeasure a k) (p := 2) (by norm_num) (by norm_num)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hn
  have hn' : ‖(radianFourierKernel χ).toLp 2 (homogeneousFourierMeasure a k)‖ =
      Real.sqrt (∫ ξ, ‖radianFourierKernel χ ξ‖ ^ 2 ∂homogeneousFourierMeasure a k) := by
    simpa only [Real.sqrt_eq_rpow, one_div] using hn
  rw [hn', Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))]
  rw [integral_homogeneousFourierMeasure a k ha1 hk _
    (integrable_homogeneousSchwartz (6 - a) (by linarith) χ)
    (integrable_homogeneousSchwartz k (by linarith) χ)]
  simp only [homogeneousFourierEnergy, radianFourierKernel_apply]

end DefocusingNLS

end OAI
