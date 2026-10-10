import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFresnelCoefficient

namespace OAI

/-! # Removing the damping on the physical test-function side -/

namespace Ostmann

open MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology

private theorem fresnelCoefficient_continuous {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    Continuous (quadraticFresnelCoefficient ε a) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let z : ℂ := (ε : ℂ) + 2 * Complex.I * (a * t : ℝ)
  have hz : z ≠ 0 := by
    intro hh
    have hh' := congrArg Complex.re hh
    simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im] at hh'
    norm_num at hh'
    linarith
  have hzre : z.re = ε := by simp [z]
  have hi : z⁻¹ ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    rw [Complex.inv_re, hzre]
    exact div_pos hε (Complex.normSq_pos.mpr hz)
  have hc : ContinuousAt (fun t' : ℝ => (ε : ℂ) + 2 * Complex.I * (a * t' : ℝ)) t := by
    fun_prop
  have ht : Tendsto (fun t' : ℝ => ((ε : ℂ) + 2 * Complex.I * (a * t' : ℝ))⁻¹)
      (𝓝 t) (𝓝 z⁻¹) := (hc.inv₀ hz).tendsto
  have hh := (continuousAt_cpow_const (b := (1 / 2 : ℂ)) hi).tendsto.comp ht
  change Tendsto (fun t' => quadraticFresnelCoefficient ε a t') (𝓝 t)
    (𝓝 (quadraticFresnelCoefficient ε a t))
  simpa only [Function.comp_def, quadraticFresnelCoefficient, one_div, z] using hh

 theorem quadratic_fresnel_coefficient_integral_limit (ρ : 𝓢(ℝ, ℂ))
    (a : ℝ) (ha : 1 ≤ |a|) (hρ : ∀ t < 1 / 2, ρ t = 0) :
    Tendsto (fun n : ℕ => ∫ t : ℝ,
      quadraticFresnelCoefficient (1 / ((n : ℝ) + 1)) a t * ρ t)
      atTop (𝓝 (∫ t : ℝ, quadraticFresnelCoefficient 0 a t * ρ t)) := by
  apply tendsto_integral_of_dominated_convergence (fun t : ℝ => ‖ρ t‖)
  · intro n
    exact ((fresnelCoefficient_continuous (by positivity) a).mul ρ.continuous).aestronglyMeasurable
  · exact ρ.integrable.norm
  · intro n
    filter_upwards with t
    by_cases ht : t < 1 / 2
    · simp [hρ t ht]
    · rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right
        (quadraticFresnelCoefficient_norm_le _ ha (le_of_not_gt ht))
        (norm_nonneg _)).trans_eq (one_mul _)
  · filter_upwards with t
    by_cases ht : t < 1 / 2
    · simp only [hρ t ht, mul_zero]
      exact tendsto_const_nhds
    · have ha₀ : a ≠ 0 := by
        intro hh
        simp only [hh, abs_zero] at ha
        linarith
      have ht₀ : t ≠ 0 := by linarith
      have hc := (quadraticFresnelCoefficient_continuousAt_zero (mul_ne_zero ha₀ ht₀)).tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      exact hc.mul_const (ρ t)

 theorem quadratic_fresnel_integral (ρ : 𝓢(ℝ, ℂ)) (a : ℝ)
    (ha : 1 ≤ |a|) (hρ : ∀ t < 1 / 2, ρ t = 0) :
    (∫ x : ℝ, 𝓕 ρ (a * x ^ 2)) =
      ∫ t : ℝ, quadraticFresnelCoefficient 0 a t * ρ t := by
  have hleft := quadratic_damped_fourier_integral_limit ρ a ha
  have hright := quadratic_fresnel_coefficient_integral_limit ρ a ha hρ
  have he : (fun n : ℕ => ∫ x : ℝ,
      quadraticGaussianDamping (1 / ((n : ℝ) + 1)) x * 𝓕 ρ (a * x ^ 2)) =
      (fun n : ℕ => ∫ t : ℝ,
        quadraticFresnelCoefficient (1 / ((n : ℝ) + 1)) a t * ρ t) := by
    funext n
    exact quadratic_damped_fresnel ρ (by positivity) a
  rw [he] at hleft
  exact tendsto_nhds_unique hleft hright

end Ostmann

end OAI
