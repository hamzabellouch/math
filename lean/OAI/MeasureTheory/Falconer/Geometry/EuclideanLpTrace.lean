import OAI.MeasureTheory.Falconer.Geometry.EuclideanTrace
import OAI.MeasureTheory.Falconer.Graphs.FiberTrace

namespace OAI

/-! The fixed-dimensional Sobolev trace estimate used for radial densities. -/

namespace Falconer
open Set MeasureTheory PlanarFalconer
open scoped ENNReal FourierTransform SchwartzMap

theorem euclidean_dual_test_bound {n : ℕ} (η : Measure (Space n)) [IsFiniteMeasure η]
    (f : 𝓢(Space n, ℂ)) (h : Space n → ℝ≥0∞) (hh : Measurable h)
    {D p q u t : ℝ} (hpq : p.HolderConjugate q) (hu : 0 < u) (hun : u < n)
    (hD : 0 < D) (hupt : u*p < t) (hnorm : (∫⁻ x, h x^q ∂η) = 1)
    (hdiam : ∀ᵐ z : Space n × Space n ∂η.prod η, dist z.1 z.2 ≤ D) :
    (ENNReal.ofReal (sourceEnergyConstant n u))^(1/2 : ℝ) *
      ENNReal.ofReal (‖∫ x, f x ∂η.withDensity h‖) ≤
      (ENNReal.ofReal (D^(t-u*p)) * rieszEnergyOn η t)^(1/(2*p)) *
        (∫⁻ ξ : Space n, ENNReal.ofReal (‖𝓕 f ξ‖^2 * ‖ξ‖^((n : ℝ)-u)))^(1/2 : ℝ) := by
  let := finiteMeasure_normalized_density η h hh hpq hnorm
  have hpair := euclidean_fourier_pairing (η.withDensity h) f hu hun
  have he := density_energy_of_diameter η h hh hpq hu hD hupt hnorm hdiam
  apply hpair.trans
  apply mul_le_mul_left
  have hr := ENNReal.rpow_le_rpow he (by norm_num : (0 : ℝ) ≤ 1/2)
  rw [← ENNReal.rpow_mul] at hr
  convert hr using 1
  congr 1
  ring

noncomputable def euclideanComplexSchwartz {n : ℕ} (f : 𝓢(Space n, ℝ)) : 𝓢(Space n, ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM f

theorem euclidean_lp_trace {n : ℕ} (η : Measure (Space n)) [IsFiniteMeasure η]
    (f : 𝓢(Space n, ℝ)) (hf : ∀ x, 0 ≤ f x) {D p q u t : ℝ}
    (hpq : p.HolderConjugate q) (hu : 0 < u) (hun : u < n)
    (hD : 0 < D) (hupt : u*p < t)
    (hdiam : ∀ᵐ z : Space n × Space n ∂η.prod η, dist z.1 z.2 ≤ D) :
    (ENNReal.ofReal (sourceEnergyConstant n u))^(1/2 : ℝ) *
      eLpNorm (fun x => f x) (ENNReal.ofReal p) η ≤
      (ENNReal.ofReal (D^(t-u*p)) * rieszEnergyOn η t)^(1/(2*p)) *
        (∫⁻ ξ : Space n, ENNReal.ofReal
          (‖𝓕 (euclideanComplexSchwartz f) ξ‖^2 * ‖ξ‖^((n : ℝ)-u)))^(1/2 : ℝ) := by
  let F : Space n → ℝ≥0∞ := fun x => ENNReal.ofReal (f x)
  let N : ℝ≥0∞ := ∫⁻ x, F x^p ∂η
  have hnorm : eLpNorm (fun x => f x) (ENNReal.ofReal p) η = N^(1/p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_pos.mpr hpq.pos).ne' ENNReal.ofReal_ne_top
        f.continuous.aestronglyMeasurable,
      ENNReal.toReal_ofReal hpq.nonneg]
    congr 1
    apply lintegral_congr
    intro x
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hf x)]
  have hfinite := ((f.memLp_top η).mono_exponent
    (show ENNReal.ofReal p ≤ ∞ from le_top)).eLpNorm_lt_top
  change eLpNorm (fun x => f x) (ENNReal.ofReal p) η < ∞ at hfinite
  rw [hnorm] at hfinite
  have hNtop : N ≠ ∞ := by
    intro ht
    rw [ht, ENNReal.top_rpow_of_pos (one_div_pos.mpr hpq.pos)] at hfinite
    exact lt_irrefl _ hfinite
  rw [hnorm]
  by_cases hN0 : N = 0
  · rw [hN0, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hpq.pos), mul_zero]
    exact bot_le
  obtain ⟨h, hh, hq, hdual⟩ := exists_normalized_dual_density η F
    (by dsimp [F]; fun_prop) hpq hN0 hNtop
  let := finiteMeasure_normalized_density η h hh hpq hq
  have hi : Integrable (fun x => f x) (η.withDensity h) :=
    ((f.memLp_top (η.withDensity h)).mono_exponent
      (show (1 : ℝ≥0∞) ≤ ∞ from le_top)).integrable le_rfl
  have hnormIntegral : ENNReal.ofReal (‖∫ x, euclideanComplexSchwartz f x ∂η.withDensity h‖) =
      N^(1/p) := by
    change ENNReal.ofReal (‖∫ x, (f x : ℂ) ∂η.withDensity h‖) = _
    rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg hf),
      ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf),
      lintegral_withDensity_eq_lintegral_mul _ hh (by fun_prop)]
    rw [← hdual]
    apply lintegral_congr
    intro x
    exact mul_comm _ _
  have hb := euclidean_dual_test_bound η (euclideanComplexSchwartz f) h hh
    hpq hu hun hD hupt hq hdiam
  rwa [hnormIntegral] at hb

end Falconer

end OAI
