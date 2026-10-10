import OAI.MeasureTheory.Falconer.Graphs.FiberPairing
import OAI.MeasureTheory.Falconer.Graphs.FiberEnergy

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal FourierTransform SchwartzMap

theorem exists_normalized_dual_density {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : X → ℝ≥0∞) (hF : Measurable F) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (hN0 : (∫⁻ x, F x^p ∂μ) ≠ 0) (hNtop : (∫⁻ x, F x^p ∂μ) ≠ ∞) :
    ∃ h : X → ℝ≥0∞, Measurable h ∧ (∫⁻ x, h x^q ∂μ) = 1 ∧
      (∫⁻ x, F x*h x ∂μ) = (∫⁻ x, F x^p ∂μ)^(1/p) := by
  let N := ∫⁻ x, F x^p ∂μ
  let h : X → ℝ≥0∞ := fun x => F x^(p-1) * N^(-1/q)
  have hp1 : 0 < p-1 := sub_pos.mpr (Real.holderConjugate_iff.mp hpq).1
  have hc : N^(-1/q) ≠ ∞ := ENNReal.rpow_ne_top_of_ne_zero hN0 hNtop
  refine ⟨h, by dsimp [h]; fun_prop, ?_, ?_⟩
  · have he (x : X) : h x^q = F x^p * N⁻¹ := by
      dsimp [h]
      rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.symm.nonneg,
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,hpq.sub_one_mul_conj]
      rw [show (-1/q)*q = -1 by field_simp [hpq.symm.pos.ne'], ENNReal.rpow_neg_one]
    simp_rw [he]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hN0),
      ENNReal.mul_inv_cancel hN0 hNtop]
  · have he (x : X) : F x*h x = F x^p * N^(-1/q) := by
      dsimp [h]
      have hr := ENNReal.rpow_add_of_nonneg (x := F x) 1 (p-1) zero_le_one hp1.le
      rw [show (1 : ℝ)+(p-1)=p by ring, ENNReal.rpow_one] at hr
      rw [← mul_assoc, ← hr]
    simp_rw [he]
    rw [lintegral_mul_const' _ _ hc]
    change N * N^(-1/q) = N^(1/p)
    conv_lhs => lhs; rw [← ENNReal.rpow_one N]
    rw [← ENNReal.rpow_add _ _ hN0 hNtop]
    congr 1
    have ht := hpq.one_div_add_one_div
    norm_num at ht
    simp only [neg_div,one_div]
    linarith

theorem fiber_dual_test_bound (η : Measure ℝ) [IsFiniteMeasure η]
    (f : 𝓢(ℝ, ℂ)) (h : ℝ → ℝ≥0∞) (hh : Measurable h) {D p q u t : ℝ}
    (hpq : p.HolderConjugate q) (hu : 0 < u) (hu1 : u < 1)
    (hD : 0 < D) (hupt : u*p < t) (hnorm : (∫⁻ x, h x^q ∂η) = 1)
    (hdiam : ∀ᵐ z : ℝ × ℝ ∂η.prod η, dist z.1 z.2 ≤ D) :
    (ENNReal.ofReal (sourceEnergyConstant 1 u))^(1/2 : ℝ) *
      ENNReal.ofReal (‖∫ x, f x ∂η.withDensity h‖) ≤
      (ENNReal.ofReal (D^(t-u*p)) * rieszEnergyOn η t)^(1/(2*p)) *
        (∫⁻ ξ : ℝ, ENNReal.ofReal (‖(𝓕 f) ξ‖^2 * |ξ|^(1-u)))^(1/2 : ℝ) := by
  let := finiteMeasure_normalized_density η h hh hpq hnorm
  have hpair := source_fourier_pairing (η.withDensity h) f hu hu1
  have he := density_energy_of_diameter η h hh hpq hu hD hupt hnorm hdiam
  apply hpair.trans
  apply mul_le_mul_left
  have hr := ENNReal.rpow_le_rpow he (by norm_num : (0 : ℝ) ≤ 1/2)
  rw [← ENNReal.rpow_mul] at hr
  convert hr using 1
  congr 1
  ring

noncomputable def complexSchwartz (f : 𝓢(ℝ, ℝ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM f

theorem source_fiber_lp_bound (η : Measure ℝ) [IsFiniteMeasure η]
    (f : 𝓢(ℝ, ℝ)) (hf : ∀ x, 0 ≤ f x) {D p q u t : ℝ}
    (hpq : p.HolderConjugate q) (hu : 0 < u) (hu1 : u < 1)
    (hD : 0 < D) (hupt : u*p < t)
    (hdiam : ∀ᵐ z : ℝ × ℝ ∂η.prod η, dist z.1 z.2 ≤ D) :
    (ENNReal.ofReal (sourceEnergyConstant 1 u))^(1/2 : ℝ) *
      eLpNorm (fun x => f x) (ENNReal.ofReal p) η ≤
      (ENNReal.ofReal (D^(t-u*p)) * rieszEnergyOn η t)^(1/(2*p)) *
        (∫⁻ ξ : ℝ, ENNReal.ofReal
          (‖(𝓕 (complexSchwartz f)) ξ‖^2 * |ξ|^(1-u)))^(1/2 : ℝ) := by
  let F : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (f x)
  let N : ℝ≥0∞ := ∫⁻ x, F x^p ∂η
  have hnorm : eLpNorm (fun x => f x) (ENNReal.ofReal p) η = N^(1/p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_pos.mpr hpq.pos).ne' ENNReal.ofReal_ne_top
        f.continuous.aestronglyMeasurable,
      ENNReal.toReal_ofReal hpq.nonneg]
    congr 1
    apply lintegral_congr
    intro x
    rw [← ofReal_norm,Real.norm_eq_abs,abs_of_nonneg (hf x)]
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
  · rw [hN0,ENNReal.zero_rpow_of_pos (one_div_pos.mpr hpq.pos),mul_zero]
    exact bot_le
  obtain ⟨h,hh,hq,hdual⟩ := exists_normalized_dual_density η F
    (by dsimp [F]; fun_prop) hpq hN0 hNtop
  let := finiteMeasure_normalized_density η h hh hpq hq
  have hi : Integrable (fun x => f x) (η.withDensity h) :=
    ((f.memLp_top (η.withDensity h)).mono_exponent (show (1 : ℝ≥0∞) ≤ ∞ from le_top)).integrable le_rfl
  have hnormIntegral : ENNReal.ofReal (‖∫ x, (complexSchwartz f) x ∂η.withDensity h‖) = N^(1/p) := by
    change ENNReal.ofReal (‖∫ x, (f x : ℂ) ∂η.withDensity h‖) = _
    rw [integral_complex_ofReal,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg hf),
      ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf),
      lintegral_withDensity_eq_lintegral_mul _ hh (by fun_prop)]
    rw [← hdual]
    apply lintegral_congr
    intro x
    exact mul_comm _ _
  have hb := fiber_dual_test_bound η (complexSchwartz f) h hh hpq hu hu1 hD hupt hq hdiam
  rwa [hnormIntegral] at hb

end PlanarFalconer

end OAI
