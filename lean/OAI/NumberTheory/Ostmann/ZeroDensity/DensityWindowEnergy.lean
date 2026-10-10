import OAI.NumberTheory.Ostmann.ZeroDensity.DensityLocalizedPolynomial

namespace OAI

/-! # A compact Fourier window controls the height mean square -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators SchwartzMap FourierTransform

 theorem density_schwartz_square_integrable (W : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ => ‖W x‖ ^ 2) :=
  (memLp_two_iff_integrable_sq_norm W.continuous.aestronglyMeasurable).mp (W.memLp 2)

 theorem density_height_window_bound {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (c h T : ℝ) (hc : 0 < c) (hh : 0 < h)
    (hwindow : h * T ≤ 1) (hW : ∀ t, |t| ≤ 1 → c ≤ ‖𝓕 W t‖)
    (a : ι → ℂ) (freq : ι → ℝ) :
    h ^ 2 * c ^ 2 * (∫ t in Icc (-T) T,
      ‖∑ j, a j * realAdditivePhase (-(freq j * t))‖ ^ 2) ≤
        ∫ x : ℝ, ‖∑ j, a j * W ((x - freq j) / h)‖ ^ 2 := by
  let P := densityLocalizedPolynomial W h hh a freq
  have hi : Integrable (fun t : ℝ => ‖𝓕 P t‖ ^ 2) :=
    density_schwartz_square_integrable (𝓕 P)
  have hl : IntegrableOn (fun t : ℝ => h ^ 2 * c ^ 2 *
      ‖∑ j, a j * realAdditivePhase (-(freq j * t))‖ ^ 2) (Icc (-T) T) := by
    apply ContinuousOn.integrableOn_Icc
    apply Continuous.continuousOn
    unfold realAdditivePhase
    fun_prop
  have hm : (∫ t in Icc (-T) T, h ^ 2 * c ^ 2 *
      ‖∑ j, a j * realAdditivePhase (-(freq j * t))‖ ^ 2) ≤
        ∫ t in Icc (-T) T, ‖𝓕 P t‖ ^ 2 := by
    apply setIntegral_mono_on hl hi.integrableOn measurableSet_Icc
    intro t ht
    exact density_localized_pointwise_bound W c h T hc hh hwindow hW a freq t
      (abs_le.mpr ht)
  rw [integral_const_mul] at hm
  have hb := setIntegral_le_integral (s := Icc (-T) T) hi
    (Filter.Eventually.of_forall (fun t => sq_nonneg ‖𝓕 P t‖))
  apply (hm.trans hb).trans_eq
  rw [SchwartzMap.integral_norm_sq_fourier]
  apply integral_congr_ae
  filter_upwards with x
  rw [show P = densityLocalizedPolynomial W h hh a freq from rfl,
    densityLocalizedPolynomial_apply]

 theorem density_shifted_window_square (W : 𝓢(ℝ, ℂ)) (h : ℝ) (hh : 0 < h) (v : ℝ) :
    (∫ x : ℝ, ‖W ((x - v) / h)‖ ^ 2) = h * ∫ x : ℝ, ‖W x‖ ^ 2 := by
  have ht := integral_add_right_eq_self (μ := volume)
    (fun x : ℝ => ‖W (x / h)‖ ^ 2) (-v)
  simp only [sub_eq_add_neg] at ⊢
  rw [ht]
  simpa only [abs_of_pos hh, smul_eq_mul] using
    Measure.integral_comp_div (fun x : ℝ => ‖W x‖ ^ 2) h

 theorem density_shifted_window_integrable (W : 𝓢(ℝ, ℂ)) (h : ℝ)
    (hh : 0 < h) (v : ℝ) :
    Integrable (fun x : ℝ => ‖W ((x - v) / h)‖ ^ 2) := by
  have hi := density_schwartz_square_integrable
    ((positiveDilate W h⁻¹ (inv_pos.mpr hh)).compSubConstCLM ℂ v)
  simpa only [SchwartzMap.compSubConstCLM_apply, positiveDilate_apply,
    div_eq_inv_mul] using hi

 theorem density_localized_square_integrable {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (h : ℝ) (hh : 0 < h) (a : ι → ℂ) (freq : ι → ℝ) :
    Integrable (fun x : ℝ => ‖∑ j, a j * W ((x - freq j) / h)‖ ^ 2) := by
  simpa only [densityLocalizedPolynomial_apply] using
    density_schwartz_square_integrable (densityLocalizedPolynomial W h hh a freq)

end Ostmann

end OAI
