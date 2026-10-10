import OAI.MeasureTheory.Falconer.Fourier.DistanceSincSpectralIdentity

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem distanceFrequencyBox_two_lower :
    (2:ℝ≥0∞) • volume.restrict (Icc (-1:ℝ) 1) ≤
      distanceDifferenceMeasure (distanceFrequencyBox 2) := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [distanceDifferenceMeasure,Measure.map_apply (by fun_prop) hS,
    Measure.prod_apply (hS.preimage (by fun_prop))]
  have hsub : distanceFrequencyBox 1 ≤ distanceFrequencyBox 2 :=
    Measure.restrict_mono (Ioc_subset_Ioc (by norm_num) (by norm_num)) le_rfl
  calc
    _ = ∫⁻ _x, volume (S ∩ Icc (-1:ℝ) 1) ∂distanceFrequencyBox 1 := by
      rw [lintegral_const,distanceFrequencyBox_mass (by norm_num),
        Measure.smul_apply,Measure.restrict_apply hS,smul_eq_mul]
      norm_num
      exact mul_comm _ _
    _ ≤ ∫⁻ x, distanceFrequencyBox 2 ((fun y : ℝ => x-y) ⁻¹' S) ∂distanceFrequencyBox 1 := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioc] with x hx
      rw [distanceFrequencyBox,Measure.restrict_apply (hS.preimage (by fun_prop))]
      rw [← (volume.measurePreserving_sub_left x).measure_preimage
        (hS.inter measurableSet_Icc).nullMeasurableSet]
      apply measure_mono
      intro y hy
      refine ⟨hy.1,?_,?_⟩ <;> dsimp at * <;> linarith [hy.2.1,hy.2.2,hx.1,hx.2]
    _ ≤ _ := lintegral_mono' hsub (fun _ => le_rfl)

theorem distanceSincKernel_two_decay (s : ℝ) :
    distanceSincKernel 2 s ≤ 4/(1+|s|)^2 := by
  have hden : 0 < (1+|s|)^2 := by positivity
  apply (le_div_iff₀ hden).mpr
  by_cases hs : |s| ≤ 1
  · have h := distanceSincKernel_le_one 2 s
    have hn := distanceSincKernel_nonneg 2 s
    nlinarith [abs_nonneg s,mul_le_mul_of_nonneg_right h (sq_nonneg (1+|s|))]
  · have hs' : 1 < |s| := lt_of_not_ge hs
    have hn : s ≠ 0 := by intro h; norm_num [h] at hs'
    have he : distanceSincKernel 2 s * (2*s)^2 = (Real.sin (2*s))^2 := by
      rw [distanceSincKernel,Real.sinc_of_ne_zero (mul_ne_zero (by norm_num) hn),div_pow]
      field_simp
    have hb : (Real.sin (2*s))^2 ≤ 1 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sin_le_one (2*s)) 2
      simpa only [sq_abs,one_pow] using h
    have hn' := distanceSincKernel_nonneg 2 s
    have hsq : (1+|s|)^2 ≤ 4*s^2 := by nlinarith [sq_abs s]
    have hm := mul_le_mul_of_nonneg_left hsq hn'
    nlinarith

theorem frequency_band_le_sinc (μ : Measure ℝ) [IsFiniteMeasure μ] (A : ℝ) :
    (∫ r in Icc (-1:ℝ) 1, ‖charFun μ (A*r)‖^2) ≤
      8 * ∫ s, distanceSincKernel 2 (A*s) ∂distanceDifferenceMeasure μ := by
  have hi := charFun_sq_integrable_finite μ (distanceDifferenceMeasure (distanceFrequencyBox 2)) A
  have h := integral_mono_measure distanceFrequencyBox_two_lower
    (Filter.Eventually.of_forall (fun r => sq_nonneg ‖charFun μ (A*r)‖)) hi
  rw [integral_smul_measure,smul_eq_mul,ENNReal.toReal_ofNat,
    ← distanceSincKernel_spectral_identity μ (by norm_num : (0:ℝ) ≤ 2) A] at h
  norm_num at h
  linarith

end PlanarFalconer

end OAI
