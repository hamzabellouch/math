import OAI.MeasureTheory.Falconer.Fourier.DistanceFrequencyMajorant
import OAI.MeasureTheory.Falconer.Fourier.DistanceSincCollision

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem distanceBandKernel_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    {A : ℝ} (hA : 0 ≤ A) :
    Integrable (fun z : ℝ × ℝ => 1/(1+A*|z.1-z.2|)^2) (μ.prod μ) := by
  apply (integrable_const (1:ℝ)).mono (by apply Measurable.aestronglyMeasurable; fun_prop)
  filter_upwards with z
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),norm_one]
  apply (div_le_one (by positivity : 0 < (1+A*|z.1-z.2|)^2)).mpr
  nlinarith [mul_nonneg hA (abs_nonneg (z.1-z.2))]

theorem distance_band_kernel_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {A : ℝ} (hA : 0 < A) :
    (∫ r in Icc (-A) A, ‖charFun μ r‖^2) ≤
      32*A * ∫ z : ℝ × ℝ, 1/(1+A*|z.1-z.2|)^2 ∂μ.prod μ := by
  have h := mul_le_mul_of_nonneg_left (frequency_band_le_sinc μ A) hA.le
  rw [integral_scale_Icc (fun r => ‖charFun μ r‖^2) hA (by norm_num : (0:ℝ) ≤ 1)] at h
  simp only [mul_one] at h
  have he : (∫ s, distanceSincKernel 2 (A*s) ∂distanceDifferenceMeasure μ) =
      ∫ z : ℝ × ℝ, distanceSincKernel 2 (A*(z.1-z.2)) ∂μ.prod μ :=
    integral_map_of_stronglyMeasurable (by fun_prop)
      (((continuous_distanceSincKernel 2).comp (continuous_const.mul continuous_id)).stronglyMeasurable)
  rw [he] at h
  have hi : Integrable (fun z : ℝ × ℝ => distanceSincKernel 2 (A*(z.1-z.2))) (μ.prod μ) := by
    apply (integrable_const (1:ℝ)).mono (by
      exact ((continuous_distanceSincKernel 2).comp
        (continuous_const.mul (continuous_fst.sub continuous_snd))).aestronglyMeasurable)
    filter_upwards with z
    rw [Real.norm_eq_abs,abs_of_nonneg (distanceSincKernel_nonneg _ _),norm_one]
    exact distanceSincKernel_le_one _ _
  have hk := integral_mono hi ((distanceBandKernel_integrable μ hA.le).const_mul 4)
    (show ∀ z : ℝ × ℝ, distanceSincKernel 2 (A*(z.1-z.2)) ≤
      4*(1/(1+A*|z.1-z.2|)^2) from by
      intro z
      simpa only [abs_mul,abs_of_pos hA,mul_one_div] using
        distanceSincKernel_two_decay (A*(z.1-z.2)))
  rw [integral_const_mul] at hk
  have hh := mul_le_mul_of_nonneg_left hk (show 0 ≤ A*8 by positivity)
  nlinarith

theorem distance_band_kernel_bound_ennreal (μ : Measure ℝ) [IsFiniteMeasure μ]
    {A : ℝ} (hA : 0 < A) :
    ENNReal.ofReal (∫ r in Icc (-A) A, ‖charFun μ r‖^2) ≤
      ENNReal.ofReal (32*A) *
        ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+A*|z.1-z.2|)^2) ∂μ.prod μ := by
  have h := ENNReal.ofReal_le_ofReal (distance_band_kernel_bound μ hA)
  rw [ENNReal.ofReal_mul (by positivity),ofReal_integral_eq_lintegral_ofReal
    (distanceBandKernel_integrable μ hA.le) (Filter.Eventually.of_forall (fun _ => by positivity))] at h
  exact h

end PlanarFalconer

end OAI
