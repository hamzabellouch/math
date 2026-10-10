import OAI.MeasureTheory.Falconer.Fourier.DistanceFrequencyBox

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem distanceSincKernel_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (u A : ℝ) :
    Integrable (fun s => distanceSincKernel u (A*s)) μ := by
  apply (integrable_const (1:ℝ)).mono
  · exact ((continuous_distanceSincKernel u).comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards with s
    rw [Real.norm_eq_abs,abs_of_nonneg (distanceSincKernel_nonneg _ _),norm_one]
    exact distanceSincKernel_le_one _ _

theorem charFun_sq_integrable_finite (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (A : ℝ) :
    Integrable (fun r => ‖charFun μ (A*r)‖^2) ν := by
  apply (integrable_const ((μ.real univ)^2)).mono
  · exact ((measurable_charFun.comp (measurable_const.mul measurable_id)).norm.pow_const 2).aestronglyMeasurable
  · filter_upwards with r
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le _) 2

theorem distanceSincKernel_spectral_identity (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u : ℝ} (hu : 0 ≤ u) (A : ℝ) :
    (2*u)^2 * (∫ s, distanceSincKernel u (A*s) ∂distanceDifferenceMeasure μ) =
      ∫ r, ‖charFun μ (A*r)‖^2 ∂distanceDifferenceMeasure (distanceFrequencyBox u) := by
  have h := integral_charFun_scale_swap
    (distanceDifferenceMeasure (distanceFrequencyBox u)) (distanceDifferenceMeasure μ) A
  simp only [distanceFrequencyBox_difference_charFun hu,charFun_distanceDifferenceMeasure] at h
  have hr : (∫ s, (2*u)^2 * distanceSincKernel u (A*s) ∂distanceDifferenceMeasure μ) =
      ∫ r, ‖charFun μ (A*r)‖^2 ∂distanceDifferenceMeasure (distanceFrequencyBox u) := by
    apply Complex.ofReal_injective
    simpa only [← Complex.ofReal_pow,integral_complex_ofReal] using h
  rwa [integral_const_mul] at hr

theorem distanceSincKernel_frequency_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u : ℝ} (hu : 0 < u) (A : ℝ) :
    (2*u) * (∫ s, distanceSincKernel u (A*s) ∂distanceDifferenceMeasure μ) ≤
      ∫ r in Icc (-2*u) (2*u), ‖charFun μ (A*r)‖^2 := by
  have hi := charFun_sq_integrable_finite μ (volume.restrict (Icc (-2*u) (2*u))) A
  have hb := integral_mono_measure (distanceFrequencyBox_difference_le_band hu.le)
    (Filter.Eventually.of_forall (fun r => sq_nonneg ‖charFun μ (A*r)‖))
    (hi.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure,ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*u),smul_eq_mul,
    ← distanceSincKernel_spectral_identity μ hu.le A] at hb
  nlinarith

end PlanarFalconer

end OAI
