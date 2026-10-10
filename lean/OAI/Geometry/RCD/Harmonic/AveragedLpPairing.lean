import OAI.Geometry.RCD.Heat.HeatTimeContinuity

namespace OAI

/-! # Exact averaged kernel pairings with bounded Sobolev densities -/

open Set MeasureTheory Filter
open scoped InnerProductSpace ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk in
/-- The actual averaged kernel pairing is an L2 heat pairing. This also
justifies its initial-time limit without a pointwise kernel limit. -/
theorem kernelAverage_integral_lp {t : ℝ} (ht : 0 < t)
    (A : Set X) (hA : MeasurableSet A) (hAt : μ A ≠ ∞) (f : Lp ℝ 2 μ) :
    (∫ z, kernelAverage μ ker t A z * f z ∂μ) =
      ⟪heatAt μ hQ t (uniformDensityLp μ A hA hAt), f⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [kernelAverage_heatSobolev_coe μ hQ hk ht A hA hAt] with z hz
  rw [heatSobolev_toLp] at hz
  simp only [hz, RCLike.inner_apply, conj_trivial]
  ring

include hk in
/-- The full averaged pairing is integrable down to zero time for L2
densities, including the compact curvature density. -/
theorem kernelAverage_integral_lp_intervalIntegrable_zero
    (A : Set X) (hA : MeasurableSet A) (hAt : μ A ≠ ∞) (f : Lp ℝ 2 μ)
    {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t => ∫ z, kernelAverage μ ker t A z * f z ∂μ) volume 0 T := by
  have hc : Continuous (fun t => ⟪heatAt μ hQ t (uniformDensityLp μ A hA hAt), f⟫_ℝ) :=
    (heatAt_continuous μ hQ _).inner continuous_const
  apply (hc.intervalIntegrable 0 T).congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  have ht' : 0 < t := by
    rw [uIoc_of_le hT] at ht
    exact ht.1
  exact (kernelAverage_integral_lp μ hQ hk ht' A hA hAt f).symm

include hk in
/-- The same pairing is the actual average of the heat-evolved density. -/
theorem kernelAverage_integral_lp_eq_average {t : ℝ} (ht : 0 < t)
    (A : Set X) (hA : MeasurableSet A) (hAt : μ A ≠ ∞) (f : Lp ℝ 2 μ) :
    (∫ z, kernelAverage μ ker t A z * f z ∂μ) =
      (μ.real A)⁻¹ * ∫ z in A, heatAt μ hQ t f z ∂μ := by
  rw [kernelAverage_integral_lp μ hQ hk ht A hA hAt f, heatAt_inner, uniformDensityLp_inner]

include hk in
/-- Each positive-time averaged kernel pairing is an ordinary integrable
product of two L2 representatives. -/
theorem kernelAverage_mul_lp_integrable {t : ℝ} (ht : 0 < t)
    (A : Set X) (hA : MeasurableSet A) (hAt : μ A ≠ ∞) (f : Lp ℝ 2 μ) :
    Integrable (fun z => kernelAverage μ ker t A z * f z) μ := by
  have he := kernelAverage_heatSobolev_coe μ hQ hk ht A hA hAt
  rw [heatSobolev_toLp] at he
  apply (L2.integrable_inner (𝕜 := ℝ) (heatAt μ hQ t (uniformDensityLp μ A hA hAt)) f).congr
  filter_upwards [he] with z hz
  simp only [hz, RCLike.inner_apply, conj_trivial]
  ring

include hk in
/-- The pointwise kernel pairing is also an integrable L2 product. -/
theorem kernel_mul_lp_integrable {t : ℝ} (ht : 0 < t) (x : X) (f : Lp ℝ 2 μ) :
    Integrable (fun z => ker t x z * f z) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (heatKernelRow μ hQ hk t x) f).congr
  filter_upwards [heatKernelRow_coe μ hQ hk ht x] with z hz
  simp only [hz, RCLike.inner_apply, conj_trivial]
  ring

/-- Kernel subtraction is valid for these actual integrable products. -/
theorem kernelAverage_difference_integral_lp {t : ℝ} (ht : 0 < t)
    (A : Set X) (hA : MeasurableSet A) (hAt : μ A ≠ ∞) (x : X) (f : Lp ℝ 2 μ) :
    (∫ z, (kernelAverage μ ker t A z - ker t x z) * f z ∂μ) =
      ⟪heatAt μ hQ t (uniformDensityLp μ A hA hAt), f⟫_ℝ - kernelHeat μ hQ hk t f x := by
  simp_rw [sub_mul]
  rw [integral_sub (kernelAverage_mul_lp_integrable μ hQ hk ht A hA hAt f)
    (kernel_mul_lp_integrable μ hQ hk ht x f),
    kernelAverage_integral_lp μ hQ hk ht A hA hAt f, kernelHeat_eq_integral μ hQ hk ht f x]

include hk in
/-- All positive-time difference pairings with an L2 density are
integrable on compact time intervals. -/
theorem kernelAverage_difference_lp_intervalIntegrable
    (A : Set X) (hA : MeasurableSet A) (hAt : μ A ≠ ∞) (x : X) (f : Lp ℝ 2 μ)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    IntervalIntegrable (fun r => ∫ z, (kernelAverage μ ker r A z - ker r x z) * f z ∂μ)
      volume s t := by
  have ha : Continuous (fun r => ⟪heatAt μ hQ r (uniformDensityLp μ A hA hAt), f⟫_ℝ) :=
    (heatAt_continuous μ hQ _).inner continuous_const
  have hp : ContinuousOn (fun r => kernelHeat μ hQ hk r f x) (Icc s t) :=
    (kernelHeat_continuousOn_time_space μ hQ hk f).comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => ⟨hs.trans_le hr.1, mem_univ _⟩)
  apply ((ha.continuousOn.sub hp).intervalIntegrable_of_Icc hst).congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
  have hr' : 0 < r := by
    rw [uIoc_of_le hst] at hr
    exact hs.trans hr.1
  exact (kernelAverage_difference_integral_lp μ hQ hk hr' A hA hAt x f).symm

end RegularPointCoordinates

end

end OAI
