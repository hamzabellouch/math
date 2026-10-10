import OAI.Geometry.RCD.Heat.KernelDensityTime
import OAI.Geometry.RCD.Sobolev.CutoffErrorEstimates

namespace OAI

/-! # Genuine time integrability for compact L1 sources -/

open Set Metric MeasureTheory Filter
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk in
/-- The spatial average makes any compact L1 source time-integrable at
zero, using only its finite mass and the exact inverse-volume bound. -/
theorem average_density_intervalIntegrable_zero (A : Set X)
    (hA : MeasurableSet A) (hAt : μ A ≠ ∞)
    {g : X → ℝ} (hg : Integrable g μ) {K : Set X} (hK : IsCompact K)
    (hz : ∀ᵐ z ∂μ, z ∉ K → g z = 0) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t => ∫ z, kernelAverage μ ker t A z * g z ∂μ) volume 0 T := by
  let f := fun t => ∫ z, kernelAverage μ ker t A z * g z ∂μ
  have hc : ContinuousOn f (Ioi 0) := average_density_continuousOn_time μ hQ hk A hA hAt hg hK hz
  let D := (μ.real A)⁻¹ * ∫ z, |g z| ∂μ
  have hb (t : ℝ) (ht : 0 < t) : |f t| ≤ D := by
    apply abs_integral_mul_le_of_bound_on μ hg (inv_nonneg.mpr (measureReal_nonneg))
      (S := univ) (Eventually.of_forall fun _ hn => (hn (mem_univ _)).elim)
    intro z _
    rw [abs_of_nonneg (kernelAverage_bounds μ hQ hk ht A z).1]
    exact (kernelAverage_bounds μ hQ hk ht A z).2
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  apply IntegrableOn.of_bound measure_Ioc_lt_top
    ((hc.mono (fun _ ht => ht.1)).aestronglyMeasurable measurableSet_Ioc) D
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  simpa only [Real.norm_eq_abs] using hb t ht.1

include hk in
/-- The difference pairing is integrable on every compact positive-time interval. -/
theorem difference_density_intervalIntegrable (A : Set X)
    (hA : MeasurableSet A) (hbounded : Bornology.IsBounded A) (x : X)
    {g : X → ℝ} (hg : Integrable g μ) {K : Set X} (hK : IsCompact K)
    (hz : ∀ᵐ z ∂μ, z ∉ K → g z = 0) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    IntervalIntegrable (fun τ => ∫ z, (kernelAverage μ ker τ A z - ker τ x z) * g z ∂μ)
      volume s t :=
  ((difference_density_continuousOn_time μ hQ hk A hA hbounded x hg hK hz).mono
    (fun _ ht => hs.trans_le ht.1)).intervalIntegrable_of_Icc hst

end RegularPointCoordinates

end

end OAI
