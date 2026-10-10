import OAI.Geometry.RCD.Heat.AveragedHeatSource

namespace OAI

/-! # Integrability of the actual compact measure sources in time -/

open Set Metric MeasureTheory Filter
open scoped InnerProductSpace Topology ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk in
/-- The finite signed source has an integrable averaged heat pairing,
including the initial endpoint. -/
theorem IsMeasureLaplacian.average_source_intervalIntegrable
    {u : SobolevSpace μ hQ} {ν : SignedMeasure X}
    (hν : IsMeasureLaplacian μ hQ u ν) (c : X) {R : ℝ} (hR : 0 < R)
    (hu : ∀ᵐ x ∂μ, R < dist c x → SobolevSpace.toLp μ hQ u x = 0)
    (hsν : ν.variation (Metric.closedBall c R)ᶜ = 0)
    (A : Set X) (hA : MeasurableSet A) (hAt : μ A ≠ ∞)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    IntervalIntegrable (fun r => ∫ᵛ z, kernelAverage μ ker r A z ∂<•ν) volume s t := by
  let F := fun r => ⟪heatAt μ hQ r (uniformDensityLp μ A hA hAt), SobolevSpace.toLp μ hQ u⟫_ℝ
  let D := fun r => ∫ᵛ z, kernelAverage μ ker r A z ∂<•ν
  have hd (r : ℝ) (hr : 0 < r) : HasDerivAt F (D r) r :=
    hν.average_heat_hasDerivAt μ hQ hk c hR hu hsν A hA hAt hr
  have heae : deriv F =ᵐ[volume.restrict (Ioc s t)] D := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact (hd r (hs.trans_lt hr.1)).deriv
  have hDm : AEStronglyMeasurable D (volume.restrict (Ioc s t)) :=
    (aestronglyMeasurable_deriv F _).congr heae
  let : IsFiniteMeasure ν.variation := by
    rw [← ν.totalVariation_eq_variation]
    infer_instance
  let C := (μ.real A)⁻¹ * ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip‖ * ν.variation.real univ
  have hDb : ∀ᵐ r ∂volume.restrict (Ioc s t), ‖D r‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    apply VectorMeasure.norm_integral_le_of_norm_le_const
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (kernelAverage_bounds μ hQ hk (hs.trans_lt hr.1) A z).1]
      exact (kernelAverage_bounds μ hQ hk (hs.trans_lt hr.1) A z).2
  show IntervalIntegrable D volume s t
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
  exact IntegrableOn.of_bound measure_Ioc_lt_top hDm C hDb

include hk in
/-- The pointwise pairing with the same full source is integrable on
every compact positive-time interval. -/
theorem IsMeasureLaplacian.point_source_intervalIntegrable
    {u : SobolevSpace μ hQ} {ν : SignedMeasure X}
    (hν : IsMeasureLaplacian μ hQ u ν) (c : X) {R : ℝ} (hR : 0 < R)
    (hu : ∀ᵐ x ∂μ, R < dist c x → SobolevSpace.toLp μ hQ u x = 0)
    (hsν : ν.variation (Metric.closedBall c R)ᶜ = 0)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (x : X) :
    IntervalIntegrable (fun r => ∫ᵛ z, ker r x z ∂<•ν) volume s t := by
  let a := s / 4
  have ha : 0 < a := by dsimp [a]; positivity
  let φ := fun r => heatTail μ hQ a ha (heatKernelRow μ hQ hk a x) (r - a)
  have hφc : Continuous φ := by
    exact (heatSobolevMap μ hQ a ha).continuous.comp
      ((heatAt_continuous μ hQ (heatKernelRow μ hQ hk a x)).comp
        ((continuous_id.sub continuous_const).sub continuous_const))
  have hφ (r : ℝ) (hr : r ∈ Icc s t) :
      φ r = heatKernelSobolev μ hQ hk r (hs.trans_le hr.1) x := by
    have hlow : s ≤ r := hr.1
    have hLp : SobolevSpace.toLp μ hQ (φ r) =
        SobolevSpace.toLp μ hQ (heatKernelSobolev μ hQ hk r (hs.trans_le hr.1) x) := by
      change SobolevSpace.toLp μ hQ (heatTail μ hQ a ha _ (r - a)) =
        SobolevSpace.toLp μ hQ (heatKernelSobolev μ hQ hk r (hs.trans_le hr.1) x)
      rw [heatTail_toLp μ hQ a ha _ (r - a) (by dsimp [a]; linarith),
        heatKernelSobolev_toLp,
        heatKernelRow_evolves μ hQ hk (show 0 < r - a by dsimp [a]; linarith) ha]
      simp only [sub_add_cancel]
    exact Subtype.ext hLp
  let D := fun r => -energyForm μ hQ u (φ r)
  have hDc : Continuous D :=
    ((energyForm_continuous μ hQ).comp (continuous_const.prodMk hφc)).neg
  have hDe (r : ℝ) (hr : r ∈ Icc s t) : D r = ∫ᵛ z, ker r x z ∂<•ν := by
    dsimp only [D]
    rw [hφ r hr, hν.test_heatKernel μ hQ hk c hR hu hsν, neg_neg]
  apply (hDc.intervalIntegrable s t).congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
  apply hDe r
  have hr' : r ∈ Ioc s t := by simpa only [uIoc_of_le hst] using hr
  exact ⟨hr'.1.le, hr'.2⟩

end RegularPointCoordinates

end

end OAI
