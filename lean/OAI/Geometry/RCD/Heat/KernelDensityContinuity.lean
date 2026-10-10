import OAI.Geometry.RCD.Metric.AveragedDensityFubini

namespace OAI

/-! # Spatial continuity of the genuine compact L1 source pairings -/

open Set Metric MeasureTheory Filter
open scoped Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

omit [ProperSpace X] [μ.Regular] in
/-- A continuous multiplier preserves integrability of a compact L1 density. -/
theorem continuous_mul_integrable_compact {k g : X → ℝ} (hc : Continuous k)
    (hg : Integrable g μ) {K : Set X} (hK : IsCompact K)
    (hz : ∀ᵐ z ∂μ, z ∉ K → g z = 0) : Integrable (fun z => k z * g z) μ := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image hc.norm.continuousOn
  let D := max C 0
  apply (hg.abs.const_mul D).mono' (hc.aestronglyMeasurable.mul hg.aestronglyMeasurable)
  filter_upwards [hz] with z hz'
  change ‖k z * g z‖ ≤ D * |g z|
  by_cases hzK : z ∈ K
  · rw [norm_mul, Real.norm_eq_abs (g z)]
    exact mul_le_mul_of_nonneg_right
      ((hC ⟨z, hzK, rfl⟩).trans (le_max_left _ _)) (abs_nonneg _)
  · simp only [hz' hzK, mul_zero, norm_zero, abs_zero, le_refl]

include hk in
/-- Compact L1 densities give continuous positive-time heat pairings.
This applies to the cutoff error without requiring it to belong to L2. -/
theorem kernel_integral_density_continuous {t : ℝ} (ht : 0 < t)
    {g : X → ℝ} (hg : Integrable g μ) {K : Set X} (hK : IsCompact K)
    (hgzero : ∀ᵐ z ∂μ, z ∉ K → g z = 0) :
    Continuous (fun y => ∫ z, ker t y z * g z ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro x
  let U := closedBall x 1
  have hU : IsCompact U := isCompact_closedBall x 1
  have hUn : U ∈ 𝓝 x := closedBall_mem_nhds x (by norm_num)
  obtain ⟨C, hC⟩ := (hU.prod hK).bddAbove_image (hk.continuous_joint t ht).norm.continuousOn
  let D := max C 0
  apply continuousAt_of_dominated (bound := fun z => D * |g z|)
  · filter_upwards with y
    exact (hk.continuous_right t ht y).aestronglyMeasurable.mul hg.aestronglyMeasurable
  · filter_upwards [hUn] with y hy
    filter_upwards [hgzero] with z hz
    by_cases hzK : z ∈ K
    · rw [norm_mul, Real.norm_eq_abs (g z)]
      exact mul_le_mul_of_nonneg_right
        ((hC ⟨(y, z), ⟨hy, hzK⟩, rfl⟩).trans (le_max_left _ _)) (abs_nonneg _)
    · simp only [hz hzK, mul_zero, norm_zero, abs_zero, le_refl]
  · exact hg.abs.const_mul D
  · filter_upwards with z
    exact (((hk.continuous_joint t ht).comp
      (continuous_id.prodMk continuous_const)).mul continuous_const).continuousAt

end RegularPointCoordinates

end

end OAI
