import OAI.Geometry.RCD.Heat.KernelDensityContinuity
import OAI.Geometry.RCD.Heat.HeatTimeContinuity

namespace OAI

/-! # Time continuity of compact L1 source pairings -/

open Set Metric MeasureTheory Filter
open scoped Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X)

/-- Compact L1 support is sufficient for positive-time continuity of the
source pairing, for both the kernel and its actual spatial average. -/
theorem integral_compact_density_continuousOn_time
    {k : ℝ × X → ℝ} (hc : ContinuousOn k (Ioi 0 ×ˢ univ))
    {g : X → ℝ} (hg : Integrable g μ) {K : Set X} (hK : IsCompact K)
    (hz : ∀ᵐ z ∂μ, z ∉ K → g z = 0) :
    ContinuousOn (fun t => ∫ z, k (t, z) * g z ∂μ) (Ioi 0) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  let T := closedBall t (t / 2)
  have hT : IsCompact T := isCompact_closedBall t (t / 2)
  have hTn : T ∈ 𝓝 t := closedBall_mem_nhds t (half_pos ht)
  have hTp : T ⊆ Ioi 0 := by
    intro s hs
    have habs : |s - t| ≤ t / 2 := by simpa only [T, mem_closedBall, Real.dist_eq] using hs
    have hh := (abs_le.mp habs).1
    change 0 < s
    have ht0 : 0 < t := ht
    linarith
  have hcTK : ContinuousOn k (T ×ˢ K) := hc.mono (fun sz hsz => ⟨hTp hsz.1, mem_univ _⟩)
  obtain ⟨C, hC⟩ := (hT.prod hK).bddAbove_image hcTK.norm
  let D := max C 0
  apply continuousAt_of_dominated (bound := fun z => D * |g z|)
  · filter_upwards [hTn] with s hs
    have hcs : Continuous (fun z => k (s, z)) := by
      apply continuousOn_univ.mp
      exact hc.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ _ => ⟨hTp hs, mem_univ _⟩)
    exact hcs.aestronglyMeasurable.mul hg.aestronglyMeasurable
  · filter_upwards [hTn] with s hs
    filter_upwards [hz] with z hz'
    by_cases hzK : z ∈ K
    · rw [norm_mul, Real.norm_eq_abs (g z)]
      exact mul_le_mul_of_nonneg_right
        ((hC ⟨(s, z), ⟨hs, hzK⟩, rfl⟩).trans (le_max_left _ _)) (abs_nonneg _)
    · simp only [hz' hzK, mul_zero, norm_zero, abs_zero, le_refl]
  · exact hg.abs.const_mul D
  · filter_upwards with z
    have hc' := (hc (t, z) ⟨ht, mem_univ _⟩).continuousAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht, mem_univ _⟩)
    exact (hc'.comp (f := fun s : ℝ => (s, z))
      (continuous_id.prodMk continuous_const).continuousAt).mul continuousAt_const

variable [ProperSpace X] [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk in
theorem kernel_density_continuousOn_time (x : X)
    {g : X → ℝ} (hg : Integrable g μ) {K : Set X} (hK : IsCompact K)
    (hz : ∀ᵐ z ∂μ, z ∉ K → g z = 0) :
    ContinuousOn (fun t => ∫ z, ker t x z * g z ∂μ) (Ioi 0) :=
  integral_compact_density_continuousOn_time μ (kernel_continuousOn_time_right μ hQ hk x) hg hK hz

include hk in
theorem average_density_continuousOn_time (A : Set X)
    (hA : MeasurableSet A) (hAt : μ A ≠ ⊤)
    {g : X → ℝ} (hg : Integrable g μ) {K : Set X} (hK : IsCompact K)
    (hz : ∀ᵐ z ∂μ, z ∉ K → g z = 0) :
    ContinuousOn (fun t => ∫ z, kernelAverage μ ker t A z * g z ∂μ) (Ioi 0) :=
  integral_compact_density_continuousOn_time μ
    (kernelAverage_continuousOn_time_space μ hQ hk A hA hAt) hg hK hz

include hk in
/-- The compact L1 source also gives a continuous averaged difference pairing. -/
theorem difference_density_continuousOn_time (A : Set X)
    (hA : MeasurableSet A) (hbounded : Bornology.IsBounded A) (x : X)
    {g : X → ℝ} (hg : Integrable g μ) {K : Set X} (hK : IsCompact K)
    (hz : ∀ᵐ z ∂μ, z ∉ K → g z = 0) :
    ContinuousOn (fun t => ∫ z, (kernelAverage μ ker t A z - ker t x z) * g z ∂μ) (Ioi 0) := by
  have hfinite : μ A ≠ ⊤ := hbounded.measure_lt_top.ne
  apply ((average_density_continuousOn_time μ hQ hk A hA hfinite hg hK hz).sub
    (kernel_density_continuousOn_time μ hQ hk x hg hK hz)).congr
  intro t ht
  simp_rw [sub_mul]
  exact integral_sub
    (continuous_mul_integrable_compact μ (kernelAverage_continuous μ hQ hk ht hA hbounded) hg hK hz)
    (continuous_mul_integrable_compact μ (hk.continuous_right t ht x) hg hK hz)

end RegularPointCoordinates

end

end OAI
