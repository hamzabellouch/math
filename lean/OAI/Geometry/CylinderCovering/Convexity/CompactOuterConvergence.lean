import Mathlib

namespace OAI

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology

namespace CylinderCovering.CompactOuterConvergence

variable {E : Type*} [MetricSpace E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [ProperSpace E]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

theorem cthickening_excess_tendsto {D : Set E} (hD : IsCompact D) :
    Tendsto (fun r : ℝ => μ (cthickening r D \ D)) (𝓝 0) (𝓝 0) := by
  have h := (ENNReal.continuous_sub_right (μ D)).tendsto (μ D) |>.comp
    (tendsto_measure_cthickening_of_isCompact (μ := μ) hD)
  have heq : ∀ r : ℝ, μ (cthickening r D \ D) = μ (cthickening r D) - μ D :=
    fun _ => measure_sdiff (self_subset_cthickening D)
      hD.measurableSet.nullMeasurableSet hD.measure_lt_top.ne
  simpa only [heq, tsub_self, Function.comp_def] using h

theorem excess_tendsto_of_eventually_subset_cthickening
    {ι : Type*} {l : Filter ι} {D : Set E} (hD : IsCompact D)
    {U : ι → Set E} {r : ι → ℝ} (hr : Tendsto r l (𝓝 0))
    (hU : ∀ᶠ i in l, U i ⊆ cthickening (r i) D) :
    Tendsto (fun i => μ (U i \ D)) l (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    ((cthickening_excess_tendsto (μ := μ) hD).comp hr)
  · exact Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [hU] with i hi
    exact measure_mono (sdiff_subset_sdiff_left hi)

theorem real_excess_tendsto_of_eventually_subset_cthickening
    {ι : Type*} {l : Filter ι} {D : Set E} (hD : IsCompact D)
    {U : ι → Set E} {r : ι → ℝ} (hr : Tendsto r l (𝓝 0))
    (hU : ∀ᶠ i in l, U i ⊆ cthickening (r i) D) :
    Tendsto (fun i => μ.real (U i \ D)) l (𝓝 0) := by
  simpa only [measureReal_def, ENNReal.toReal_zero, Function.comp_def] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (excess_tendsto_of_eventually_subset_cthickening hD hr hU)

theorem linear_mesh_real_excess_tendsto {D : Set E} (hD : IsCompact D)
    (C : ℝ) {U : ℝ → Set E}
    (hU : ∀ δ : ℝ, 0 < δ → U δ ⊆ cthickening (C * δ) D) :
    Tendsto (fun δ : ℝ => μ.real (U δ \ D)) (𝓝[>] 0) (𝓝 0) := by
  apply real_excess_tendsto_of_eventually_subset_cthickening hD
    (r := fun δ => C * δ)
  · simpa using (tendsto_const_nhds.mul
      (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun δ : ℝ => C * δ) (𝓝[>] 0) (𝓝 (C * 0)))
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hU δ hδ

end CylinderCovering.CompactOuterConvergence

end

end OAI
