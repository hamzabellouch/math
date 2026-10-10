import OAI.Geometry.RCD.Heat.HeatTimeContinuity
import OAI.Geometry.RCD.Metric.LongAverageMassIntegral

namespace OAI

/-! # Positive-time continuity and integrability of full heat mass -/

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {χ : X → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [IsLocallyFiniteMeasure μ] in
/-- The finite positive Bochner measure may be singular; continuity follows
from the actual joint kernel and the fixed compact cutoff. -/
theorem cutoffHeatMassAt_continuousOn (M : PositiveBilinearMeasure X E) (x : X) (v : E) :
    ContinuousOn (fun t => ⟪v, cutoffHeatMassAt μ hQ hk hχ hc M t x v⟫_ℝ) (Ioi 0) := by
  have hker := kernel_continuousOn_time_right μ hQ hk x
  have hint := continuousOn_integral_of_compact_support (μ := M.measure v)
    hc.isCompact (((hχ.comp continuous_snd).continuousOn).mul hker)
    (fun t z _ hz => by
      change χ z * ker t x z = 0
      rw [image_eq_zero_of_notMem_tsupport hz, zero_mul])
  apply hint.congr
  intro t ht
  change ⟪v, cutoffHeatMassAt μ hQ hk hχ hc M t x v⟫_ℝ = _
  rw [cutoffHeatMassAt_of_pos μ hQ hk hχ hc M ht x]
  exact cutoffHeatMass_energy μ hQ hk hχ hc M ht x v

/-- Averaging in the first pole preserves the same positive-time
continuity against the full Bochner measure. -/
theorem cutoffAverageHeatMassAt_continuousOn (M : PositiveBilinearMeasure X E)
    (A : Set X) (hA : MeasurableSet A) (hbounded : Bornology.IsBounded A) (v : E) :
    ContinuousOn (fun t => ⟪v, cutoffAverageHeatMassAt μ hQ hk hχ hc M A hA hbounded t v⟫_ℝ)
      (Ioi 0) := by
  have hker := kernelAverage_continuousOn_time_space μ hQ hk A hA hbounded.measure_lt_top.ne
  have hint := continuousOn_integral_of_compact_support (μ := M.measure v)
    hc.isCompact (((hχ.comp continuous_snd).continuousOn).mul hker)
    (fun t z _ hz => by
      change χ z * kernelAverage μ ker t A z = 0
      rw [image_eq_zero_of_notMem_tsupport hz, zero_mul])
  apply hint.congr
  intro t ht
  change ⟪v, cutoffAverageHeatMassAt μ hQ hk hχ hc M A hA hbounded t v⟫_ℝ = _
  rw [cutoffAverageHeatMassAt_of_pos μ hQ hk hχ hc M A hA hbounded ht]
  exact cutoffAverageHeatMass_integral μ hQ hk hχ hc M ht A hA hbounded v

/-- Both terms in a long-time block are genuinely integrable. -/
theorem cutoffAverageHeatMassAt_difference_intervalIntegrable
    (M : PositiveBilinearMeasure X E) (A : Set X) (hA : MeasurableSet A)
    (hbounded : Bornology.IsBounded A) (x : X) (v : E)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    IntervalIntegrable (fun r => ⟪v, (cutoffAverageHeatMassAt μ hQ hk hχ hc M A hA hbounded r -
      cutoffHeatMassAt μ hQ hk hχ hc M r x) v⟫_ℝ) volume s t := by
  have ha := cutoffAverageHeatMassAt_continuousOn μ hQ hk hχ hc M A hA hbounded v
  have hp := cutoffHeatMassAt_continuousOn μ hQ hk hχ hc M x v
  have hsub : ContinuousOn (fun r => ⟪v, (cutoffAverageHeatMassAt μ hQ hk hχ hc M A hA hbounded r -
      cutoffHeatMassAt μ hQ hk hχ hc M r x) v⟫_ℝ) (Ioi 0) := by
    apply (ha.sub hp).congr
    intro r _
    change ⟪v, (cutoffAverageHeatMassAt μ hQ hk hχ hc M A hA hbounded r -
      cutoffHeatMassAt μ hQ hk hχ hc M r x) v⟫_ℝ = _
    rw [sub_apply, inner_sub_right]
    rfl
  exact (hsub.mono (fun r hr => hs.trans_le hr.1)).intervalIntegrable_of_Icc hst

end RegularPointCoordinates

end

end OAI
