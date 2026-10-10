import OAI.Geometry.RCD.Heat.HeatMeasureMass
import OAI.Geometry.RCD.Sobolev.NullCompactCutoff
import OAI.Geometry.RCD.Sobolev.UniformLipschitzL2Limit

namespace OAI

/-! # Absolute continuity of the constructed heat measure

Small continuous cutoffs of a null compact set converge to zero in L².
The uniform bounded-data smoothing estimate makes their heat values
converge at every center. Radon regularity then excludes every null set.
No kernel density is assumed.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology CompactlySupported

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem heatRadonMeasure_compact_null (t : ℝ) (ht : 0 < t) (x : X)
    {S : Set X} (hS : IsCompact S) (hnull : hausdorff n X S = 0) :
    hX.heatRadonMeasure hn p t ht x S = 0 := by
  obtain ⟨F, hF, hFS, hlim⟩ := exists_null_compact_cutoffs (hausdorff n X) hS hnull
  have hb (i : ℕ) : ∀ᵐ y ∂hausdorff n X,
      |compactTestToL2 (hausdorff n X) (F i) y| ≤ (1 : ℝ≥0) := by
    filter_upwards [compactTestToL2_coe (hausdorff n X) (F i)] with y hy
    rw [hy, abs_of_nonneg (hF i y).1]
    exact (hF i y).2
  have hv : Tendsto (fun i => hX.compactHeatEval hn p t ht x (F i)) atTop (𝓝 0) :=
    hX.boundedHeat_tendsto_zero hn p (fun i => compactTestToL2 (hausdorff n X) (F i))
      1 hb hlim t ht x
  have he : Tendsto (fun i => ENNReal.ofReal (hX.compactHeatEval hn p t ht x (F i)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using! (ENNReal.continuous_ofReal.tendsto 0).comp hv
  apply le_antisymm (ge_of_tendsto he (Eventually.of_forall fun i => ?_)) bot_le
  exact RealRMK.rieszMeasure_le_of_eq_one (hX.compactHeatEval hn p t ht x)
    (fun y => (hF i y).1) hS (hFS i)

/-- Every positive-time heat evaluation has a density with respect to the
actual reference measure, including at every prescribed center. -/
theorem heatRadonMeasure_absolutelyContinuous (t : ℝ) (ht : 0 < t) (x : X) :
    hX.heatRadonMeasure hn p t ht x ≪ hausdorff n X := by
  have hmeas (S : Set X) (hS : MeasurableSet S) (hnull : hausdorff n X S = 0) :
      hX.heatRadonMeasure hn p t ht x S = 0 := by
    rw [hS.measure_eq_iSup_isCompact]
    apply le_antisymm ?_ bot_le
    refine iSup_le fun A => iSup_le fun hAS => iSup_le fun hA => ?_
    exact le_of_eq (hX.heatRadonMeasure_compact_null hn p t ht x hA
      (measure_mono_null hAS hnull))
  intro S hnull
  exact measure_mono_null (subset_toMeasurable (hausdorff n X) S)
    (hmeas (toMeasurable (hausdorff n X) S) (measurableSet_toMeasurable _ _)
      (by rwa [measure_toMeasurable]))

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
