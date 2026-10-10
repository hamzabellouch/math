import OAI.GroupTheory.PolycyclicRecognition.Algebra.OccupationWeakLimit
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Ultrafilter

namespace OAI

/-! # Selecting one occupation limit while preserving the profile limit -/

namespace PolycyclicRecognition

open Filter MeasureTheory Set
open scoped Topology

/-- Compactness selects a single occupation limit on a finer filter, and
every already established profile limit is retained. The filter and the
occupation measure are selected before any microstep length. -/
theorem exists_occupation_limit_preserving
    {X Y ι : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
    {l : Filter ι} [l.NeBot] (μs : ι → ProbabilityMeasure X)
    {profiles : ι → Y} {ν : Y} (hν : Tendsto profiles l (𝓝 ν)) :
    ∃ (u : Ultrafilter ι) (μ : ProbabilityMeasure X),
      (u : Filter ι) ≤ l ∧ Tendsto μs u (𝓝 μ) ∧ Tendsto profiles u (𝓝 ν) := by
  obtain ⟨μ, _, hμ⟩ := (isCompact_univ : IsCompact (univ : Set (ProbabilityMeasure X))).exists_mapClusterPt
    (show Filter.map μs l ≤ 𝓟 univ by simp)
  obtain ⟨u, hul, huμ⟩ := mapClusterPt_iff_ultrafilter.mp hμ
  exact ⟨u, μ, hul, huμ, hν.mono_left hul⟩

/-- The stationary nonnegative integral is the real integral used by the
microstep estimate, so convergence of the former supplies the latter. -/
theorem integral_tendsto_zero_of_lintegral_nonneg
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) {l : Filter ι} (f : ι → C(X, ℝ))
    (hp : ∀ i x, 0 ≤ f i x)
    (hlim : Tendsto (fun i => ∫⁻ x, ENNReal.ofReal (f i x) ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, f i x ∂μ) l (𝓝 0) := by
  have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
  simp only [ENNReal.toReal_zero] at ht
  have heq (i : ι) : (∫⁻ x, ENNReal.ofReal (f i x) ∂μ).toReal = ∫ x, f i x ∂μ := by
    symm
    exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (hp i))
      (f i).continuous.aestronglyMeasurable
  simpa only [Function.comp_def, heq] using ht

end PolycyclicRecognition

end OAI
