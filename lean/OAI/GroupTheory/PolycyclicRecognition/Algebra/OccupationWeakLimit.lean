import OAI.GroupTheory.PolycyclicRecognition.Analysis.StationaryProbability
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.Support

namespace OAI

/-! # Invariance of weak occupation limits

The geometric chart calculation must supply the displayed translated-integral
error. This bridge then passes that error to the fixed limiting probability.
-/

namespace PolycyclicRecognition

open MeasureTheory Filter
open scoped Topology CompactlySupported ENNReal

/-- Vanishing translation errors pass through weak convergence on the compact
section. This theorem does not assume invariance of the limiting measure. -/
theorem invariant_of_weak_occupation_limit
    {G X ι : Type*} [Group G] [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [MulAction G X] [ContinuousConstSMul G X]
    {l : Filter ι} [l.NeBot]
    (μs : ι → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hlim : Tendsto μs l (𝓝 μ))
    (herror : ∀ (g : G) (f : C(X, ℝ)), Tendsto
      (fun i => (∫ x, f (g • x) ∂(μs i : Measure X)) -
        ∫ x, f x ∂(μs i : Measure X)) l (𝓝 0)) :
    SMulInvariantMeasure G X (μ : Measure X) := by
  have hintegral (g : G) (f : C(X, ℝ)) :
      ∫ x, f (g • x) ∂(μ : Measure X) = ∫ x, f x ∂(μ : Measure X) := by
    let fg : C(X, ℝ) := ⟨fun x => f (g • x), f.continuous.comp (continuous_const_smul g)⟩
    have h₁ := (ProbabilityMeasure.continuous_integral_continuousMap fg).tendsto μ |>.comp hlim
    have h₂ := (ProbabilityMeasure.continuous_integral_continuousMap f).tendsto μ |>.comp hlim
    have heq := tendsto_nhds_unique (h₁.sub h₂) (herror g f)
    exact sub_eq_zero.mp heq
  have hmap (g : G) : Measure.map (g • ·) (μ : Measure X) = μ := by
    have : (Measure.map (g • ·) (μ : Measure X)).Regular :=
      Measure.Regular.map (Homeomorph.smul g)
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    change (∫ x, f.toContinuousMap x ∂Measure.map (g • ·) (μ : Measure X)) =
      ∫ x, f.toContinuousMap x ∂(μ : Measure X)
    rw [integral_map (continuous_const_smul g).measurable.aemeasurable
      f.continuous.aestronglyMeasurable]
    exact hintegral g f.toContinuousMap
  exact ⟨fun g s hs => by
    rw [← Measure.map_apply (continuous_const_smul g).measurable hs, hmap]⟩

/-- A continuous nonnegative error with zero integral vanishes on every
supported profile, not merely almost everywhere. -/
theorem eq_zero_on_support_of_lintegral_eq_zero
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) (hf : Continuous f)
    (hzero : ∫⁻ x, f x ∂μ = 0) {x : X} (hx : x ∈ μ.support) : f x = 0 := by
  have hae := (lintegral_eq_zero_iff hf.measurable).mp hzero
  exact μ.support_subset_of_isClosed (isClosed_eq hf continuous_const) hae hx

end PolycyclicRecognition

end OAI
