import OAI.GroupTheory.PolycyclicRecognition.Algebra.SlowPositiveSelection
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Support

namespace OAI

/-! # Good profile neighborhoods selected from a supported weak limit -/

noncomputable section

namespace PolycyclicRecognition

open Filter MeasureTheory Set
open scoped Topology ENNReal

/-- Each open neighborhood of a supported profile has a fixed positive
mass along every sufficiently late member of the weakly convergent family. -/
theorem eventual_positive_mass_of_supported_weak_limit
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {l : Filter ι} [l.NeBot] {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs l (𝓝 μ)) {x : X} (hx : x ∈ (μ : Measure X).support)
    {U : Set X} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ i in l, c ≤ ((μs i : Measure X) U).toReal := by
  have hp : 0 < (μ : Measure X) U :=
    (Measure.mem_support_iff_forall x).mp hx U (hU.mem_nhds hxU)
  have hfin : (μ : Measure X) U ≠ ∞ := measure_ne_top _ _
  have hr : 0 < ((μ : Measure X) U).toReal := ENNReal.toReal_pos hp.ne' hfin
  let c := ((μ : Measure X) U).toReal / 2
  have hc : 0 < c := half_pos hr
  have hlt : ENNReal.ofReal c < (μ : Measure X) U :=
    (ENNReal.ofReal_lt_iff_lt_toReal hc.le hfin).mpr (half_lt_self hr)
  have he := eventually_lt_of_lt_liminf
    (hlt.trans_le (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ hU))
  refine ⟨c, hc, he.mono ?_⟩
  intro i hi
  exact ((ENNReal.ofReal_lt_iff_lt_toReal hc.le (measure_ne_top _ _)).mp hi).le

/-- For any prescribed shrinking sequence of open neighborhoods, the
supported weak limit supplies good sets of subexponential mass. -/
theorem exists_supported_good_sets_subexponential
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {μs : ℝ → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs atTop (𝓝 μ)) {x : X} (hx : x ∈ (μ : Measure X).support)
    (U : ℕ → Set X) (hU : ∀ j, IsOpen (U j)) (hxU : ∀ j, x ∈ U j) :
    ∃ k : ℝ → ℕ, Tendsto k atTop atTop ∧
      HasSubexponentialLowerBound (fun r => ((μs r : Measure X) (U (k r))).toReal) := by
  exact exists_slow_subexponential_mass _ (fun j =>
    eventual_positive_mass_of_supported_weak_limit hμ hx (hU j) (hxU j))

end PolycyclicRecognition

end

end OAI
