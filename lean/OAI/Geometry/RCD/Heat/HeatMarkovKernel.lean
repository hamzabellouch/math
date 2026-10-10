import OAI.Geometry.RCD.Heat.HeatBoundedContinuousTest
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace OAI

/-! # The measurable Markov family associated to the RCD heat flow -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology CompactlySupported BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

/-- Heat evaluation as a probability measure, constructed from the actual
semigroup on compact continuous tests. -/
def radonHeatProbability (t : ℝ) (ht : 0 < t) (x : X) : ProbabilityMeasure X :=
  ⟨hX.heatRadonMeasure hn p t ht x, inferInstance⟩

theorem radonHeatProbability_continuous (t : ℝ) (ht : 0 < t) :
    Continuous (hX.radonHeatProbability hn p t ht) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro f
  exact (hX.heatRadonMeasure_integral_lipschitz hn p t ht f).continuous

/-- Closed-set approximation converts continuity on bounded tests into
measurability of the entire measure-valued family. -/
theorem heatRadonMeasure_measurable (t : ℝ) (ht : 0 < t) :
    Measurable (hX.heatRadonMeasure hn p t ht) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (S := {s : Set X | IsClosed s})
  · exact (show ‹MeasurableSpace X› = borel X from BorelSpace.measurable_eq).trans
      borel_eq_generateFrom_isClosed
  · exact isPiSystem_isClosed
  intro A hA
  have hm (i : ℕ) : Measurable (fun x =>
      ∫⁻ y, (hA.apprSeq i y : ℝ≥0∞) ∂hX.heatRadonMeasure hn p t ht x) := by
    let f : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun y => (hA.apprSeq i y : ℝ))
      (NNReal.continuous_coe.comp (hA.apprSeq i).continuous) 1
      (fun y => by simpa using HasOuterApproxClosed.apprSeq_apply_le_one hA i y)
    have he (x : X) : (∫⁻ y, (hA.apprSeq i y : ℝ≥0∞)
        ∂hX.heatRadonMeasure hn p t ht x) =
        ENNReal.ofReal (∫ y, f y ∂hX.heatRadonMeasure hn p t ht x) := by
      exact lintegral_coe_eq_integral _ (f.integrable _)
    simp_rw [he]
    exact ENNReal.continuous_ofReal.measurable.comp
      (hX.heatRadonMeasure_integral_lipschitz hn p t ht f).continuous.measurable
  apply ENNReal.measurable_of_tendsto hm
  exact tendsto_pi_nhds.mpr fun x =>
    HasOuterApproxClosed.tendsto_lintegral_apprSeq hA (hX.heatRadonMeasure hn p t ht x)

/-- The canonical heat family is an actual measurable Markov kernel. -/
def heatMarkovKernel (t : ℝ) (ht : 0 < t) : ProbabilityTheory.Kernel X X where
  toFun := hX.heatRadonMeasure hn p t ht
  measurable' := hX.heatRadonMeasure_measurable hn p t ht

instance heatMarkovKernel_isMarkov (t : ℝ) (ht : 0 < t) :
    ProbabilityTheory.IsMarkovKernel (hX.heatMarkovKernel hn p t ht) :=
  ⟨fun x => show IsProbabilityMeasure (hX.heatRadonMeasure hn p t ht x) from inferInstance⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
