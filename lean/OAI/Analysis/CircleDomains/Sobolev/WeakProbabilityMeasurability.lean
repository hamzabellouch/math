import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

/-! A continuous family of weak probability laws is a measurable family of
measures. Closed-set evaluations are limits of continuous test integrals. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma measurable_measure_of_continuous_probability
    {X Z : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [HasOuterApproxClosed Z]
    {F : X → ProbabilityMeasure Z} (hF : Continuous F) :
    Measurable (fun x => (F x : Measure Z)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed
  intro S hS
  apply measurable_of_tendsto_metrizable
    (fun n => ((ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction
      (hS.apprSeq n)).comp hF).measurable)
  apply tendsto_pi_nhds.mpr
  intro x
  exact HasOuterApproxClosed.tendsto_lintegral_apprSeq hS (F x : Measure Z)

end CircleDomainRigidity

end

end OAI
