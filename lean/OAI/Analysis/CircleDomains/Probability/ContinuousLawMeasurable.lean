import OAI.Analysis.CircleDomains.Probability.PathHitLaws

namespace OAI

/-! Weakly continuous probability kernels are measurable for the evaluation
sigma algebra. This follows from the open-set Portmanteau inequality and the
pi-system of open sets. -/

open Set MeasureTheory TopologicalSpace

noncomputable section

namespace CircleDomainRigidity

theorem measurable_of_continuous_probability
    {Z Ω : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [HasOuterApproxClosed Ω]
    {law : Z → ProbabilityMeasure Ω} (hlaw : Continuous law) : Measurable law := by
  have hm : Measurable (fun z => (law z : Measure Ω)) := by
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      BorelSpace.measurable_eq isPiSystem_isOpen
    intro U hU
    have h : LowerSemicontinuous (fun z => (law z : Measure Ω) U) := by
      apply lowerSemicontinuous_iff_le_liminf.mpr
      intro z
      exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlaw.continuousAt hU
    exact h.measurable
  exact hm.subtype_mk

end CircleDomainRigidity

end

end OAI
