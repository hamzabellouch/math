import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Function
open scoped Topology ENNReal

namespace Problem356

/-- A Stieltjes function has no jumps when its associated measure has no point atoms. -/
theorem continuous_stieltjesFunction_of_nullSingletonClass
    (f : StieltjesFunction ℝ) [NullSingletonClass f.measure] : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply f.mono.continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [f.rightLim_eq]
  have hz : ENNReal.ofReal (f x - leftLim f x) = 0 := by
    rw [← f.measure_singleton]
    exact measure_singleton x
  exact le_antisymm (f.mono.leftLim_le le_rfl)
    (sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp hz))

/-- The cumulative distribution function of an atomless real probability measure is continuous. -/
theorem continuous_cdf_of_nullSingletonClass (mu : Measure ℝ)
    [IsProbabilityMeasure mu] [NullSingletonClass mu] :
    Continuous (ProbabilityTheory.cdf mu) := by
  have : NullSingletonClass (ProbabilityTheory.cdf mu).measure := by
    rw [ProbabilityTheory.measure_cdf]
    infer_instance
  exact continuous_stieltjesFunction_of_nullSingletonClass _

end Problem356

end

end OAI
