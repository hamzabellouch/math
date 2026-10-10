import OAI.GroupTheory.PolycyclicRecognition.Analysis.BoundedProbabilityMean

namespace OAI

/-! # Mean error implies convergence in probability -/

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- Markov's inequality gives the probability direction for an integrable
nonnegative profile error, without a global bound off its sampling cell. -/
theorem bad_probability_tendsto_zero_of_mean
    {X : Type*} [MeasurableSpace X] (μ : ℕ → ProbabilityMeasure X)
    (f : ℕ → X → ℝ) (hi : ∀ n, Integrable (f n) (μ n : Measure X))
    (hf : ∀ n, 0 ≤ᵐ[(μ n : Measure X)] f n)
    (hm : Tendsto (fun n => ∫ x, f n x ∂(μ n : Measure X)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (μ n : Measure X) {x | ε ≤ f n x}) atTop (𝓝 0) := by
  have hbound n : ((μ n : Measure X) {x | ε ≤ f n x}).toReal ≤
      (∫ x, f n x ∂(μ n : Measure X)) / ε := by
    apply (le_div_iff₀ hε).mpr
    simpa only [measureReal_def, mul_comm] using
      mul_meas_ge_le_integral_of_nonneg (hf n) (hi n) ε
  have hreal : Tendsto (fun n => ((μ n : Measure X) {x | ε ≤ f n x}).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg) hbound (by simpa using hm.div_const ε)
  simpa only [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_zero] using
    ENNReal.tendsto_ofReal hreal

end PolycyclicRecognition

end OAI
