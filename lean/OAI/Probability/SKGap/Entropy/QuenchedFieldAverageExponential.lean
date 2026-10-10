import Mathlib
import OAI.Probability.SKGap.Stability.PlantedFieldCenter
import OAI.Probability.SKGap.Terminal.GibbsEventProbability

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
namespace SKGapCutoff.Regression

lemma quenched_field_average_exponential (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1)
    (f : ℝ → ℝ) {K : ℝ≥0} (hK : 0 < K) (hf : LipschitzWith K f)
    (B : ℝ) (hB : 0 < B) (hbound : ∀ z, |f z| ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ Tendsto (fun n => disorderLaw β n {g |
      ENNReal.ofReal (Real.exp (-c*n)) ≤
        gibbsEventProbability (fun x : Spin n => {h : GaussianCoordinates n |
          ε ≤ |(∑ i : Fin n, f (gaugedField x h i))/(n:ℝ) -
            ∫ z, f (β^2+β*z) ∂gaussianReal 0 1|}) g}) atTop (nhds 0) := by
  obtain ⟨c, hc, hs⟩ := planted_field_average_exponential β hβ f hK hf B hB hbound ε hε
  refine ⟨c/2, by positivity, ?_⟩
  have hb : β^2 < 1 := by nlinarith
  apply quenched_gibbs_events_exponential β hb c hc _ _ hs
  intro n x
  apply measurableSet_le measurable_const
  apply Measurable.abs
  apply Measurable.sub_const
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _
  exact hf.continuous.measurable.comp
    ((measurable_pi_apply i).comp (continuous_gaugedField x).measurable)

end SKGapCutoff.Regression

open scoped BigOperators

end

end OAI
