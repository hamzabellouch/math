import OAI.Probability.InvariantIsing.Fields.FieldSimpleApproximation

namespace OAI

/-! The magnetic value for a field law with finite first absolute moment. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

def magneticFieldFunctional (spectral : Measure ℝ) (edge : ℝ) (field : ProbabilityMeasure ℝ) : ℝ :=
  limUnder atTop (fun n => simpleFieldValue (field : Measure ℝ) (fieldSimpleApproximation n)
    (measureR spectral edge))

lemma magneticFieldFunctional_approximation
    (ν μ : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hμ : Integrable (fun x : ℝ => x) (μ : Measure ℝ)) :
    Tendsto (fun n => simpleFieldValue (μ : Measure ℝ) (fieldSimpleApproximation n)
      (measureR (ν : Measure ℝ) b)) atTop (𝓝 (magneticFieldFunctional (ν : Measure ℝ) b μ)) := by
  exact (simpleFieldValue_cauchy (μ : Measure ℝ) fieldSimpleApproximation id hμ
    (fieldSimpleApproximation_tendsto _ hμ) ν a b hcompact hbound ha hb).tendsto_limUnder

lemma magneticFieldFunctional_simple_error
    (ν μ : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hμ : Integrable (fun x : ℝ => x) (μ : Measure ℝ)) (s : SimpleFunc ℝ ℝ) :
    |magneticFieldFunctional (ν : Measure ℝ) b μ-simpleFieldValue (μ : Measure ℝ) s
      (measureR (ν : Measure ℝ) b)| ≤ ∫ x, |x-s x| ∂(μ : Measure ℝ) := by
  have hv := ((magneticFieldFunctional_approximation ν μ a b hcompact hbound ha hb hμ).sub_const
    (simpleFieldValue (μ : Measure ℝ) s (measureR (ν : Measure ℝ) b))).abs
  have he := (fieldSimpleApproximation_tendsto (μ : Measure ℝ) hμ).add_const
    (∫ x, |x-s x| ∂(μ : Measure ℝ))
  rw [zero_add] at he
  apply le_of_tendsto_of_tendsto hv he
  apply Eventually.of_forall
  intro n
  dsimp only
  refine (simpleFieldValue_abs_sub_le ν a b hcompact hbound ha hb
    (μ : Measure ℝ) (fieldSimpleApproximation n) s).trans ?_
  have hsum := integral_add ((simpleField_integrable (μ : Measure ℝ) (fieldSimpleApproximation n)).sub hμ).abs
    (hμ.sub (simpleField_integrable (μ : Measure ℝ) s)).abs
  dsimp only [Pi.add_apply,Pi.sub_apply] at hsum
  rw [← hsum]
  apply integral_mono ((simpleField_integrable (μ : Measure ℝ) (fieldSimpleApproximation n)).sub
    (simpleField_integrable (μ : Measure ℝ) s)).abs
    (((simpleField_integrable (μ : Measure ℝ) (fieldSimpleApproximation n)).sub hμ).abs.add
      (hμ.sub (simpleField_integrable (μ : Measure ℝ) s)).abs)
  intro x
  change |fieldSimpleApproximation n x-s x| ≤ |fieldSimpleApproximation n x-x|+|x-s x|
  exact abs_sub_le _ _ _

end InvariantIsing

end

end OAI
