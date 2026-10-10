import OAI.Probability.InvariantIsing.Fields.SimpleFieldTransport

namespace OAI

/-! The extended magnetic value is one-Lipschitz for first-moment transport. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace InvariantIsing

lemma magneticFieldFunctional_coupling_le
    (ν μ ξ : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hμ : Integrable (fun x : ℝ => x) (μ : Measure ℝ))
    (hξ : Integrable (fun x : ℝ => x) (ξ : Measure ℝ)) (p : FieldLawCoupling μ ξ) :
    |magneticFieldFunctional (ν : Measure ℝ) b μ-magneticFieldFunctional (ν : Measure ℝ) b ξ| ≤
      ∫ xy, |xy.1-xy.2| ∂(p.law : Measure (ℝ × ℝ)) := by
  have hl := ((magneticFieldFunctional_approximation ν μ a b hcompact hbound ha hb hμ).sub
    (magneticFieldFunctional_approximation ν ξ a b hcompact hbound ha hb hξ)).abs
  have hr := (((fieldSimpleApproximation_tendsto (μ : Measure ℝ) hμ).add_const
    (∫ xy, |xy.1-xy.2| ∂(p.law : Measure (ℝ × ℝ)))).add
    (fieldSimpleApproximation_tendsto (ξ : Measure ℝ) hξ))
  simp only [zero_add,add_zero] at hr
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall fun n =>
    fieldCoupling_simple_error ν a b hcompact hbound ha hb p hμ hξ
      (fieldSimpleApproximation n) (fieldSimpleApproximation n))

lemma magneticFieldFunctional_wasserstein_le
    (ν μ ξ : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hμ : Integrable (fun x : ℝ => x) (μ : Measure ℝ))
    (hξ : Integrable (fun x : ℝ => x) (ξ : Measure ℝ)) :
    ENNReal.ofReal |magneticFieldFunctional (ν : Measure ℝ) b μ-
      magneticFieldFunctional (ν : Measure ℝ) b ξ| ≤ fieldWassersteinOne μ ξ := by
  apply le_iInf
  intro p
  rw [p.cost_eq_ofReal hμ hξ]
  exact ENNReal.ofReal_le_ofReal (magneticFieldFunctional_coupling_le ν μ ξ a b hcompact hbound ha hb hμ hξ p)

lemma magneticFieldFunctional_tendsto_wasserstein
    (ν μ : ProbabilityMeasure ℝ) (μs : ℕ → ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hμ : Integrable (fun x : ℝ => x) (μ : Measure ℝ))
    (hμs : ∀ n, Integrable (fun x : ℝ => x) (μs n : Measure ℝ))
    (hw : Tendsto (fun n => fieldWassersteinOne (μs n) μ) atTop (𝓝 0)) :
    Tendsto (fun n => magneticFieldFunctional (ν : Measure ℝ) b (μs n))
      atTop (𝓝 (magneticFieldFunctional (ν : Measure ℝ) b μ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hh := hw.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))
  filter_upwards [hh] with n hn
  rw [Real.dist_eq]
  have hc := (magneticFieldFunctional_wasserstein_le ν (μs n) μ a b hcompact hbound ha hb (hμs n) hμ).trans_lt hn
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp hc

end InvariantIsing

end

end OAI
