import OAI.Probability.InvariantIsing.Fields.SimpleFieldTransport

namespace OAI

/-! The field-law extension agrees exactly with the finite variational formula. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators Classical
namespace InvariantIsing

variable (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
include hcompact hbound ha hb

lemma simpleFieldValue_eq_finite_law {Ω A : Type*} [MeasurableSpace Ω] [Fintype A]
    (P : Measure Ω) [IsProbabilityMeasure P] (s : SimpleFunc Ω ℝ)
    (γ c : A → ℝ) (hγ : ∀ i, 0 < γ i) (hsum : ∑ i, γ i=1)
    (he : P.map s=finiteSpectralMeasure γ c) :
    simpleFieldValue P s (measureR (ν : Measure ℝ) b)=
      (finiteMagneticFunctional (measureR (ν : Measure ℝ) b) γ c).toReal := by
  apply measureMagnetic_eq_of_field_law_eq ν a b hcompact hbound ha hb
    (fun i : SimpleFieldPositive P s => simpleFieldWeight P s i) (fun i => i.val.val)
    γ c (fun i => i.property) hγ
    (positiveSpectralWeights_sum _ (fun _ => measureReal_nonneg) (simpleFieldWeight_sum P s)) hsum
  rw [← simpleField_law P s,he]

lemma magneticFieldFunctional_eq_simple {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s : SimpleFunc Ω ℝ)
    (μ : ProbabilityMeasure ℝ) (he : P.map s=(μ : Measure ℝ))
    (hμ : Integrable (fun x : ℝ => x) (μ : Measure ℝ)) :
    magneticFieldFunctional (ν : Measure ℝ) b μ=simpleFieldValue P s (measureR (ν : Measure ℝ) b) := by
  have herr := fieldSimpleApproximation_tendsto (μ : Measure ℝ) hμ
  have hv := magneticFieldFunctional_approximation ν μ a b hcompact hbound ha hb hμ
  have hdiff : Tendsto (fun n => simpleFieldValue (μ : Measure ℝ) (fieldSimpleApproximation n)
      (measureR (ν : Measure ℝ) b)-simpleFieldValue P s (measureR (ν : Measure ℝ) b)) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ herr
    intro n
    have hm := simpleFieldValue_comp ν a b hcompact hbound ha hb P (μ : Measure ℝ)
      s s.measurable he (fieldSimpleApproximation n)
    rw [← hm,Real.norm_eq_abs]
    refine (simpleFieldValue_abs_sub_le ν a b hcompact hbound ha hb P
      ((fieldSimpleApproximation n).comp s s.measurable) s).trans_eq ?_
    rw [← he,integral_map s.aemeasurable]
    · rfl
    · exact (((fieldSimpleApproximation n).measurable.sub measurable_id).abs).aestronglyMeasurable
  exact sub_eq_zero.mp (tendsto_nhds_unique (hv.sub_const _) hdiff)

lemma magneticFieldFunctional_finite {A : Type*} [Fintype A]
    (γ c : A → ℝ) (hγ : ∀ i, 0 < γ i) (hsum : ∑ i, γ i=1)
    (μ : ProbabilityMeasure ℝ) (he : (μ : Measure ℝ)=finiteSpectralMeasure γ c) :
    magneticFieldFunctional (ν : Measure ℝ) b μ=
      (finiteMagneticFunctional (measureR (ν : Measure ℝ) b) γ c).toReal := by
  let : MeasurableSpace A := ⊤
  let P : Measure A := Measure.sum fun i => ENNReal.ofReal (γ i) • Measure.dirac i
  let : IsProbabilityMeasure P := HasSum.isProbabilityMeasure_sum_dirac
    (fun i => (hγ i).le) (by simpa only [hsum] using hasSum_fintype γ)
  let s := SimpleFunc.ofFinite c
  have hp : P.map s=(μ : Measure ℝ) := by
    rw [he]
    change P.map (c ∘ id)=_
    have hh := finiteIndex_map P id measurable_id c
    have hw : finiteIndexWeight P id=γ := by
      funext i
      change (P.real {i})=γ i
      simp [P,measureReal_def,Pi.single_apply,(hγ i).le]
    rw [hw] at hh
    exact hh
  have hi : Integrable (fun x : ℝ => x) (μ : Measure ℝ) := by
    rw [← hp]
    exact (integrable_map_measure aestronglyMeasurable_id s.aemeasurable).mpr
      (simpleField_integrable P s)
  rw [magneticFieldFunctional_eq_simple ν a b hcompact hbound ha hb P s μ hp hi]
  exact simpleFieldValue_eq_finite_law ν a b hcompact hbound ha hb P s γ c hγ hsum (hp.trans he)

end InvariantIsing

end

end OAI
