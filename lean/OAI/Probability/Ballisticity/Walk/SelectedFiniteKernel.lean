import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

noncomputable def normalizeFinite {α : Type*} [MeasurableSpace α] (μ : Measure α) : Measure α :=
  (μ Set.univ)⁻¹ • μ

lemma normalizeFinite_probability {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (h0 : μ Set.univ ≠ 0) (ht : μ Set.univ ≠ ∞) : IsProbabilityMeasure (normalizeFinite μ) := by
  refine ⟨?_⟩
  simpa [normalizeFinite,Measure.smul_apply] using ENNReal.inv_mul_cancel h0 ht

lemma normalizeFinite_domination {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {δ : ℝ≥0∞} (_ : δ ≠ 0) (hm : δ ≤ μ Set.univ) :
    normalizeFinite μ ≤ δ⁻¹ • μ := by
  apply Measure.le_iff.mpr
  intro U hU
  simp only [normalizeFinite,Measure.smul_apply,smul_eq_mul]
  gcongr

lemma measurable_normalizeFinite {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Ω → Measure α) (hμ : Measurable μ) : Measurable (fun ω => normalizeFinite (μ ω)) := by
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [normalizeFinite,Measure.smul_apply,smul_eq_mul]
  exact (((Measure.measurable_coe MeasurableSet.univ).comp hμ).inv).mul
    ((Measure.measurable_coe hU).comp hμ)

noncomputable def selectedFiniteKernel {α : Type*} [MeasurableSpace α]
    (D : Measure α) (E : Set α) (dummy : α) (failure strict : Prop)
    [Decidable failure] [Decidable strict] : Measure α :=
  if failure then Measure.dirac dummy else normalizeFinite (if strict then D.restrict E else D)

lemma selectedFiniteKernel_probability {α : Type*} [MeasurableSpace α]
    (D : Measure α) [IsFiniteMeasure D] (E : Set α) (dummy : α) (failure strict : Prop)
    [Decidable failure] [Decidable strict]
    (hD : ¬failure → D Set.univ ≠ 0) (hE : ¬failure → strict → D E ≠ 0) :
    IsProbabilityMeasure (selectedFiniteKernel D E dummy failure strict) := by
  by_cases hf : failure
  · simp only [selectedFiniteKernel,ite_eq_left hf]; infer_instance
  simp only [selectedFiniteKernel,ite_eq_right hf]
  by_cases hs : strict
  · simp only [ite_eq_left hs]
    apply normalizeFinite_probability
    · simpa using hE hf hs
    · exact measure_ne_top _ _
  · simp only [ite_eq_right hs]
    exact normalizeFinite_probability D (hD hf) (measure_ne_top _ _)

lemma selectedFiniteKernel_domination {α : Type*} [MeasurableSpace α]
    (D : Measure α) (E : Set α) (dummy : α) (failure strict : Prop)
    [Decidable failure] [Decidable strict] {δ : ℝ≥0∞} (hδ : δ ≠ 0)
    (hf : ¬failure) (hD : δ ≤ D Set.univ) (hE : strict → δ ≤ D E) :
    selectedFiniteKernel D E dummy failure strict ≤ δ⁻¹ • D := by
  simp only [selectedFiniteKernel,ite_eq_right hf]
  by_cases hs : strict
  · simp only [ite_eq_left hs]
    exact (normalizeFinite_domination _ hδ (by simpa using hE hs)).trans
      (by
        apply Measure.le_iff.mpr
        intro U hU
        simp only [Measure.smul_apply,smul_eq_mul]
        gcongr
        exact Measure.restrict_le_self)
  · simp only [ite_eq_right hs]
    exact normalizeFinite_domination D hδ hD

lemma selectedFiniteKernel_measurable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (D : Ω → Measure α) (hD : Measurable D) (E : Set α) (hE : MeasurableSet E)
    (dummy : α) (failure strict : Ω → Prop) [DecidablePred failure] [DecidablePred strict]
    (hf : MeasurableSet {ω | failure ω}) (hs : MeasurableSet {ω | strict ω}) :
    Measurable (fun ω => selectedFiniteKernel (D ω) E dummy (failure ω) (strict ω)) := by
  unfold selectedFiniteKernel
  apply Measurable.ite hf measurable_const
  apply measurable_normalizeFinite
  apply Measurable.ite hs _ hD
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [Measure.restrict_apply hU]
  exact (Measure.measurable_coe (hU.inter hE)).comp hD

end DirectionalTransience

end

end

end OAI
