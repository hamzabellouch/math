import OAI.Probability.InvariantIsing.Fields.FieldWasserstein

namespace OAI

/-! Comparing simple fields through an arbitrary joint law of their arguments. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

variable (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)

include hcompact hbound ha hb

lemma simpleFieldValue_comp {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : Ω → Ξ) (hf : Measurable f) (he : P.map f=Q) (s : SimpleFunc Ξ ℝ) :
    simpleFieldValue P (s.comp f hf) (measureR (ν : Measure ℝ) b)=
      simpleFieldValue Q s (measureR (ν : Measure ℝ) b) := by
  apply simpleFieldValue_eq_of_map_eq ν a b hcompact hbound ha hb
  change P.map (s ∘ f)=Q.map s
  rw [← Measure.map_map s.measurable hf,he]

lemma fieldCoupling_simple_error {μ ξ : ProbabilityMeasure ℝ} (p : FieldLawCoupling μ ξ)
    (hμ : Integrable (fun x : ℝ => x) (μ : Measure ℝ))
    (hξ : Integrable (fun x : ℝ => x) (ξ : Measure ℝ)) (s t : SimpleFunc ℝ ℝ) :
    |simpleFieldValue (μ : Measure ℝ) s (measureR (ν : Measure ℝ) b)-
      simpleFieldValue (ξ : Measure ℝ) t (measureR (ν : Measure ℝ) b)| ≤
      (∫ x, |s x-x| ∂(μ : Measure ℝ))+
      (∫ xy, |xy.1-xy.2| ∂(p.law : Measure (ℝ × ℝ)))+
      (∫ y, |t y-y| ∂(ξ : Measure ℝ)) := by
  let P := (p.law : Measure (ℝ × ℝ))
  let S : SimpleFunc (ℝ × ℝ) ℝ := s.comp Prod.fst measurable_fst
  let T : SimpleFunc (ℝ × ℝ) ℝ := t.comp Prod.snd measurable_snd
  have hS := simpleFieldValue_comp ν a b hcompact hbound ha hb P (μ : Measure ℝ)
    Prod.fst measurable_fst p.fst s
  have hT := simpleFieldValue_comp ν a b hcompact hbound ha hb P (ξ : Measure ℝ)
    Prod.snd measurable_snd p.snd t
  rw [← hS,← hT]
  refine (simpleFieldValue_abs_sub_le ν a b hcompact hbound ha hb P S T).trans ?_
  have iS := ((simpleField_integrable P S).sub (p.integrable_fst hμ)).abs
  have iM := ((p.integrable_fst hμ).sub (p.integrable_snd hξ)).abs
  have iT := ((simpleField_integrable P T).sub (p.integrable_snd hξ)).abs
  have eS : (∫ xy, |S xy-xy.1| ∂P)=∫ x, |s x-x| ∂(μ : Measure ℝ) := by
    rw [← p.fst,integral_map measurable_fst.aemeasurable]
    · rfl
    · exact ((s.measurable.sub measurable_id).abs).aestronglyMeasurable
  have eT : (∫ xy, |T xy-xy.2| ∂P)=∫ x, |t x-x| ∂(ξ : Measure ℝ) := by
    rw [← p.snd,integral_map measurable_snd.aemeasurable]
    · rfl
    · exact ((t.measurable.sub measurable_id).abs).aestronglyMeasurable
  have e1 := integral_add iS iM
  have e2 := integral_add (iS.add iM) iT
  dsimp only [Pi.add_apply,Pi.sub_apply] at e1 e2
  rw [← eS,← eT]
  change (∫ xy, |S xy-T xy| ∂P) ≤
    (∫ xy, |S xy-xy.1| ∂P)+(∫ xy, |xy.1-xy.2| ∂P)+(∫ xy, |T xy-xy.2| ∂P)
  rw [← e1,← e2]
  apply integral_mono ((simpleField_integrable P S).sub (simpleField_integrable P T)).abs
    ((iS.add iM).add iT)
  intro xy
  change |S xy-T xy| ≤ (|S xy-xy.1|+|xy.1-xy.2|)+|T xy-xy.2|
  have h1 := abs_sub_le (S xy) xy.1 xy.2
  have h2 := abs_sub_le (S xy) xy.2 (T xy)
  rw [abs_sub_comm xy.2 (T xy)] at h2
  linarith

end InvariantIsing

end

end OAI
