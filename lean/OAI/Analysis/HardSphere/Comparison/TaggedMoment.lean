import Mathlib
import OAI.Analysis.HardSphere.Comparison.MixtureMoment

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {I X : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X]

def taggedReference (P : Measure X) (E : I→Set X) : Measure (I×X) :=
  (Measure.count.prod P).restrict {p | p.2∈E p.1}
lemma taggedEvent_measurable (E : I→Set X) (hE : ∀i,MeasurableSet (E i)) :
    MeasurableSet {p : I×X | p.2∈E p.1} := by
  have he : {p : I×X | p.2∈E p.1}=⋃i,({i}:Set I)×ˢE i := by ext p; simp
  rw [he]
  exact MeasurableSet.iUnion (fun i ↦ (measurableSet_singleton i).prod (hE i))
lemma taggedFunction_measurable (f : I→X→ℝ≥0∞) (hf : ∀i,Measurable (f i)) :
    Measurable (fun p : I×X ↦ f p.1 p.2) :=
  measurable_from_prod_countable_right hf

lemma tagged_density_square (P : Measure X) [SFinite P] (E : I→Set X)
    (f : I→X→ℝ≥0∞) (hf : ∀i,Measurable (f i)) :
    (∫⁻p,(f p.1 p.2)^2 ∂taggedReference P E)≤∫⁻x,(∑i,f i x)^2 ∂P := by
  apply (lintegral_mono' Measure.restrict_le_self (le_refl _)).trans
  rw [lintegral_prod _ (taggedFunction_measurable (fun i x ↦ (f i x)^2) (fun i ↦ (hf i).pow_const 2)).aemeasurable]
  rw [lintegral_count,tsum_fintype]
  exact tag_likelihood_square P f hf

lemma tagged_full_density (P : Measure X) (E : I→Set X) (hE : ∀i,MeasurableSet (E i))
    (f : I→X→ℝ≥0∞) (hzero : ∀i x,x∉E i→f i x=0) :
    (Measure.count.prod P).withDensity (fun p ↦ f p.1 p.2)=
      (taggedReference P E).withDensity (fun p ↦ f p.1 p.2) := by
  rw [taggedReference,←withDensity_indicator (taggedEvent_measurable E hE)]
  congr 1
  funext p
  by_cases hp : p.2∈E p.1
  · simp [hp]
  · simp [hp,hzero p.1 p.2 hp]

lemma tagged_density_moment (P : Measure X) [IsFiniteMeasure P] (E : I→Set X)
    (f : I→X→ℝ≥0∞) (hf : ∀i,Measurable (f i)) (C : ℝ) (hC : 0≤C)
    (hbound : (∫⁻x,(∑i,f i x)^2 ∂P)≤ENNReal.ofReal C) :
    Integrable (fun p ↦ (f p.1 p.2).toReal^2) (taggedReference P E) ∧
      (∫p,(f p.1 p.2).toReal^2 ∂taggedReference P E)≤C := by
  let R := taggedReference P E
  let F : I×X→ℝ≥0∞ := fun p ↦ (f p.1 p.2)^2
  have hF : Measurable F := (taggedFunction_measurable f hf).pow_const 2
  have hb : (∫⁻p,F p ∂ R)≤ENNReal.ofReal C := (tagged_density_square P E f hf).trans hbound
  have hfin : (∫⁻p,F p ∂ R)≠⊤ := ne_of_lt (hb.trans_lt ENNReal.ofReal_lt_top)
  have haef := ae_lt_top hF hfin
  have hi := integrable_toReal_of_lintegral_ne_top hF.aemeasurable hfin
  constructor
  · simpa only [F,ENNReal.toReal_pow] using hi
  · have he := integral_toReal hF.aemeasurable haef
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rw [ENNReal.toReal_ofReal hC] at hh
    calc
      _ = (∫⁻p,F p ∂ R).toReal := by simpa only [F,ENNReal.toReal_pow] using he
      _ ≤ C := hh

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
attribute [local instance] Classical.propDecidable
variable {Q X I : Type*} [MeasurableSpace Q] [MeasurableSpace X]
  [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

def tagLikelihood (σ : Measure Q) (tag : Q→I) (L : Q×X→ℝ≥0∞) (i : I) (x : X) : ℝ≥0∞ :=
  ∫⁻q,if tag q=i then L (q,x) else 0 ∂σ
lemma tagLikelihood_measurable (σ : Measure Q) [SFinite σ] (tag : Q→I)
    (ht : Measurable tag) (L : Q×X→ℝ≥0∞) (hL : Measurable L) (i : I) :
    Measurable (tagLikelihood σ tag L i) := by
  apply Measurable.lintegral_prod_left
  exact hL.ite (measurableSet_eq_fun (ht.comp measurable_fst) measurable_const) measurable_const

lemma sum_tagLikelihood (σ : Measure Q) (tag : Q→I) (ht : Measurable tag)
    (L : Q×X→ℝ≥0∞) (hL : Measurable L) (x : X) :
    (∑i,tagLikelihood σ tag L i x)=∫⁻q,L (q,x) ∂σ := by
  classical
  simp only [tagLikelihood]
  rw [←lintegral_finsetSum]
  · apply lintegral_congr
    intro q
    simp
  · intro i _
    exact (hL.comp measurable_prodMk_right).ite (measurableSet_eq_fun ht measurable_const) measurable_const

lemma tagged_mixture_density (σ : Measure Q) (P : Measure X) [SFinite σ] [SFinite P]
    (tag : Q→I) (ht : Measurable tag) (L : Q×X→ℝ≥0∞) (hL : Measurable L) :
    ((σ.prod P).withDensity L).map (fun p ↦ (tag p.1,p.2))=
      (Measure.count.prod P).withDensity (fun p ↦ tagLikelihood σ tag L p.1 p.2) := by
  classical
  let T : Q×X→I×X := fun p ↦ (tag p.1,p.2)
  have hm : Measurable T := (ht.comp measurable_fst).prodMk measurable_snd
  have hl : Measurable (fun p : I×X ↦ tagLikelihood σ tag L p.1 p.2) :=
    taggedFunction_measurable _ (tagLikelihood_measurable σ tag ht L hL)
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hm]
  change (∫⁻a,(F∘T) a ∂(σ.prod P).withDensity L)=_
  rw [lintegral_withDensity_eq_lintegral_mul _ hL (hF.comp hm),
    lintegral_withDensity_eq_lintegral_mul _ hl hF]
  rw [lintegral_prod _ (hl.mul hF).aemeasurable,lintegral_count,tsum_fintype]
  have hi (i : I) : (∫⁻x,tagLikelihood σ tag L i x*F (i,x) ∂P)=
      ∫⁻q,∫⁻x,(if tag q=i then L (q,x) else 0)*F (i,x) ∂P ∂σ := by
    unfold tagLikelihood
    have he (x : X) : (∫⁻q,if tag q=i then L (q,x) else 0 ∂σ)*F (i,x)=
        ∫⁻q,(if tag q=i then L (q,x) else 0)*F (i,x) ∂σ :=
      (lintegral_mul_const _ ((hL.comp measurable_prodMk_right).ite
        (measurableSet_eq_fun ht measurable_const) measurable_const)).symm
    simp_rw [he]
    apply lintegral_lintegral_swap
    exact (((hL.comp measurable_swap).ite
      (measurableSet_eq_fun (ht.comp measurable_snd) measurable_const) measurable_const).mul
      ((hF.comp measurable_prodMk_left).comp measurable_fst)).aemeasurable
  simp only [Pi.mul_apply,Function.comp_apply]
  simp_rw [hi]
  rw [←lintegral_finsetSum]
  · rw [lintegral_prod _ (show Measurable (fun p : Q×X ↦ L p*F (T p)) from hL.mul (hF.comp hm)).aemeasurable]
    apply lintegral_congr
    intro q
    rw [←lintegral_finsetSum]
    · apply lintegral_congr
      intro x
      simp [T]
    · intro i _
      exact (((hL.comp measurable_prodMk_left).ite (by measurability) measurable_const).mul
        (hF.comp measurable_prodMk_left))
  · intro i _
    exact (((hL.ite (measurableSet_eq_fun (ht.comp measurable_fst) measurable_const) measurable_const).mul
      ((hF.comp measurable_prodMk_left).comp measurable_snd))).lintegral_prod_right

end HardSphere.Comparison

end
end

end

end OAI
