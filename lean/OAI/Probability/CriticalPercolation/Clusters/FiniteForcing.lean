import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.ClosedCutProbability

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

private lemma forceOn_mem_iff (S σ ω : Set E) (edge : E) :
    edge ∈ forceOn S σ ω ↔ if edge ∈ S then edge ∈ σ else edge ∈ ω := Iff.rfl

lemma forceOn_insert (S : Set E) (e : E) (σ ω : Set E) :
    forceOn (insert e S) σ ω = forceOn {e} σ (forceOn S σ ω) := by
  classical
  ext edge
  simp only [forceOn_mem_iff]
  by_cases hedge : edge = e <;> simp [hedge]

lemma forceOn_empty_eq_sdiff (S ω : Set E) : forceOn S ∅ ω = ω \ S := by
  classical
  ext e
  show (if e∈S then e∈(∅ : Set E) else e∈ω) ↔ _
  split_ifs <;> simp_all

lemma finite_forceOn_preimage_null (q : E → unitInterval)
    (hq : ∀ e, (q e : ℝ)∈Set.Ioo 0 1) (S : Set E) (hS : S.Finite) (σ : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) (hnull : law q A=0) :
    law q (forceOn S σ ⁻¹' A)=0 := by
  classical
  induction S,hS using Set.Finite.induction_on generalizing A with
  | empty =>
    have he : forceOn (∅ : Set E) σ = id := by
      funext ω
      ext edge
      simp only [forceOn_mem_iff, Set.mem_empty_iff_false, ite_false, id_eq]
    rwa [he,Set.preimage_id_eq]
  | @insert e S he hS ih =>
    have hb : bitMeasure (q e) {e∈σ} ≠ 0 := by
      by_cases h : e∈σ
      · simpa only [h] using bitMeasure_true_ne_zero (q e) (hq e).1
      · simpa only [h] using bitMeasure_false_ne_zero (q e) (hq e).2
    have hi := force_singleton_preimage_null q e σ hb A hA hnull
    have hm : Measurable (forceOn ({e} : Set E) σ) :=
      (measurable_forceOn_block {e} σ).mono (blockSigma_le _) le_rfl
    have hh := ih (forceOn {e} σ ⁻¹' A) (hA.preimage hm) hi
    simpa only [Set.preimage_preimage,Function.comp_def,←forceOn_insert] using hh

lemma ae_finite_forceOn (q : E → unitInterval)
    (hq : ∀ e, (q e : ℝ)∈Set.Ioo 0 1) (S : Set E) (hS : S.Finite) (σ : Set E)
    (P : Set E → Prop) (hm : Measurable P) (h : ∀ᵐ ω ∂law q, P ω) :
    ∀ᵐ ω ∂law q, P (forceOn S σ ω) := by
  rw [ae_iff] at h ⊢
  exact finite_forceOn_preimage_null q hq S hS σ {ω | ¬P ω} hm.not.setOf h

end CriticalPercolation.BernoulliProduct
end
end

end OAI
