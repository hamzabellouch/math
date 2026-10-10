import Mathlib
import OAI.Probability.CriticalPercolation.Gluing.ConditionalGluing
import OAI.Probability.CriticalPercolation.ProductMeasure.ProductEmbedding

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def withSource (A : Set V) : BondGraph (Option V) (E⊕A) where
  ends e := match e with
    | Sum.inl b => Sym2.map Option.some (G.ends b)
    | Sum.inr a => s(none,some a.val)

lemma withSource_local (hl : G.LocallyFinite) {A : Set V} (hA : A.Finite) :
    (G.withSource A).LocallyFinite := by
  intro v
  have hw : (Set.range (Sum.inr : A → E⊕A)).Finite := by
    let := hA.fintype
    exact Set.finite_range _
  cases v with
  | none =>
    apply hw.subset
    intro e he
    cases e with
    | inl e => simp [withSource] at he
    | inr a => exact ⟨a,rfl⟩
  | some v =>
    apply ((hl v).image Sum.inl |>.union hw).subset
    intro e he
    cases e with
    | inl e =>
      apply Or.inl
      refine ⟨e,?_,rfl⟩
      simpa [withSource] using he
    | inr a => exact Or.inr ⟨a,rfl⟩

lemma withSource_original_adj (A : Set V) (ω : Set (E⊕A)) {v w : V}
    (h : (G.openGraph (Sum.inl ⁻¹' ω)).Adj v w) :
    ((G.withSource A).openGraph ω).Adj (some v) (some w) := by
  obtain ⟨⟨e,he,hend⟩,hne⟩ := h
  exact ⟨⟨Sum.inl e,he,by simp [withSource,hend]⟩,fun h => hne (Option.some.inj h)⟩

lemma withSource_original_reachable (A : Set V) (ω : Set (E⊕A)) {v w : V}
    (h : (G.openGraph (Sum.inl ⁻¹' ω)).Reachable v w) :
    ((G.withSource A).openGraph ω).Reachable (some v) (some w) :=
  h.map ⟨Option.some,fun hvw => G.withSource_original_adj A ω hvw⟩

lemma withSource_seedHit [Countable V] [Countable E] (A B T : Set V)
    (q : (E⊕A) → unitInterval) :
    (BernoulliProduct.law (fun e => q (Sum.inl e))).real (G.seedHitEvent B T) ≤
      (BernoulliProduct.law q).real ((G.withSource A).seedHitEvent (Option.some '' B) (Option.some '' T)) := by
  have hm : Measurable (fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω : Set (E⊕A) → Set E) :=
    Measurable.of_eval (fun edge => measurable_set_mem (Sum.inl edge))
  have hlaw : BernoulliProduct.law (fun e => q (Sum.inl e)) =
      (BernoulliProduct.law q).map (fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) :=
    (BernoulliProduct.law_map_preimage q Sum.inl Sum.inl_injective).symm
  rw [hlaw,measureReal_def,
    Measure.map_apply hm (G.measurableSet_seedHitEvent B T)]
  change (BernoulliProduct.law q).real ((fun ω => Sum.inl ⁻¹' ω) ⁻¹' G.seedHitEvent B T) ≤ _
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  obtain ⟨v,hv,w,hvw,hw⟩ := Set.mem_iUnion₂.mp hω
  exact Set.mem_iUnion₂.mpr ⟨some v,⟨v,hv,rfl⟩,some w,
    G.withSource_original_reachable A ω hvw,⟨w,hw,rfl⟩⟩

lemma withSource_incident (A : Set V) {v : V} (hv : v∉A) :
    (G.withSource A).incidentEdges {some v}=Sum.inl '' G.incidentEdges {v} := by
  ext e
  cases e with
  | inl e => simp [incidentEdges,withSource]
  | inr a =>
    have hne : v≠a.val := fun hh => hv (hh.symm ▸ a.property)
    simp [incidentEdges,withSource,hne]

lemma withSource_trial_reachable (A : Set V) (F : Set E) {v w : V}
    (h : (G.openGraph F).Reachable v w) :
    ((G.withSource A).openGraph (Sum.inl '' F)).Reachable (some v) (some w) := by
  apply G.withSource_original_reachable
  simpa only [Set.preimage_image_eq _ Sum.inl_injective] using h

end CriticalPercolation.BondGraph
end
end
end

end OAI
