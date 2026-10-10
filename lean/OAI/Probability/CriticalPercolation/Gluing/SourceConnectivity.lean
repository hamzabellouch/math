import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.HitEvent
import OAI.Probability.CriticalPercolation.Criticality.FiniteEnergy
import OAI.Probability.CriticalPercolation.ProductMeasure.ProductEmbedding
import OAI.Probability.CriticalPercolation.Gluing.SourceGraph
import OAI.Probability.CriticalPercolation.Gluing.SourceLift

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma withSource_reachable_from_seed (A : Set V) (ω : Set (E⊕A))
    (hw : ∀ a : A, Sum.inr a∈ω) {v : V}
    (hv : ∃ a∈A, (G.openGraph (Sum.inl ⁻¹' ω)).Reachable a v) :
    ((G.withSource A).openGraph ω).Reachable none (some v) := by
  obtain ⟨a,ha,hav⟩ := hv
  have hh : ((G.withSource A).openGraph ω).Adj none (some a) :=
    ⟨⟨Sum.inr ⟨a,ha⟩,hw ⟨a,ha⟩,rfl⟩,by simp⟩
  exact hh.reachable.trans (G.withSource_original_reachable A ω hav)

lemma withSource_reachable_to_seed (A : Set V) (ω : Set (E⊕A)) {v : V}
    (hv : ((G.withSource A).openGraph ω).Reachable none (some v)) :
    ∃ a∈A, (G.openGraph (Sum.inl ⁻¹' ω)).Reachable a v := by
  have hi : ∀ w, ((G.withSource A).openGraph ω).Reachable none w →
      Option.elim' True (fun v => ∃ a∈A, (G.openGraph (Sum.inl ⁻¹' ω)).Reachable a v) w := by
    intro w hw
    rw [SimpleGraph.reachable_iff_reflTransGen] at hw
    induction hw with
    | refl => trivial
    | @tail u w hr huw ih =>
      obtain ⟨⟨b,hb,hend⟩,hne⟩ := huw
      cases w with
      | none => trivial
      | some w =>
        rcases G.withSource_edge_cases A b u (some w) hend with
          ⟨b,v,w',rfl,rfl,hw',hb'⟩|⟨a,rfl,hh⟩
        · have he : w'=w := Option.some.inj hw'.symm
          subst w'
          obtain ⟨a,ha,hav⟩ := ih
          refine ⟨a,ha,hav.trans ?_⟩
          exact (show (G.openGraph (Sum.inl ⁻¹' ω)).Adj v w from
            ⟨⟨b,hb,hb'⟩,fun h => hne (congrArg some h)⟩).reachable
        · rcases hh with ⟨rfl,hh⟩|⟨hh,_⟩
          · have he : w=a.val := Option.some.inj hh
            exact ⟨a.val,a.property,he.symm ▸ SimpleGraph.Reachable.refl _⟩
          · simp at hh
  exact hi (some v) hv

lemma source_hit_iff_seedHit (A T : Set V) (ω : Set (E⊕A))
    (hw : ∀ a : A, Sum.inr a∈ω) :
    ω∈(G.withSource A).hitEvent none (some '' T) ↔
      Sum.inl ⁻¹' ω∈G.seedHitEvent A T := by
  constructor
  · rintro ⟨w,hr,v,hv,rfl⟩
    obtain ⟨a,ha,hav⟩ := G.withSource_reachable_to_seed A ω hr
    exact Set.mem_iUnion₂.mpr ⟨a,ha,v,hav,hv⟩
  · intro h
    obtain ⟨a,ha,v,hav,hv⟩ := Set.mem_iUnion₂.mp h
    exact ⟨some v,G.withSource_reachable_from_seed A ω hw ⟨a,ha,hav⟩,v,hv,rfl⟩

lemma source_hit_probability [Countable V] [Countable E] (A T : Set V)
    (q : (E⊕A) → unitInterval) (hq : ∀ a : A, q (Sum.inr a)=1) :
    BernoulliProduct.law q ((G.withSource A).hitEvent none (some '' T))=
      BernoulliProduct.law (fun b => q (Sum.inl b)) (G.seedHitEvent A T) := by
  have ha (a : A) : ∀ᵐ ω ∂BernoulliProduct.law q, Sum.inr a∈ω := by
    rw [ae_iff]
    have he : {ω : Set (E⊕A) | ¬Sum.inr a∈ω}={ω | (Sum.inr a∈ω)=False} := by
      ext ω; simp
    rw [he,BernoulliProduct.law_coordinate,hq a]
    simp [BernoulliProduct.bitMeasure]
  have hall : ∀ᵐ ω ∂BernoulliProduct.law q, ∀ a : A, Sum.inr a∈ω := ae_all_iff.mpr ha
  have heq : BernoulliProduct.law q ((G.withSource A).hitEvent none (some '' T))=
      BernoulliProduct.law q ((fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) ⁻¹' G.seedHitEvent A T) := by
    apply measure_congr
    filter_upwards [hall] with ω hω
    exact propext (G.source_hit_iff_seedHit A T ω hω)
  rw [heq]
  change BernoulliProduct.law q ((fun ω : Set (E⊕A) => fun b => Sum.inl b∈ω) ⁻¹' G.seedHitEvent A T)=_
  rw [← Measure.map_apply
    (Measurable.of_eval (fun bond => measurable_set_mem (Sum.inl bond)))
    (G.measurableSet_seedHitEvent A T)]
  change (Measure.map (fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) (BernoulliProduct.law q)) (G.seedHitEvent A T)=_
  rw [BernoulliProduct.law_map_preimage q Sum.inl Sum.inl_injective]
  rfl

end CriticalPercolation.BondGraph
end
end
end

end OAI
