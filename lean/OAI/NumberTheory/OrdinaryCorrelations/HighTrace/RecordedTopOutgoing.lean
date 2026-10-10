import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TaggedShape

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

lemma recordedTop_outgoing (w : ClosedLine h ℓ) (E : Finset (Fin ℓ)) (v : ℤ)
    (hv : v ∈ recordedTops w E) : ∃ e ∈ E, w.offset e.castSucc=v := by
  obtain ⟨hv,hn⟩ := mem_sdiff.mp hv
  rcases mem_union.mp hv with ho | hi
  · exact mem_image.mp ho
  · exact (hn hi).elim

lemma fixed_record_token_lit_subset (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index)
    (hp : S.IsFixed w p) (t : LocalToken ℓ)
    (ht : t ∈ recordTokens w hh 𝔏 (recordAt w hh 𝔏 a) p) (hg : t.2.1=false) :
    tokenEdges t ⊆ (recordAt w hh 𝔏 a).1 p := by
  intro e he
  rw [← recordTokens_fixed_lit w hh 𝔏 a p hp]
  exact mem_biUnion.mpr ⟨t,mem_filter.mpr ⟨ht,hg⟩,he⟩

lemma shape_top_of_recordedTop (w : ClosedLine h ℓ) (E : Finset (Fin ℓ)) (v : ℤ)
    (hv : v ∈ recordedTops w E) (Q : Shape w) (hQ : Q.edges.val ⊆ E)
    (e : Fin ℓ) (he : e ∈ Q.edges.val) (hev : w.offset e.castSucc=v) : Q.top.val=v := by
  rcases Q.grows.2 e he with h | ⟨j,hj,_,hjv⟩
  · exact h.symm.trans hev
  · exact ((mem_sdiff.mp hv).2 (mem_image.mpr ⟨j,hQ hj,hjv.trans hev⟩)).elim

theorem good_origin_core_token (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (v : ℤ)
    (hv : v ∈ goodOrigins w) (hU : v ∉ recordU w (recordAt w hh 𝔏 a).1) :
    (∃ p : S.Index, S.IsCore p ∧ ∃ Q : Shape w,
      taggedShapeCode w (.inl Q) ∈ taggedTokens w hh 𝔏 (recordAt w hh 𝔏 a) p ∧ Q.top.val=v) ∨
    (∃ p : S.Index, ∃ t : TokenType w, untaggedType w hh 𝔏 a p=some t ∧ t.1=true ∧ t.2.top.val=v) := by
  have hex : ∃ p : S.Index, S.IsCore p ∧ v ∈ recordedTops w ((recordAt w hh 𝔏 a).1 p) := by
    by_contra hn
    push Not at hn
    exact hU (mem_filter.mpr ⟨hv,hn⟩)
  obtain ⟨p,hpcore,hpv⟩ := hex
  obtain ⟨e,he,hev⟩ := recordedTop_outgoing w _ v hpv
  have hep := recordAt_compatible w hh 𝔏 a p he
  have hpfixed : S.IsFixed w p := ⟨⟨e,(mem_filter.mp hep).2⟩,Or.inl hpcore⟩
  have _helit := he
  rw [← recordTokens_fixed_lit w hh 𝔏 a p hpfixed] at he
  obtain ⟨t,ht,het⟩ := mem_biUnion.mp he
  obtain ⟨ht,hghost⟩ := mem_filter.mp ht
  have hsub := fixed_record_token_lit_subset w hh 𝔏 a p hpfixed t ht hghost
  by_cases htag : t.1=true
  · have htagmem : t ∈ taggedTokens w hh 𝔏 (recordAt w hh 𝔏 a) p := mem_filter.mpr ⟨ht,htag⟩
    obtain ⟨s,hs⟩ := record_tagged_shape w hh 𝔏 a p t htagmem
    cases s with
    | inl Q =>
      have hQ : Q.edges.val=tokenEdges t := congrArg tokenEdges hs
      refine Or.inl ⟨p,hpcore,Q,hs ▸ htagmem,?_⟩
      exact shape_top_of_recordedTop w _ v hpv Q (hQ.symm ▸ hsub) e (hQ.symm ▸ het) hev
    | inr j =>
      have hg : t.2.1=true := (congrArg (fun t : LocalToken ℓ => t.2.1) hs).symm
      rw [hghost] at hg
      contradiction
  · have htagfalse : t.1=false := Bool.eq_false_iff.mpr htag
    have hhas : HasUntagged w hh 𝔏 (recordAt w hh 𝔏 a) p := ⟨t,ht,htagfalse⟩
    let Q := untaggedShape w hh 𝔏 a p hhas
    have hQ : Q.edges.val=tokenEdges t := by
      have ht' := ht
      rw [untaggedShape_spec w hh 𝔏 a p hhas] at ht'
      exact (congrArg tokenEdges (mem_singleton.mp ht')).symm
    refine Or.inr ⟨p,(true,Q),?_,rfl,?_⟩
    · simp only [untaggedType,dite_eq_left hhas,hpcore,decide_true, Q]
    · exact shape_top_of_recordedTop w _ v hpv Q (hQ.symm ▸ hsub) e (hQ.symm ▸ het) hev

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
