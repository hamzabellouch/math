import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FixedIsTagged
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BitWeight

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

abbrev LocalToken (ℓ : ℕ) := Bool × Bool × Finset (Fin ℓ)

def tokenEdges (t : LocalToken ℓ) : Finset (Fin ℓ) := t.2.2

def taggedPieces (w : ClosedLine h ℓ) (hh : 0 < h) (O E : Finset (Fin ℓ)) :
    Finset (LocalToken ℓ) :=
  (edgeComponents w hh E).image (fun c => (true,false,componentEdges w hh E c)) ∪
    (O \ E).image (fun e => (true,true,({e} : Finset (Fin ℓ))))

lemma taggedPieces_cover (w : ClosedLine h ℓ) (hh : 0 < h) (O E : Finset (Fin ℓ))
    (hE : E ⊆ O) :
    (taggedPieces w hh O E).biUnion tokenEdges = O := by
  ext e
  simp only [taggedPieces,mem_biUnion,mem_union,mem_image,tokenEdges]
  constructor
  · rintro ⟨t,(⟨c,hc,rfl⟩ | ⟨j,hj,rfl⟩),he⟩
    · exact hE (componentEdges_subset w hh E c he)
    · simpa only [mem_singleton.mp he] using (Finset.mem_sdiff.mp hj).1
  · intro he
    by_cases heE : e ∈ E
    · obtain ⟨c,hc,hec⟩ := mem_biUnion.mp ((componentEdges_biUnion w hh E).symm ▸ heE)
      exact ⟨(true,false,componentEdges w hh E c),Or.inl ⟨c,hc,rfl⟩,hec⟩
    · exact ⟨(true,true,{e}),Or.inr ⟨e,Finset.mem_sdiff.mpr ⟨he,heE⟩,rfl⟩,mem_singleton_self e⟩

def localTokenWeight (w : ClosedLine h ℓ) (p : S.Index) (t : LocalToken ℓ) : ℝ :=
  if t.1 then if t.2.1 then 2 else subtreeUnionWeight w p (tokenEdges t)
  else modifiedWeight w p (tokenEdges t)

lemma localTokenWeight_nonneg (w : ClosedLine h ℓ) (p : S.Index) (t : LocalToken ℓ) :
    0 ≤ localTokenWeight w p t := by
  unfold localTokenWeight
  split_ifs
  · norm_num
  · exact subtreeUnionWeight_nonneg w p _
  · exact modifiedWeight_nonneg w p _

lemma componentEdges_injOn (w : ClosedLine h ℓ) (hh : 0 < h) (E : Finset (Fin ℓ)) :
    Set.InjOn (componentEdges w hh E) (edgeComponents w hh E) := by
  intro c hc d hd hcd
  obtain ⟨e,he⟩ := componentEdges_nonempty w hh E c hc
  have hed := hcd ▸ he
  exact (mem_filter.mp he).2.symm.trans (mem_filter.mp hed).2

lemma taggedPieces_weight (w : ClosedLine h ℓ) (hh : 0 < h) (p : S.Index)
    (E : Finset (Fin ℓ)) :
    (∏ t ∈ taggedPieces w hh (treeOccurrences w p) E, localTokenWeight w p t) =
      taggedFixedWeight w hh p E := by
  have hd : Disjoint
      ((edgeComponents w hh E).image (fun c => (true,false,componentEdges w hh E c)))
      (((treeOccurrences w p) \ E).image (fun e => (true,true,({e} : Finset (Fin ℓ))))) := by
    apply disjoint_left.mpr
    intro t ht hs
    obtain ⟨c,hc,rfl⟩ := mem_image.mp ht
    obtain ⟨e,he,hte⟩ := mem_image.mp hs
    have := congrArg (fun t : LocalToken ℓ => t.2.1) hte
    contradiction
  rw [taggedPieces,prod_union hd,prod_image (fun c hc d hd hcd =>
    componentEdges_injOn w hh E hc hd (congrArg (fun t : LocalToken ℓ => t.2.2) hcd))]
  rw [prod_image (fun e he j hj h => singleton_injective (congrArg (fun t : LocalToken ℓ => t.2.2) h))]
  rfl

def freePiece (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) (p : S.Index)
    (e : Fin ℓ) : LocalToken ℓ :=
  if singletonIsTagged w 𝔏 p e then (true,true,{e}) else (false,false,{e})

lemma freePiece_edges (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (p : S.Index) (e : Fin ℓ) : tokenEdges (freePiece w 𝔏 p e) = {e} := by
  unfold freePiece
  split_ifs <;> rfl

lemma freePiece_injective (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) (p : S.Index) :
    Function.Injective (freePiece w 𝔏 p) := by
  intro e j he
  have ht := congrArg tokenEdges he
  simp only [freePiece_edges] at ht
  exact singleton_injective ht

def recordTokens (w : ClosedLine h ℓ) (hh : 0 < h) (𝔏 : List (AttachedSpec w D L))
    (R : AssignedRecord S ℓ) (p : S.Index) : Finset (LocalToken ℓ) :=
  if (treeOccurrences w p).Nonempty then
    if S.IsFixed w p then
      if R.2 p then taggedPieces w hh (treeOccurrences w p) (R.1 p)
      else {(false,false,R.1 p)}
    else (treeOccurrences w p).image (freePiece w 𝔏 p)
  else ∅

theorem recordTokens_cover (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index) :
    (recordTokens w hh 𝔏 (recordAt w hh 𝔏 a) p).biUnion tokenEdges = treeOccurrences w p := by
  by_cases ho : (treeOccurrences w p).Nonempty
  · rw [recordTokens,ite_eq_left ho]
    by_cases hf : S.IsFixed w p
    · rw [ite_eq_left hf]
      let pf : S.FixedIndex w := ⟨p,hf⟩
      by_cases ht : (recordAt w hh 𝔏 a).2 p = true
      · rw [ite_eq_left ht]
        exact taggedPieces_cover w hh _ _ (recordAt_compatible w hh 𝔏 a p)
      · rw [ite_eq_right ht]
        rw [Finset.singleton_biUnion]
        change (recordAt w hh 𝔏 a).1 p = treeOccurrences w p
        rw [recordAt_edges w hh 𝔏 a pf]
        exact untagged_fixed_edges w hh 𝔏 p (a pf)
          (fun h => ht ((recordAt_tag w hh 𝔏 a pf ho).mpr h))
    · rw [ite_eq_right hf]
      ext e
      simp only [mem_biUnion,mem_image]
      constructor
      · rintro ⟨t,⟨j,hj,rfl⟩,he⟩
        rw [freePiece_edges] at he
        simpa only [mem_singleton.mp he] using hj
      · intro he
        exact ⟨freePiece w 𝔏 p e,⟨e,he,rfl⟩,by rw [freePiece_edges]; exact mem_singleton_self _⟩
  · rw [recordTokens,ite_eq_right ho]
    simpa only [biUnion_empty] using (not_nonempty_iff_eq_empty.mp ho).symm

theorem recordTokens_recover_label (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w)
    (hlabels : ∀ i, w.label i ∈ D.members) (e : Fin ℓ) (he : e ∈ w.treeSteps) :
    (∏ p : S.Index, if ∃ t ∈ recordTokens w hh 𝔏 (recordAt w hh 𝔏 a) p,
      e ∈ tokenEdges t then (p : ℕ) else 1) = w.label e := by
  have ht (p : S.Index) : (∃ t ∈ recordTokens w hh 𝔏 (recordAt w hh 𝔏 a) p,
      e ∈ tokenEdges t) ↔ (p : ℕ) ∣ w.label e := by
    rw [← mem_biUnion,recordTokens_cover]
    simp only [treeOccurrences,mem_filter,he,true_and]
  simp_rw [ht]
  rw [prod_coe_sort S.primes (fun p : ℕ => if p ∣ w.label e then p else 1),← prod_filter]
  have hp : S.primes.filter (fun p => p ∣ w.label e) = (w.label e).primeFactors := by
    ext p
    constructor
    · intro hp
      obtain ⟨hp,hpd⟩ := mem_filter.mp hp
      exact Nat.mem_primeFactors.mpr ⟨S.prime_mem p hp,hpd,ne_of_gt (w.label_pos e)⟩
    · intro hp
      exact mem_filter.mpr ⟨D.support _ (hlabels e) hp,(Nat.mem_primeFactors.mp hp).2.1⟩
  rw [hp,Nat.prod_primeFactors_of_squarefree (D.squarefree _ (hlabels e))]

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
