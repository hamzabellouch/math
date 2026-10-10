import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LocalToken

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

lemma freePiece_weight (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (p : S.Index) (hp : ¬S.IsCore p) (e : Fin ℓ) :
    localTokenWeight w p (freePiece w 𝔏 p e) = singletonTokenWeight w 𝔏 p e := by
  by_cases ht : singletonIsTagged w 𝔏 p e
  · simp [freePiece,localTokenWeight,singletonTokenWeight,ht]
  · by_cases hg : w.Good e <;>
      simp [freePiece,localTokenWeight,tokenEdges,modifiedWeight,hp,singletonTokenWeight,ht,hg]

theorem recordTokens_weight (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (R : AssignedRecord S ℓ) (p : S.Index) :
    (∏ t ∈ recordTokens w hh 𝔏 R p, localTokenWeight w p t) =
      recordTreeWeight w hh 𝔏 R p := by
  by_cases ho : (treeOccurrences w p).Nonempty
  · rw [recordTokens,recordTreeWeight,ite_eq_left ho,ite_eq_left ho]
    by_cases hf : S.IsFixed w p
    · rw [ite_eq_left hf,ite_eq_left hf]
      by_cases ht : R.2 p = true
      · rw [ite_eq_left ht,ite_eq_left ht]
        exact taggedPieces_weight w hh p _
      · rw [ite_eq_right ht,ite_eq_right ht,prod_singleton]
        rfl
    · rw [ite_eq_right hf,ite_eq_right hf,prod_image (fun e _ j _ he => freePiece_injective w 𝔏 p he)]
      have hc : ¬S.IsCore p := by
        intro hc
        obtain ⟨e,he⟩ := ho
        exact hf ⟨⟨e,(mem_filter.mp he).2⟩,Or.inl hc⟩
      exact prod_congr rfl (fun e he => freePiece_weight w 𝔏 p hc e)
  · rw [recordTokens,recordTreeWeight,ite_eq_right ho,ite_eq_right ho,prod_empty]

lemma taggedPieces_lit_cover (w : ClosedLine h ℓ) (hh : 0 < h)
    (O E : Finset (Fin ℓ)) :
    ((taggedPieces w hh O E).filter (fun t => t.2.1 = false)).biUnion tokenEdges = E := by
  ext e
  simp only [mem_biUnion,mem_filter,taggedPieces,mem_union,mem_image]
  constructor
  · rintro ⟨t,⟨(⟨c,hc,rfl⟩ | ⟨j,hj,rfl⟩),ht⟩,he⟩
    · exact componentEdges_subset w hh E c he
    · contradiction
  · intro he
    obtain ⟨c,hc,hec⟩ := mem_biUnion.mp ((componentEdges_biUnion w hh E).symm ▸ he)
    exact ⟨(true,false,componentEdges w hh E c),⟨Or.inl ⟨c,hc,rfl⟩,rfl⟩,hec⟩

lemma taggedPieces_tagged (w : ClosedLine h ℓ) (hh : 0 < h)
    (O E : Finset (Fin ℓ)) {t : LocalToken ℓ} (ht : t ∈ taggedPieces w hh O E) :
    t.1 = true := by
  rcases mem_union.mp ht with ht | ht <;>
    obtain ⟨i,hi,rfl⟩ := mem_image.mp ht <;> rfl

lemma taggedPieces_nonempty (w : ClosedLine h ℓ) (hh : 0 < h)
    (O E : Finset (Fin ℓ)) (hO : O.Nonempty) (hE : E ⊆ O) :
    (taggedPieces w hh O E).Nonempty := by
  have hcov := taggedPieces_cover w hh O E hE
  by_contra hn
  rw [not_nonempty_iff_eq_empty.mp hn,biUnion_empty] at hcov
  exact hO.ne_empty hcov.symm

lemma recordTokens_fixed_lit (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index)
    (hp : S.IsFixed w p) :
    ((recordTokens w hh 𝔏 (recordAt w hh 𝔏 a) p).filter (fun t => t.2.1 = false)).biUnion
      tokenEdges = (recordAt w hh 𝔏 a).1 p := by
  by_cases ho : (treeOccurrences w p).Nonempty
  · rw [recordTokens,ite_eq_left ho,ite_eq_left hp]
    split_ifs with ht
    · exact taggedPieces_lit_cover w hh _ _
    · simp only [filter_singleton,ite_true,singleton_biUnion,tokenEdges]
  · have he : (recordAt w hh 𝔏 a).1 p = ∅ :=
      eq_empty_iff_forall_notMem.mpr (fun e he => ho ⟨e,recordAt_compatible w hh 𝔏 a p he⟩)
    rw [recordTokens,ite_eq_right ho,filter_empty,biUnion_empty,he]

lemma recordTokens_fixed_tag (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index)
    (hp : S.IsFixed w p) :
    (∃ t ∈ recordTokens w hh 𝔏 (recordAt w hh 𝔏 a) p, t.1 = true) ↔
      (recordAt w hh 𝔏 a).2 p = true := by
  by_cases ho : (treeOccurrences w p).Nonempty
  · rw [recordTokens,ite_eq_left ho,ite_eq_left hp]
    by_cases ht : (recordAt w hh 𝔏 a).2 p = true
    · rw [ite_eq_left ht]
      constructor
      · intro _; exact ht
      · intro _
        obtain ⟨t,ht⟩ := taggedPieces_nonempty w hh _ _ ho (recordAt_compatible w hh 𝔏 a p)
        exact ⟨t,ht,taggedPieces_tagged w hh _ _ ht⟩
    · rw [ite_eq_right ht]
      simp [ht]
  · rw [recordTokens,ite_eq_right ho]
    simp [recordAt,hp,ho]

theorem recordTokens_injective_on_records (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a b : S.FixedResidues w)
    (ht : ∀ p, recordTokens w hh 𝔏 (recordAt w hh 𝔏 a) p =
      recordTokens w hh 𝔏 (recordAt w hh 𝔏 b) p) :
    recordAt w hh 𝔏 a = recordAt w hh 𝔏 b := by
  apply Prod.ext
  · funext p
    by_cases hp : S.IsFixed w p
    · rw [← recordTokens_fixed_lit w hh 𝔏 a p hp,
        ← recordTokens_fixed_lit w hh 𝔏 b p hp,ht p]
    · simp only [recordAt,hp,dite_false]
  · funext p
    by_cases hp : S.IsFixed w p
    · have he : ((recordAt w hh 𝔏 a).2 p = true) ↔ ((recordAt w hh 𝔏 b).2 p = true) := by
        rw [← recordTokens_fixed_tag w hh 𝔏 a p hp,
          ← recordTokens_fixed_tag w hh 𝔏 b p hp,ht p]
      exact Bool.eq_iff_iff.mpr he
    · simp only [recordAt,hp,dite_false]

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
