import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ConnectedLitComponent

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

lemma record_untagged_singleton (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (R : AssignedRecord S ℓ) (p : S.Index)
    (t : LocalToken ℓ) (ht : t ∈ recordTokens w hh 𝔏 R p) (hu : t.1 = false) :
    recordTokens w hh 𝔏 R p = {t} := by
  by_cases ho : (treeOccurrences w p).Nonempty
  · rw [recordTokens,ite_eq_left ho] at ht ⊢
    by_cases hf : S.IsFixed w p
    · rw [ite_eq_left hf] at ht ⊢
      by_cases htag : R.2 p = true
      · rw [ite_eq_left htag] at ht
        have h := taggedPieces_tagged w hh _ _ ht
        rw [hu] at h
        contradiction
      · rw [ite_eq_right htag] at ht ⊢
        rw [mem_singleton.mp ht]
    · rw [ite_eq_right hf] at ht ⊢
      obtain ⟨e,he⟩ := ho
      have heq := treeOccurrences_singleton_of_free w ⟨p,hf⟩ e he
      rw [heq,image_singleton] at ht ⊢
      rw [mem_singleton.mp ht]
  · rw [recordTokens,ite_eq_right ho] at ht
    exact False.elim (Finset.notMem_empty _ ht)

lemma record_untagged_not_in_list (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index)
    (t : LocalToken ℓ) (ht : t ∈ recordTokens w hh 𝔏 (recordAt w hh 𝔏 a) p)
    (hu : t.1 = false) : (p : ℕ) ∉ listSupport w 𝔏 := by
  by_cases ho : (treeOccurrences w p).Nonempty
  · rw [recordTokens,ite_eq_left ho] at ht
    by_cases hf : S.IsFixed w p
    · rw [ite_eq_left hf] at ht
      by_cases htag : (recordAt w hh 𝔏 a).2 p = true
      · rw [ite_eq_left htag] at ht
        have h := taggedPieces_tagged w hh _ _ ht
        rw [hu] at h
        contradiction
      · intro hp
        exact htag ((recordAt_tag w hh 𝔏 a ⟨p,hf⟩ ho).mpr (Or.inl hp))
    · rw [ite_eq_right hf] at ht
      obtain ⟨e,he,rfl⟩ := mem_image.mp ht
      intro hp
      have htag : singletonIsTagged w 𝔏 p e := Or.inl hp
      simp only [freePiece,htag,ite_true] at hu
      contradiction
  · rw [recordTokens,ite_eq_right ho] at ht
    exact False.elim (Finset.notMem_empty _ ht)

def HasUntagged (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (R : AssignedRecord S ℓ) (p : S.Index) : Prop :=
  ∃ t ∈ recordTokens w hh 𝔏 R p, t.1 = false

lemma hasUntagged_shape (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index)
    (hp : HasUntagged w hh 𝔏 (recordAt w hh 𝔏 a) p) :
    ∃ Q : Shape w,
      recordTokens w hh 𝔏 (recordAt w hh 𝔏 a) p = {(false,false,Q.edges.val)} := by
  obtain ⟨t,ht,hu⟩ := hp
  obtain ⟨hg,Q,hQ⟩ := record_untagged_shape w hh 𝔏 a p t ht hu
  have he : t = (false,false,Q.edges.val) := by
    apply Prod.ext hu
    exact Prod.ext hg hQ.symm
  exact ⟨Q,by rw [record_untagged_singleton w hh 𝔏 _ p t ht hu,he]⟩

def untaggedShape (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index)
    (hp : HasUntagged w hh 𝔏 (recordAt w hh 𝔏 a) p) : Shape w :=
  Classical.choose (hasUntagged_shape w hh 𝔏 a p hp)

lemma untaggedShape_spec (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index)
    (hp : HasUntagged w hh 𝔏 (recordAt w hh 𝔏 a) p) :
    recordTokens w hh 𝔏 (recordAt w hh 𝔏 a) p =
      {(false,false,(untaggedShape w hh 𝔏 a p hp).edges.val)} :=
  Classical.choose_spec (hasUntagged_shape w hh 𝔏 a p hp)

def untaggedType (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index) :
    Option (TokenType w) :=
  if hp : HasUntagged w hh 𝔏 (recordAt w hh 𝔏 a) p then
    some (decide (S.IsCore p),untaggedShape w hh 𝔏 a p hp) else none

lemma untaggedType_some (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index)
    (t : TokenType w) (ht : untaggedType w hh 𝔏 a p = some t) :
    (t.1 = true ↔ S.IsCore p) ∧
    recordTokens w hh 𝔏 (recordAt w hh 𝔏 a) p = {(false,false,t.2.edges.val)} := by
  unfold untaggedType at ht
  split_ifs at ht with hp
  · have he := Option.some.inj ht
    subst t
    exact ⟨by simp,untaggedShape_spec w hh 𝔏 a p hp⟩

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
