import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.TemplateRelators
import OAI.GroupTheory.SimpleAmenable.Configurations.DistinctSlotStars
import OAI.GroupTheory.SimpleAmenable.CentralCovers.DistinctSlotFixer
import OAI.GroupTheory.SimpleAmenable.RandomFields.RecoveredConstantCovariance

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SmallEvenRouting

theorem exists_small_even_reindex {m : ℕ} (hm : 12 ≤ m+1)
    (ι κ : Fin 5 ↪ Fin (m+1)) :
    ∃ J : Finset (Fin (m+1)), J.card = 12 ∧
      ∃ c : alternatingGroup (Fin (m+1)), c.val.support ⊆ J ∧
        ∀ j, c.val (ι j)=κ j := by
  classical
  have hc (e : Fin 5 ↪ Fin (m+1)) : (orderedTrackAlphabet e).card=5 := by
    simp [orderedTrackAlphabet]
  obtain ⟨J,hIJ,_,hJ⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (orderedTrackAlphabet ι ∪ orderedTrackAlphabet κ))
    (show (orderedTrackAlphabet ι ∪ orderedTrackAlphabet κ).card ≤ 12 from
      (Finset.card_union_le _ _).trans (by rw [hc,hc]; decide))
    (show 12 ≤ (Finset.univ : Finset (Fin (m+1))).card by simpa using hm)
  let i : Fin 5 ↪ J := ⟨fun j => ⟨ι j,hIJ (Finset.mem_union_left _ (orderedTrackAlphabet_mem ι j))⟩,
    fun x y he => ι.injective (congrArg Subtype.val he)⟩
  let k : Fin 5 ↪ J := ⟨fun j => ⟨κ j,hIJ (Finset.mem_union_right _ (orderedTrackAlphabet_mem κ j))⟩,
    fun x y he => κ.injective (congrArg Subtype.val he)⟩
  have hcard : Nat.card J = 12 := by rw [Nat.card_eq_fintype_card,Fintype.card_coe,hJ]
  have := alternatingGroup.isMultiplyPretransitive J
  have : MulAction.IsMultiplyPretransitive (alternatingGroup J) J 5 :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card J - 2)
      (by rw [hcard]; decide) (Nat.sub_le _ _)
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq (alternatingGroup J) i k
  refine ⟨J,hJ,subtypeAlternatingHom J c,
    (subtypeAlternatingHom_mem_range J _).mp ⟨c,rfl⟩,?_⟩
  intro j
  have he : c.val (i j)=k j := congrArg (fun e : Fin 5 ↪ J => e j) hc
  change Equiv.Perm.ofSubtype c.val (ι j)=κ j
  exact (Equiv.Perm.ofSubtype_apply_coe c.val (i j)).trans (congrArg Subtype.val he)

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem constant_mem_sourceAligned (c : alternatingGroup (Fin (m+1)))
    (J : Finset (Fin (m+1))) (hc : c.val.support ⊆ J) :
    B.c c ∈ sourceAlignedGroup a r m hm M B.t J := by
  obtain ⟨s,rfl⟩ := (subtypeAlternatingHom_mem_range J c).mpr hc
  have hh := B.initialAlphabet_aligned J 0 s
  rwa [B.initialAlphabet_zero] at hh

variable [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem distinctSlotStar_aligned_transport_with_reindex
    (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (ι κ : Fin 5 ↪ Fin (m+1)) (c : alternatingGroup (Fin (m+1)))
    (hc : ∀ j, c.val (ι j)=κ j) (C : Finset (Fin (m+1))) (hcC : c.val.support ⊆ C)
    (b : Fin (m+1)) (hb : b ∉ orderedTrackAlphabet ι) (hb' : b ∉ orderedTrackAlphabet κ)
    (u v : Fin (m+1) → CutRing × CutRing) (huv : ∀ j, u (ι j)=v (κ j))
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u)
    (G : OffsetFrame a r m hm (orderedTrackAlphabet κ) v) (V : polygonAlgebra a)
    (J : Finset (Fin (m+1)))
    (hreserve : 20 ≤ ((Finset.univ : Finset (Fin (m+1))) \ (insert b (J ∪ C) ∪ orderedTrackAlphabet ι)).card)
    (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range)
    (hzJ : z ∈ sourceAlignedGroup a r m hm M B.t J)
    (htransport : ∀ (j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (ι j,translate a (u (ι j)) x.val) =
        (κ j,translate a (v (κ j)) x.val)) :
    (MulAut.conj z).toMonoidHom.comp (B.distinctSlotStar hlarge h hr ι u F V) =
      B.distinctSlotStar hlarge h hr κ v G V := by
  let S := ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range
  have hcS : B.c c ∈ S := B.constant_mem_polygonStars hlarge h hr c
  have hczS : (B.c c)⁻¹*z ∈ S := S.mul_mem (S.inv_mem hcS) hz
  let K := sourceAlignedGroup a r m hm M B.t (J∪C)
  have hcK : B.c c ∈ K := sourceAlignedGroup_mono B.t Finset.subset_union_right
    (B.constant_mem_sourceAligned c C hcC)
  have hzK : z ∈ K := sourceAlignedGroup_mono B.t Finset.subset_union_left hzJ
  have hfix : ∀ (j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) ((B.c c)⁻¹*z)).val.val
        (ι j,translate a (u (ι j)) x.val) = (ι j,translate a (u (ι j)) x.val) := by
    intro j x
    rw [map_mul,map_inv]
    change (coverMap M (alternatingGenerator a r m hm) (B.c c)).val.val.symm
      ((coverMap M (alternatingGenerator a r m hm) z).val.val _) = _
    rw [htransport j x,
      show coverMap M (alternatingGenerator a r m hm) (B.c c) =
        conditionalAlternatingHom (wholePolygon a) c from DFunLike.congr_fun B.c_projection c]
    change (conditionalPerm (wholePolygon a) c.val).symm
      (κ j,translate a (v (κ j)) x.val) = _
    have hci : c.val.symm (κ j)=ι j := by rw [← hc j]; exact c.val.symm_apply_apply _
    simp [conditionalPerm,wholePolygon,hci,← huv j]
  ext s : 1
  have hh := B.distinct_slot_fixer hlarge h hr ι b hb u F V (J∪C) hreserve
    ((B.c c)⁻¹*z) hczS (K.mul_mem (K.inv_mem hcK) hzK) hfix s
  have he := DFunLike.congr_fun (B.distinctSlotStar_constant_transport hlarge h hr
    R hR ι κ c hc b hb' u v huv F G V) s
  change z * B.distinctSlotStar hlarge h hr ι u F V s * z⁻¹ = _
  change B.c c * B.distinctSlotStar hlarge h hr ι u F V s * (B.c c)⁻¹ =
    B.distinctSlotStar hlarge h hr κ v G V s at he
  rw [← he]
  calc
    z * B.distinctSlotStar hlarge h hr ι u F V s * z⁻¹ =
      B.c c * (((B.c c)⁻¹*z)*B.distinctSlotStar hlarge h hr ι u F V s) * z⁻¹ := by group
    _ = B.c c * (B.distinctSlotStar hlarge h hr ι u F V s*((B.c c)⁻¹*z)) * z⁻¹ := by rw [hh.eq]
    _ = B.c c * B.distinctSlotStar hlarge h hr ι u F V s * (B.c c)⁻¹ := by group

theorem distinctSlotStar_aligned_transport
    (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (ι κ : Fin 5 ↪ Fin (m+1))
    (u v : Fin (m+1) → CutRing × CutRing) (huv : ∀ j, u (ι j)=v (κ j))
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u)
    (G : OffsetFrame a r m hm (orderedTrackAlphabet κ) v) (V : polygonAlgebra a)
    (J : Finset (Fin (m+1))) (hreserve : J.card+38 ≤ m+1)
    (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range)
    (hzJ : z ∈ sourceAlignedGroup a r m hm M B.t J)
    (htransport : ∀ (j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (ι j,translate a (u (ι j)) x.val) =
        (κ j,translate a (v (κ j)) x.val)) :
    (MulAut.conj z).toMonoidHom.comp (B.distinctSlotStar hlarge h hr ι u F V) =
      B.distinctSlotStar hlarge h hr κ v G V := by
  classical
  obtain ⟨C,hC,c,hcC,hc⟩ := exists_small_even_reindex (by omega : 12 ≤ m+1) ι κ
  have hcard (e : Fin 5 ↪ Fin (m+1)) : (orderedTrackAlphabet e).card=5 := by
    simp [orderedTrackAlphabet]
  have hab : (orderedTrackAlphabet ι ∪ orderedTrackAlphabet κ).card <
      (Finset.univ : Finset (Fin (m+1))).card := by
    have hh := Finset.card_union_le (orderedTrackAlphabet ι) (orderedTrackAlphabet κ)
    rw [hcard,hcard] at hh
    simp only [Finset.card_univ,Fintype.card_fin]
    omega
  obtain ⟨b,_,hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hab
  have hbι : b ∉ orderedTrackAlphabet ι := fun hh => hb (Finset.mem_union_left _ hh)
  have hbκ : b ∉ orderedTrackAlphabet κ := fun hh => hb (Finset.mem_union_right _ hh)
  apply B.distinctSlotStar_aligned_transport_with_reindex hlarge h hr R hR ι κ c hc C hcC
    b hbι hbκ u v huv F G V J _ z hz hzJ htransport
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin]
  have h₁ := Finset.card_union_le J C
  have h₂ := Finset.card_insert_le b (J∪C)
  have h₃ := Finset.card_union_le (insert b (J∪C)) (orderedTrackAlphabet ι)
  rw [hC] at h₁
  rw [hcard] at h₃
  omega

end InitialCoverSystem
end SmallEvenRouting

end SimpleAmenable
end
end

end OAI
