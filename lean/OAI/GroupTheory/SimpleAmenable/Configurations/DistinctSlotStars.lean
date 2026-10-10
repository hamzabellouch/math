import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FrameDisjointness

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section DistinctSlotStars

noncomputable def fiveAlternatingHom {m : ℕ} (ι : Fin 5 ↪ Fin m) :
    alternatingGroup (Fin 5) →* alternatingGroup (Fin m) :=
  (fiveTrackHom ι).codRestrict _ (fiveTrack_sign ι)

noncomputable def orderedTrackAlphabet {m : ℕ} (ι : Fin 5 ↪ Fin m) : Finset (Fin m) :=
  Finset.univ.map ι

instance orderedTrackAlphabetPerfect {m : ℕ} (ι : Fin 5 ↪ Fin m) :
    Group.IsPerfect (alternatingGroup (orderedTrackAlphabet ι)) := by
  classical
  apply Group.IsPerfect.mk
  apply commutator_alternatingGroup_eq_top
  rw [Nat.card_eq_fintype_card,Fintype.card_coe,orderedTrackAlphabet,Finset.card_map,Finset.card_univ,Fintype.card_fin]

noncomputable def orderedTrackHom {m : ℕ} (ι : Fin 5 ↪ Fin m) :
    alternatingGroup (Fin 5) →* alternatingGroup (orderedTrackAlphabet ι) :=
  (MonoidHom.ofInjective (subtypeAlternatingHom_injective (orderedTrackAlphabet ι))).symm.toMonoidHom.comp
    ((fiveAlternatingHom ι).codRestrict (subtypeAlternatingHom (orderedTrackAlphabet ι)).range
      (fun s => (subtypeAlternatingHom_mem_range _ _).mpr (alphabet_support_subset ι s)))

@[simp] theorem orderedTrackHom_comp {m : ℕ} (ι : Fin 5 ↪ Fin m) :
    (subtypeAlternatingHom (orderedTrackAlphabet ι)).comp (orderedTrackHom ι) =
      fiveAlternatingHom ι := by
  ext s : 1
  exact MonoidHom.apply_ofInjective_symm (subtypeAlternatingHom_injective _) _

@[simp] theorem orderedTrackAlphabet_mem {m : ℕ} (ι : Fin 5 ↪ Fin m) (j : Fin 5) :
    ι j ∈ orderedTrackAlphabet ι := Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩

theorem orderedTrackHom_apply {m : ℕ} (ι : Fin 5 ↪ Fin m)
    (s : alternatingGroup (Fin 5)) (j : Fin 5) :
    ((orderedTrackHom ι s).val ⟨ι j,orderedTrackAlphabet_mem ι j⟩).val = ι (s.val j) := by
  have he := congrArg (fun t : alternatingGroup (Fin m) => t.val (ι j))
    (DFunLike.congr_fun (orderedTrackHom_comp ι) s)
  change Equiv.Perm.ofSubtype (orderedTrackHom ι s).val (ι j) =
    Equiv.Perm.viaEmbedding s.val ι (ι j) at he
  rw [Equiv.Perm.ofSubtype_apply_of_mem _ (orderedTrackAlphabet_mem ι j),
    Equiv.Perm.viaEmbedding_apply] at he
  exact he

noncomputable def slotAlternatingHom {a m : ℕ} (V : polygonAlgebra a)
    (slots : Fin 5 → Fin m × (CutRing × CutRing))
    (hinj : Function.Injective (SlotMap a m V slots)) :
    alternatingGroup (Fin 5) →* polygonAlternatingGroup a m :=
  ((slotHom V slots hinj).comp (alternatingGroup (Fin 5)).subtype).codRestrict _
    (fun s => slotHom_alternating_mem V slots hinj s.property)

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

noncomputable def distinctSlotStar (ι : Fin 5 ↪ Fin (m+1))
    (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u) (V : polygonAlgebra a) :
    UniversalExtension (alternatingGroup (Fin 5)) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  (B.frameStar hlarge h hr (orderedTrackAlphabet ι) u F V).comp (universalMap (orderedTrackHom ι))

theorem distinctSlotStar_apply (ι : Fin 5 ↪ Fin (m+1))
    (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u) (V : polygonAlgebra a)
    (s : UniversalExtension (alternatingGroup (Fin 5))) (j : Fin 5) (x : V.val) :
    (coverMap M (alternatingGenerator a r m hm) (B.distinctSlotStar hlarge h hr ι u F V s)).val.val
      (ι j,translate a (u (ι j)) x.val) =
      (ι ((universalProjection _ s).val j),translate a (u (ι ((universalProjection _ s).val j))) x.val) := by
  have he := B.frameStar_apply hlarge h hr (orderedTrackAlphabet ι) u F V
    (universalMap (orderedTrackHom ι) s) ⟨ι j,orderedTrackAlphabet_mem ι j⟩ x
  rw [show universalProjection _ (universalMap (orderedTrackHom ι) s) =
    orderedTrackHom ι (universalProjection _ s) from
    DFunLike.congr_fun (universalMap_spec (orderedTrackHom ι)) s,orderedTrackHom_apply] at he
  exact he

theorem distinctSlotStar_projection (ι : Fin 5 ↪ Fin (m+1))
    (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u) (V : polygonAlgebra a) :
    (coverMap M (alternatingGenerator a r m hm)).comp (B.distinctSlotStar hlarge h hr ι u F V) =
      (slotAlternatingHom V (fun j => (ι j,u (ι j)))
        (slots_injective_of_tracks V _ ι.injective)).comp (universalProjection (alternatingGroup (Fin 5))) := by
  ext s : 1
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro p
  by_cases hp : p ∈ Set.range (SlotMap a (m+1) V (fun j => (ι j,u (ι j))))
  · obtain ⟨⟨j,x⟩,rfl⟩ := hp
    change (coverMap M (alternatingGenerator a r m hm) (B.distinctSlotStar hlarge h hr ι u F V s)).val.val
      (ι j,translate a (u (ι j)) x.val) =
      slotPerm V (fun j => (ι j,u (ι j))) _ (universalProjection _ s).val
        (SlotMap a (m+1) V (fun j => (ι j,u (ι j))) (j,x))
    rw [slotPerm_apply]
    exact B.distinctSlotStar_apply hlarge h hr ι u F V s j x
  · have hp' : p ∉ frameDomain (orderedTrackAlphabet ι) u V := by
      rintro ⟨i,hi,x,hx,rfl⟩
      obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
      exact hp ⟨(j,⟨x,hx⟩),rfl⟩
    have he := B.frameStar_supported hlarge h hr (orderedTrackAlphabet ι) u F V
      (universalMap (orderedTrackHom ι) s) p hp'
    change (coverMap M (alternatingGenerator a r m hm) (B.distinctSlotStar hlarge h hr ι u F V s)).val.val p =
      slotPerm V (fun j => (ι j,u (ι j))) _ (universalProjection _ s).val p
    rw [slotPerm_apply_of_notMem _ _ _ _ hp]
    exact he

end InitialCoverSystem
end DistinctSlotStars

end SimpleAmenable
end
end

end OAI
