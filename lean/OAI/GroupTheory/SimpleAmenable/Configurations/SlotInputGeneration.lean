import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.LatticeTranslationTransport
import OAI.GroupTheory.SimpleAmenable.CentralCovers.GenerationUpstairs

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SlotInputGeneration

noncomputable def orderedTrackEquiv {m : ℕ} (ι : Fin 5 ↪ Fin m) :
    Fin 5 ≃ orderedTrackAlphabet ι :=
  Equiv.ofBijective (fun j => ⟨ι j,orderedTrackAlphabet_mem ι j⟩)
    ⟨fun j k he => ι.injective (congrArg Subtype.val he),by
      intro x
      obtain ⟨j,_,hj⟩ := Finset.mem_map.mp x.property
      exact ⟨j,Subtype.ext hj⟩⟩

theorem orderedTrackHom_bijective {m : ℕ} (ι : Fin 5 ↪ Fin m) :
    Function.Bijective (orderedTrackHom ι) := by
  have hi : Function.Injective (orderedTrackHom ι) := by
    intro s t he
    apply Subtype.ext
    apply Equiv.Perm.viaEmbeddingHom_injective ι
    have hh := congrArg (subtypeAlternatingHom (orderedTrackAlphabet ι)) he
    rw [← MonoidHom.comp_apply,← MonoidHom.comp_apply,orderedTrackHom_comp] at hh
    exact congrArg Subtype.val hh
  let e := (orderedTrackEquiv ι).altCongrHom
  have hs := Finite.surjective_of_injective (e.symm.injective.comp hi)
  refine ⟨hi,fun y => ?_⟩
  obtain ⟨x,hx⟩ := hs (e.symm y)
  exact ⟨x,e.symm.injective hx⟩

theorem smallPermutation_fiveRepresentation {m : ℕ} (hm : 5 ≤ m)
    (s : alternatingGroup (Fin m)) (hs : s.val.support.card≤5) :
    ∃ (ι : Fin 5 ↪ Fin m) (t : alternatingGroup (Fin 5)), fiveAlternatingHom ι t=s := by
  classical
  obtain ⟨I,hSI,_,hI⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ s.val.support) hs (by simpa using hm : 5≤(Finset.univ : Finset (Fin m)).card)
  let e : Fin 5 ≃ I := (Fintype.equivFinOfCardEq (by simpa using hI : Fintype.card I=5)).symm
  let ι : Fin 5 ↪ Fin m := e.toEmbedding.trans (Function.Embedding.subtype _)
  have hsub : s.val.support ⊆ orderedTrackAlphabet ι := by
    intro x hx
    exact Finset.mem_map.mpr ⟨e.symm ⟨x,hSI hx⟩,Finset.mem_univ _,
      congrArg Subtype.val (e.apply_symm_apply _)⟩
  obtain ⟨v,hv⟩ := (subtypeAlternatingHom_mem_range (orderedTrackAlphabet ι) s).mpr hsub
  obtain ⟨t,ht⟩ := (orderedTrackHom_bijective ι).2 v
  refine ⟨ι,t,?_⟩
  rw [← DFunLike.congr_fun (orderedTrackHom_comp ι) t,MonoidHom.comp_apply,ht,hv]

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem polygonStar_initial_alphabet (j : Fin 5) (I : FiveAlphabet (Fin (m+1))) :
    (B.polygonStar hlarge h hr (initialTest a r j)).comp
      (universalMap (subtypeAlternatingHom I.val)) =
    (B.initialAlphabet I.val j).comp (universalProjection (alternatingGroup I.val)) := by
  let P : Unit → Fin 5 × (CutRing × CutRing) := fun _ => (j,0)
  have hp : primitiveTests (a := a) (r := r) P ()=initialTest a r j := by
    simp only [primitiveTests,primitiveFamilyTests,P,spatialTranslate_zero]
  rw [← hp,B.polygonStar_eq hlarge h hr P _ (resolved_test _ ())]
  rw [B.fullGeometricSector_small_input hlarge P (fun J _ b hb => h Unit P J b hb) P () () rfl I]
  change (B.primitiveCopy I.val _ _ (j,0)).comp _ = _
  rw [B.primitiveCopy_zero]

variable (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (hwide : 100 ≤ m+1)

noncomputable def slotGroup : Subgroup (BoundedRelationCover M (alternatingGenerator a r m hm)) :=
  Subgroup.closure {z | ∃ (V : polygonAlgebra a) (i : Fin 5 → Fin (m+1))
    (u : Fin 5 → CutRing × CutRing)
    (hi : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j))))
    (s : UniversalExtension (alternatingGroup (Fin 5))), z=B.slotStar hlarge h hr hwide V i u hi s}

theorem slotGroup_mem (V : polygonAlgebra a) (i : Fin 5 → Fin (m+1))
    (u : Fin 5 → CutRing × CutRing)
    (hi : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j))))
    (s : UniversalExtension (alternatingGroup (Fin 5))) :
    B.slotStar hlarge h hr hwide V i u hi s ∈ B.slotGroup hlarge h hr hwide :=
  Subgroup.subset_closure ⟨V,i,u,hi,s,rfl⟩

include R hR

theorem translated_initial_mem_slotGroup (b : SmallConditional m)
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) :
    B.t k*PresentedGroup.of (Sum.inl b)*(B.t k)⁻¹ ∈ B.slotGroup hlarge h hr hwide := by
  obtain ⟨ι,s,hs⟩ := smallPermutation_fiveRepresentation (by omega : 5 ≤ m+1)
    (⟨b.2.val,b.2.property.1⟩ : alternatingGroup (Fin (m+1))) b.2.property.2
  obtain ⟨t,ht⟩ := universalProjection_surjective (alternatingGroup (Fin 5)) s
  let I : FiveAlphabet (Fin (m+1)) := ⟨orderedTrackAlphabet ι,Finset.subset_univ _,by
    simp [orderedTrackAlphabet]⟩
  let d := sourceLatticeOffsets m (Multiplicative.toAdd k)
  let F : OffsetFrame a r m hm (orderedTrackAlphabet ι) d := {
    k := k
    d := d
    projection := sourceLatticeFullMap_offsets a r m hm (Multiplicative.toAdd k)
    prescribed := fun _ _ => rfl }
  have he : B.distinctSlotStar hlarge h hr ι d F (initialTest a r b.1) t =
      B.t k*PresentedGroup.of (Sum.inl b)*(B.t k)⁻¹ := by
    change B.t k * B.polygonStar hlarge h hr (initialTest a r b.1)
      (universalMap (subtypeAlternatingHom I.val) (universalMap (orderedTrackHom ι) t)) * (B.t k)⁻¹ = _
    rw [show B.polygonStar hlarge h hr (initialTest a r b.1)
      (universalMap (subtypeAlternatingHom I.val) (universalMap (orderedTrackHom ι) t)) =
      B.initialAlphabet I.val b.1 (universalProjection _ (universalMap (orderedTrackHom ι) t)) from
        DFunLike.congr_fun (B.polygonStar_initial_alphabet hlarge h hr b.1 I) _]
    rw [show universalProjection _ (universalMap (orderedTrackHom ι) t)=orderedTrackHom ι s from
      (DFunLike.congr_fun (universalMap_spec (orderedTrackHom ι)) t).trans (by rw [MonoidHom.comp_apply,ht])]
    change B.t k*B.initialConditional b.1 (subtypeAlternatingHom (orderedTrackAlphabet ι) (orderedTrackHom ι s))*(B.t k)⁻¹=_
    have hh := DFunLike.congr_fun (orderedTrackHom_comp ι) s
    change subtypeAlternatingHom (orderedTrackAlphabet ι) (orderedTrackHom ι s) = fiveAlternatingHom ι s at hh
    rw [hh,hs,B.initialConditional_input _ _ b.2.property.2]
    rfl
  rw [← he,← DFunLike.congr_fun (B.slotStar_distinct hlarge h hr R hR hwide
    (initialTest a r b.1) ι d F (slots_injective_of_tracks _ _ ι.injective)) t]
  exact B.slotGroup_mem hlarge h hr hwide _ _ _ _ t

theorem slotGroup_eq_top : B.slotGroup hlarge h hr hwide=⊤ := by
  apply top_unique
  rw [← B.sourceAlignedGroup_univ_eq_top]
  change alignedGroup B.t (fun b : SmallConditional m => PresentedGroup.of (Sum.inl b))
    (fun b => b.2.val.support ⊆ Finset.univ) ≤ _
  apply (Subgroup.closure_le _).mpr
  rintro z ⟨b,_,k,rfl⟩
  exact B.translated_initial_mem_slotGroup hlarge h hr R hR hwide b k

end InitialCoverSystem
end SlotInputGeneration

end SimpleAmenable
end
end

end OAI
