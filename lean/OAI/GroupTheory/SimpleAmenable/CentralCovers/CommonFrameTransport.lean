import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FrameCentrality
import OAI.GroupTheory.SimpleAmenable.Configurations.DistinctSlotStars

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

noncomputable def geometricFrameGroup
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) :
    Subgroup (BoundedRelationCover M (alternatingGenerator a r m hm)) :=
  (⨆ V : polygonAlgebra a, (B.polygonStar hlarge h hr V).range).map (MulAut.conj (B.t k)).toMonoidHom

theorem geometricFrameGroup_central
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) :
    CentralOn (coverMap M (alternatingGenerator a r m hm)) (B.geometricFrameGroup hlarge h hr k) :=
  (B.polygonStars_central hlarge h hr).conjugate (B.t k)

theorem frameStar_mem_geometricFrameGroup (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)] (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm I u) (V : polygonAlgebra a)
    (s : UniversalExtension (alternatingGroup I)) :
    B.frameStar hlarge h hr I u F V s ∈ B.geometricFrameGroup hlarge h hr F.k := by
  refine ⟨_,?_,rfl⟩
  exact (le_iSup (fun W : polygonAlgebra a => (B.polygonStar hlarge h hr W).range) V)
    ⟨universalMap (subtypeAlternatingHom I) s,rfl⟩

theorem distinctSlotStar_mem_geometricFrameGroup (ι : Fin 5 ↪ Fin (m+1))
    (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u) (V : polygonAlgebra a)
    (s : UniversalExtension (alternatingGroup (Fin 5))) :
    B.distinctSlotStar hlarge h hr ι u F V s ∈ B.geometricFrameGroup hlarge h hr F.k :=
  B.frameStar_mem_geometricFrameGroup hlarge h hr _ u F V (universalMap (orderedTrackHom ι) s)

theorem distinctSlotStar_common_frame_transport (ι κ : Fin 5 ↪ Fin (m+1))
    (u v : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u)
    (G : OffsetFrame a r m hm (orderedTrackAlphabet κ) v) (hFG : F.k=G.k)
    (V : polygonAlgebra a) (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ B.geometricFrameGroup hlarge h hr F.k)
    (htransport : ∀ (j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (ι j,translate a (u (ι j)) x.val) =
        (κ j,translate a (v (κ j)) x.val)) :
    (MulAut.conj z).toMonoidHom.comp (B.distinctSlotStar hlarge h hr ι u F V) =
      B.distinctSlotStar hlarge h hr κ v G V := by
  let S := B.geometricFrameGroup hlarge h hr F.k
  apply CentralOn.lift_unique (coverMap M (alternatingGenerator a r m hm)) S
    (B.geometricFrameGroup_central hlarge h hr F.k)
  · rintro y ⟨s,rfl⟩
    exact S.mul_mem (S.mul_mem hz (B.distinctSlotStar_mem_geometricFrameGroup hlarge h hr ι u F V s))
      (S.inv_mem hz)
  · rintro y ⟨s,rfl⟩
    have he := B.distinctSlotStar_mem_geometricFrameGroup hlarge h hr κ v G V s
    rwa [← hFG] at he
  · ext s : 1
    change coverMap M (alternatingGenerator a r m hm)
      (z*B.distinctSlotStar hlarge h hr ι u F V s*z⁻¹) =
      coverMap M (alternatingGenerator a r m hm) (B.distinctSlotStar hlarge h hr κ v G V s)
    rw [map_mul,map_mul,map_inv]
    rw [show coverMap M (alternatingGenerator a r m hm) (B.distinctSlotStar hlarge h hr ι u F V s) = _ from
      DFunLike.congr_fun (B.distinctSlotStar_projection hlarge h hr ι u F V) s]
    rw [show coverMap M (alternatingGenerator a r m hm) (B.distinctSlotStar hlarge h hr κ v G V s) = _ from
      DFunLike.congr_fun (B.distinctSlotStar_projection hlarge h hr κ v G V) s]
    apply Subtype.ext
    exact slotHom_conjugate V (fun j => (ι j,u (ι j))) (fun j => (κ j,v (κ j)))
      (slots_injective_of_tracks V _ ι.injective) (slots_injective_of_tracks V _ κ.injective)
      (coverMap M (alternatingGenerator a r m hm) z).val htransport (universalProjection _ s).val

theorem distinctSlotStar_common_frame_fixer (ι : Fin 5 ↪ Fin (m+1))
    (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u) (V : polygonAlgebra a)
    (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ B.geometricFrameGroup hlarge h hr F.k)
    (hfix : ∀ (j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (ι j,translate a (u (ι j)) x.val) =
        (ι j,translate a (u (ι j)) x.val))
    (s : UniversalExtension (alternatingGroup (Fin 5))) :
    Commute z (B.distinctSlotStar hlarge h hr ι u F V s) := by
  have he := DFunLike.congr_fun
    (B.distinctSlotStar_common_frame_transport hlarge h hr ι ι u u F F rfl V z hz hfix) s
  change z*B.distinctSlotStar hlarge h hr ι u F V s*z⁻¹ = B.distinctSlotStar hlarge h hr ι u F V s at he
  have he' := congrArg (fun x => x*z) he
  exact show _*_ = _*_ from by simpa only [mul_assoc,inv_mul_cancel,mul_one] using he'

theorem frameStar_uniform (I : Finset (Fin (m+1))) (hI : 5 ≤ I.card)
    [Group.IsPerfect (alternatingGroup I)] (b : Fin (m+1)) (hb : b ∉ I)
    (u : Fin (m+1) → CutRing × CutRing) (F : OffsetFrame a r m hm I u)
    (v : CutRing × CutRing) (hu : ∀ i ∈ I, u i=v) (V : polygonAlgebra a) :
    B.frameStar hlarge h hr I u F V =
      (B.polygonStar hlarge h hr (spatialTranslate v V)).comp (universalMap (subtypeAlternatingHom I)) := by
  let C : CommonFrame a r m hm I v := {
    k := F.k
    d := F.d
    projection := F.projection
    common := fun i hi => (F.prescribed i hi).trans (hu i hi) }
  exact B.polygonStar_common_translate hlarge h hr I hI b hb v C V

theorem distinctSlotStar_uniform_mem (ι : Fin 5 ↪ Fin (m+1)) (b : Fin (m+1))
    (hb : b ∉ orderedTrackAlphabet ι) (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u)
    (v : CutRing × CutRing) (hu : ∀ j, u (ι j)=v) (V : polygonAlgebra a)
    (s : UniversalExtension (alternatingGroup (Fin 5))) :
    B.distinctSlotStar hlarge h hr ι u F V s ∈
      ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range := by
  have hc : 5 ≤ (orderedTrackAlphabet ι).card := by
    rw [orderedTrackAlphabet,Finset.card_map,Finset.card_univ,Fintype.card_fin]
  have huv : ∀ i ∈ orderedTrackAlphabet ι, u i=v := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hi
    exact hu j
  change B.frameStar hlarge h hr (orderedTrackAlphabet ι) u F V (universalMap (orderedTrackHom ι) s) ∈ _
  rw [B.frameStar_uniform hlarge h hr _ hc b hb u F v huv V]
  exact (le_iSup (fun W : polygonAlgebra a => (B.polygonStar hlarge h hr W).range) (spatialTranslate v V)) ⟨_,rfl⟩

theorem distinctSlotStar_uniform_fixer (ι : Fin 5 ↪ Fin (m+1)) (b : Fin (m+1))
    (hb : b ∉ orderedTrackAlphabet ι) (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u)
    (v : CutRing × CutRing) (hu : ∀ j, u (ι j)=v) (V : polygonAlgebra a)
    (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range)
    (hfix : ∀ (j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (ι j,translate a (u (ι j)) x.val) =
        (ι j,translate a (u (ι j)) x.val))
    (s : UniversalExtension (alternatingGroup (Fin 5))) :
    Commute z (B.distinctSlotStar hlarge h hr ι u F V s) := by
  apply CentralOn.commute_perfect _ _ (B.polygonStars_central hlarge h hr)
    (B.distinctSlotStar hlarge h hr ι u F V) _ z hz _ s
  · rintro y ⟨s,rfl⟩
    exact B.distinctSlotStar_uniform_mem hlarge h hr ι b hb u F v hu V s
  · intro t
    have hg := B.frameStar_supported hlarge h hr (orderedTrackAlphabet ι) u F V
      (universalMap (orderedTrackHom ι) t)
    have hf : ∀ p ∈ frameDomain (orderedTrackAlphabet ι) u V,
        (coverMap M (alternatingGenerator a r m hm) z).val.val p=p := by
      rintro p ⟨i,hi,x,hx,rfl⟩
      obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hi
      exact hfix j ⟨x,hx⟩
    exact show _*_ = _*_ from Subtype.ext (Subtype.ext (supported_fixer_commute hf hg).eq)

theorem frameStar_alphabet_mem (I : Finset (Fin (m+1))) (hI : 5 ≤ I.card)
    [Group.IsPerfect (alternatingGroup I)] (b : Fin (m+1)) (hb : b ∉ I)
    (u : Fin (m+1) → CutRing × CutRing) (F : OffsetFrame a r m hm I u)
    (V : polygonAlgebra a) (s : UniversalExtension (alternatingGroup I)) :
    B.frameStar hlarge h hr I u F V s ∈ sourceAlignedGroup a r m hm M B.t I :=
  alignedGroup_conjugate B.t _ _ F.k (B.polygonStar_alphabet_aligned hlarge h hr I hI b hb V s)

end InitialCoverSystem

end SimpleAmenable

end OAI
