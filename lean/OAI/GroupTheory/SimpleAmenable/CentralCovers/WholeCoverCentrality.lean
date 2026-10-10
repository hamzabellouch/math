import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FiniteSlotRefinement
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveCentralLaws
import OAI.GroupTheory.SimpleAmenable.RandomFields.RecoveredConstantCovariance
import OAI.GroupTheory.SimpleAmenable.Configurations.SlotInputGeneration

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section WholeCoverCentrality
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem initial_input_mem_polygonStars (b : SmallConditional m) :
    PresentedGroup.of (Sum.inl b) ∈
      ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range := by
  obtain ⟨ι,s,hs⟩ := smallPermutation_fiveRepresentation (by omega : 5 ≤ m+1)
    (⟨b.2.val,b.2.property.1⟩ : alternatingGroup (Fin (m+1))) b.2.property.2
  obtain ⟨t,ht⟩ := universalProjection_surjective (alternatingGroup (Fin 5)) s
  let I : FiveAlphabet (Fin (m+1)) := ⟨orderedTrackAlphabet ι,Finset.subset_univ _,by
    simp [orderedTrackAlphabet]⟩
  apply le_iSup (fun W : polygonAlgebra a => (B.polygonStar hlarge h hr W).range)
    (initialTest a r b.1)
  refine ⟨universalMap (subtypeAlternatingHom I.val) (universalMap (orderedTrackHom ι) t),?_⟩
  rw [show B.polygonStar hlarge h hr (initialTest a r b.1)
    (universalMap (subtypeAlternatingHom I.val) (universalMap (orderedTrackHom ι) t)) =
    B.initialAlphabet I.val b.1 (universalProjection _ (universalMap (orderedTrackHom ι) t)) from
      DFunLike.congr_fun (B.polygonStar_initial_alphabet hlarge h hr b.1 I) _]
  rw [show universalProjection _ (universalMap (orderedTrackHom ι) t)=orderedTrackHom ι s from
    (DFunLike.congr_fun (universalMap_spec (orderedTrackHom ι)) t).trans (by rw [MonoidHom.comp_apply,ht])]
  change B.initialConditional b.1 (subtypeAlternatingHom (orderedTrackAlphabet ι) (orderedTrackHom ι s))=_
  have hh := DFunLike.congr_fun (orderedTrackHom_comp ι) s
  change subtypeAlternatingHom (orderedTrackAlphabet ι) (orderedTrackHom ι s) = fiveAlternatingHom ι s at hh
  rw [hh,hs,B.initialConditional_input _ _ b.2.property.2]
  rfl

variable (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (hwide : 100 ≤ m+1)
include R hR

theorem uniformSlotTransport_initial (b : SmallConditional m) :
    B.UniformSlotTransport hlarge h hr hwide (PresentedGroup.of (Sum.inl b)) := by
  intro V i k u v htr hi hk
  have hspatial : ∀ (j : Fin 5) (x : V.val), translate a (u j) x.val=translate a (v j) x.val := by
    intro j x
    have he := congrArg Prod.snd (htr j x)
    have hp := coverMap_of M (alternatingGenerator a r m hm) (Sum.inl b)
    have hh := congrArg (fun g : polygonAlternatingGroup a (m+1) =>
      (g.val.val (i j,translate a (u j) x.val)).2) hp
    exact hh.symm.trans he
  have heq : SlotMap a (m+1) V (fun j => (k j,u j))=
      SlotMap a (m+1) V (fun j => (k j,v j)) := by
    funext p
    exact congrArg (fun z => (k p.1,z)) (hspatial p.1 p.2)
  have hk' : Function.Injective (SlotMap a (m+1) V (fun j => (k j,u j))) := by
    rw [heq]; exact hk
  have htr' : ∀ (j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) (PresentedGroup.of (Sum.inl b))).val.val
        (i j,translate a (u j) x.val)=(k j,translate a (u j) x.val) := by
    intro j x
    exact (htr j x).trans (congrArg (fun z => (k j,z)) (hspatial j x).symm)
  have ht := B.slotStar_aligned_transport hlarge h hr R hR hwide V i k u hi hk'
    b.2.val.support b.2.property.2 (PresentedGroup.of (Sum.inl b))
    (B.initial_input_mem_polygonStars hlarge h hr b)
    (alignedGroup_input B.t _ _ b (Finset.Subset.refl _)) htr'
  exact ht.trans (B.slotStar_parameterwise hlarge h hr R hR hwide V k k u v hk' hk
    (fun j x => congrArg (fun z => (k j,z)) (hspatial j x)))

theorem uniformSlotTransport_lattice
    (k₀ : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) :
    B.UniformSlotTransport hlarge h hr hwide (B.t k₀) := by
  intro V i k u v htr hi hk
  let d := sourceLatticeOffsets m (Multiplicative.toAdd k₀)
  let u' := fun j => d (i j)+u j
  have hi' := SlotMap_shift_injective V i u hi d
  have ht := B.slotStar_translation_lattice hlarge h hr R hR hwide
    (Multiplicative.toAdd k₀) V i u hi
  apply ht.trans
  apply B.slotStar_parameterwise hlarge h hr R hR hwide V i k u' v hi' hk
  intro j x
  have he := htr j x
  rw [show coverMap M (alternatingGenerator a r m hm) (B.t k₀)=sourceLatticeMap a r m hm k₀ from
    DFunLike.congr_fun B.t_projection k₀] at he
  change (sourceLatticeFullMap a r m hm k₀).val (i j,translate a (u j) x.val)=_ at he
  have hp := congrArg (fun g : polygonFullGroup a (m+1) =>
    g.val (i j,translate a (u j) x.val))
      (sourceLatticeFullMap_offsets a r m hm (Multiplicative.toAdd k₀))
  have hh := hp.symm.trans he
  change (i j,translate a (d (i j)) (translate a (u j) x.val))=_ at hh
  simpa only [u',translate_add] using hh

theorem uniformSlotTransport_all
    (z : BoundedRelationCover M (alternatingGenerator a r m hm)) :
    B.UniformSlotTransport hlarge h hr hwide z := by
  change z ∈ B.slotTransportSubgroup hlarge h hr hwide R hR
  apply PresentedGroup.generated_by _ (B.slotTransportSubgroup hlarge h hr hwide R hR) _ z
  intro j
  cases j with
  | inl b => exact B.uniformSlotTransport_initial hlarge h hr R hR hwide b
  | inr k =>
    have he := B.uniformSlotTransport_lattice hlarge h hr R hR hwide
      (Multiplicative.ofAdd (FreeAbelianGroup.of k))
    rw [B.t_base] at he
    exact he

include hlarge h hr hwide

theorem coverMap_kernel_central :
    (coverMap M (alternatingGenerator a r m hm)).ker ≤
      Subgroup.center (BoundedRelationCover M (alternatingGenerator a r m hm)) := by
  intro w hw
  have hw' : coverMap M (alternatingGenerator a r m hm) w=1 := hw
  have hc : ∀ z∈ B.slotGroup hlarge h hr hwide, Commute w z := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨V,i,u,hi,s,rfl⟩ := hz
      have he := B.uniformSlotTransport_all hlarge h hr R hR hwide w V i i u u
        (by intro j x; rw [hw']; rfl) hi hi
      have hh := DFunLike.congr_fun he s
      change w*B.slotStar hlarge h hr hwide V i u hi s*w⁻¹=
        B.slotStar hlarge h hr hwide V i u hi s at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    | one => exact Commute.one_right w
    | mul x y _ _ hx hy => exact hx.mul_right hy
    | inv x _ hx => exact hx.inv_right
  rw [Subgroup.mem_center_iff]
  intro z
  have hh : z∈B.slotGroup hlarge h hr hwide := by
    rw [B.slotGroup_eq_top hlarge h hr R hR hwide]
    trivial
  exact (hc z hh).eq.symm

end InitialCoverSystem
end WholeCoverCentrality

section SourceCentralCover

theorem source_cover_centrality {a m : ℕ} {r : CutRing} (hm : 2 ≤ m)
    (ha : 0<a) (hwide : 100 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hSlope : 8000<ordinary (cutTau^a)) (hconj : |conjugate (cutTau^a)|<1/1000) :
    SourceCoverCentrality a r m hm := by
  let : Group.IsPerfect (alternatingGroup (Fin (m+1))) :=
    ⟨commutator_alternatingGroup_eq_top (by simpa using (by omega : 5 ≤ m+1))⟩
  obtain ⟨L₁,hL₁⟩ := initialCoverSystem_eventually a r m hm hr (by omega)
  obtain ⟨L₂,hL₂⟩ := primitive_laws_eventually (hm := hm) ha (by omega) hr hSlope hconj
  obtain ⟨L₃,hL₃⟩ := initial_constant_covariance_eventually a r m hm hr (by omega)
  let M := L₁+L₂+L₃
  obtain ⟨B⟩ := hL₁ M (by omega)
  have h : B.AllPrimitiveLaws := hL₂ M (by omega) B
  obtain ⟨R,hR⟩ := hL₃ M (by omega) B
  exact ⟨M,B.coverMap_kernel_central (by omega) h hr R hR hwide⟩

theorem polygon_central_cover {a m : ℕ} {r : CutRing} (hm : 2 ≤ m)
    (ha : 0<a) (hwide : 100 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hSlope : 8000<ordinary (cutTau^a)) (hconj : |conjugate (cutTau^a)|<1/1000) :
    ∃ L : ℕ, Group.IsFinitelyPresented (BoundedRelationCover L (alternatingGenerator a r m hm)) ∧
      Function.Surjective (coverMap L (alternatingGenerator a r m hm)) ∧
      (coverMap L (alternatingGenerator a r m hm)).ker ≤
        Subgroup.center (BoundedRelationCover L (alternatingGenerator a r m hm)) := by
  obtain ⟨L,hL⟩ := source_cover_centrality hm ha hwide hr hSlope hconj
  exact ⟨L,inferInstance,sourceCover_surjective a r m L hr (by omega) hm,hL⟩

end SourceCentralCover

end SimpleAmenable
end
end

end OAI
