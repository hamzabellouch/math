import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.DistinctSlotStars
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CommonFrameTransport

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

theorem initial_constant_covariance_eventually (a : ℕ) (r : CutRing) (m : ℕ)
    (hm : 2 ≤ m) (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm' : 15 ≤ m+1) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∀ B : InitialCoverSystem a r m hm M,
      ∃ R : alternatingGroup (Fin (m+1)) →
          Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
          Multiplicative (FreeAbelianGroup (Fin m × Fin 2)),
        ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k) := by
  obtain ⟨L,hL⟩ := source_constant_covariance_eventually a r m hm hr hm'
  refine ⟨L,fun M hM B => ?_⟩
  obtain ⟨c,hcp,hcb,R,hc⟩ := hL M hM
  have he : c = B.c := by
    apply MonoidHom.eq_of_eqOn_dense alternatingGroup.closure_isThreeCycles_eq_top
    intro s hs
    have hs' : s.val.support.card ≤ 5 := by rw [hs.card_support]; omega
    exact (hcb ⟨s.val,s.property,hs'⟩).trans (B.c_base ⟨s.val,s.property,hs'⟩).symm
  subst c
  exact ⟨R,(hc B.t B.t_base).1⟩

namespace OffsetFrame
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}

def zero (I : Finset (Fin (m+1))) : OffsetFrame a r m hm I (fun _ => 0) where
  k := 1
  d := 0
  projection := by rw [map_one,trackTranslation_zero]
  prescribed := by intros; rfl

end OffsetFrame

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem constant_mem_polygonStars (s : alternatingGroup (Fin (m+1))) :
    B.c s ∈ ⨆ V : polygonAlgebra a, (B.polygonStar hlarge h hr V).range := by
  obtain ⟨x,hx⟩ := universalProjection_surjective (E := alternatingGroup (Fin (m+1))) s
  apply (le_iSup (fun V : polygonAlgebra a => (B.polygonStar hlarge h hr V).range) (wholePolygon a))
  refine ⟨x,?_⟩
  rw [B.polygonStar_whole hlarge h hr]
  exact congrArg B.c hx

theorem distinctSlotStar_zero_constant (ι κ : Fin 5 ↪ Fin (m+1))
    (c : alternatingGroup (Fin (m+1))) (hc : ∀ j, c.val (ι j) = κ j)
    (V : polygonAlgebra a) :
    (MulAut.conj (B.c c)).toMonoidHom.comp
      (B.distinctSlotStar hlarge h hr ι (fun _ => 0) (OffsetFrame.zero _) V) =
      B.distinctSlotStar hlarge h hr κ (fun _ => 0) (OffsetFrame.zero _) V := by
  apply B.distinctSlotStar_common_frame_transport hlarge h hr ι κ
    (fun _ => 0) (fun _ => 0) (OffsetFrame.zero _) (OffsetFrame.zero _) rfl V (B.c c)
  · change B.c c ∈ (⨆ V : polygonAlgebra a, (B.polygonStar hlarge h hr V).range).map
      (MulAut.conj (B.t 1)).toMonoidHom
    refine ⟨B.c c,B.constant_mem_polygonStars hlarge h hr c,?_⟩
    simp
  · intro j x
    rw [show coverMap M (alternatingGenerator a r m hm) (B.c c) =
      conditionalAlternatingHom (wholePolygon a) c from DFunLike.congr_fun B.c_projection c]
    change conditionalPerm (wholePolygon a) c.val (ι j,translate a 0 x.val) =
      (κ j,translate a 0 x.val)
    simp [conditionalPerm,wholePolygon,hc]

theorem distinctSlotStar_offset_formula (ι : Fin 5 ↪ Fin (m+1))
    (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u) (V : polygonAlgebra a) :
    B.distinctSlotStar hlarge h hr ι u F V =
      (MulAut.conj (B.t F.k)).toMonoidHom.comp
        (B.distinctSlotStar hlarge h hr ι (fun _ => 0) (OffsetFrame.zero _) V) := by
  ext s : 1
  simp [distinctSlotStar,frameStar,OffsetFrame.zero]

def constantReindexedFrame
    (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (ι κ : Fin 5 ↪ Fin (m+1)) (c : alternatingGroup (Fin (m+1)))
    (hc : ∀ j, c.val (ι j) = κ j)
    (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u) :
    OffsetFrame a r m hm (orderedTrackAlphabet κ) (fun i => u (c.val.symm i)) where
  k := R c F.k
  d := fun i => F.d (c.val.symm i)
  projection := by
    have he := congrArg (coverMap M (alternatingGenerator a r m hm)) (hR c F.k)
    simp only [map_mul,map_inv] at he
    rw [show coverMap M (alternatingGenerator a r m hm) (B.c c) =
      conditionalAlternatingHom (wholePolygon a) c from DFunLike.congr_fun B.c_projection c,
      show coverMap M (alternatingGenerator a r m hm) (B.t F.k) =
      sourceLatticeMap a r m hm F.k from DFunLike.congr_fun B.t_projection F.k,
      show coverMap M (alternatingGenerator a r m hm) (B.t (R c F.k)) =
      sourceLatticeMap a r m hm (R c F.k) from DFunLike.congr_fun B.t_projection (R c F.k)] at he
    have hf := congrArg Subtype.val he
    change conditionalHom (wholePolygon a) c.val * sourceLatticeFullMap a r m hm F.k *
      (conditionalHom (wholePolygon a) c.val)⁻¹ = sourceLatticeFullMap a r m hm (R c F.k) at hf
    rw [F.projection,constant_conjugate_translation] at hf
    exact hf.symm
  prescribed := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hi
    have he : c.val.symm (κ j) = ι j := by rw [← hc j]; exact c.val.symm_apply_apply _
    rw [he]
    exact F.prescribed (ι j) (orderedTrackAlphabet_mem ι j)

theorem distinctSlotStar_constant_transport
    (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (ι κ : Fin 5 ↪ Fin (m+1)) (c : alternatingGroup (Fin (m+1)))
    (hc : ∀ j, c.val (ι j) = κ j)
    (b : Fin (m+1)) (hb : b ∉ orderedTrackAlphabet κ)
    (u v : Fin (m+1) → CutRing × CutRing)
    (huv : ∀ j, u (ι j) = v (κ j))
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u)
    (G : OffsetFrame a r m hm (orderedTrackAlphabet κ) v) (V : polygonAlgebra a) :
    (MulAut.conj (B.c c)).toMonoidHom.comp (B.distinctSlotStar hlarge h hr ι u F V) =
      B.distinctSlotStar hlarge h hr κ v G V := by
  let H := B.constantReindexedFrame R hR ι κ c hc u F
  have hG : B.distinctSlotStar hlarge h hr κ (fun i => u (c.val.symm i)) H V =
      B.distinctSlotStar hlarge h hr κ v G V := by
    unfold distinctSlotStar
    rw [B.frameStar_independent hlarge h hr (orderedTrackAlphabet κ)
      (by rw [orderedTrackAlphabet,Finset.card_map,Finset.card_univ,Fintype.card_fin])
      b hb (fun i => u (c.val.symm i)) v H G (by
        intro i hi
        obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hi
        rw [← hc j,c.val.symm_apply_apply]
        simpa only [hc j] using huv j) V]
  rw [← hG,B.distinctSlotStar_offset_formula hlarge h hr ι u F V,
    B.distinctSlotStar_offset_formula hlarge h hr κ (fun i => u (c.val.symm i)) H V]
  ext s : 1
  have hz := DFunLike.congr_fun (B.distinctSlotStar_zero_constant hlarge h hr ι κ c hc V) s
  change B.c c * B.distinctSlotStar hlarge h hr ι (fun _ => 0) (OffsetFrame.zero _) V s * (B.c c)⁻¹ =
    B.distinctSlotStar hlarge h hr κ (fun _ => 0) (OffsetFrame.zero _) V s at hz
  change B.c c * (B.t F.k * _ * (B.t F.k)⁻¹) * (B.c c)⁻¹ = B.t (R c F.k) * _ * (B.t (R c F.k))⁻¹
  rw [← hR c F.k,← hz]
  group

end InitialCoverSystem

end SimpleAmenable

end OAI
