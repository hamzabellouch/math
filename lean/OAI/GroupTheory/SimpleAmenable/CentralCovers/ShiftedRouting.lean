import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.RoutingIndependence
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CanonicalSlotStars
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FrameCompatibility
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TranslationRoutingHelpers

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ShiftedRouting
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

namespace SlotRouting
variable {B hlarge h hr}

noncomputable def privateBank (V : polygonAlgebra a) (i : Fin 5 → Fin (m+1))
    (u : Fin 5 → CutRing × CutRing) (P : PrivateRoutingBank i)
    (b : Fin (m+1)) (hb : b ∉ P.alphabet)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j)))) :
    B.SlotRouting hlarge h hr V i u where
  alphabet := P.alphabet
  card_le := P.alphabet_card
  source_mem := P.source_mem
  target := P.target
  target_mem := fun j => P.row_subset j (orderedTrackAlphabet_mem _ 1)
  offsets := orderedOffsets P.target u
  offsets_spec := orderedOffsets_apply P.target u
  frame := balancedOffsetFrame a r m hm _ b (by
    intro ht
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp ht
    exact hb (P.row_subset j (orderedTrackAlphabet_mem _ 1))) (orderedOffsets P.target u)
  word := B.privateRoutingWord hlarge h hr i u P b hb V
  aligned := (B.privateRoutingWord_properties hlarge h hr i u P b hb V hinj).1
  supported := (B.privateRoutingWord_properties hlarge h hr i u P b hb V hinj).2.1
  transport := (B.privateRoutingWord_properties hlarge h hr i u P b hb V hinj).2.2

noncomputable def shift {V : polygonAlgebra a} {i : Fin 5 → Fin (m+1)}
    {u : Fin 5 → CutRing × CutRing} (ρ : B.SlotRouting hlarge h hr V i u)
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (d : Fin (m+1) → CutRing × CutRing)
    (hd : sourceLatticeFullMap a r m hm k=trackTranslation d)
    (htarget : ∀ j, d (ρ.target j)=d (i j))
    (halign : (MulAut.conj (B.t k)) ρ.word ∈
      ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range)
    (hsupp : (MulAut.conj (B.t k)) ρ.word ∈ sourceAlignedGroup a r m hm M B.t ρ.alphabet) :
    B.SlotRouting hlarge h hr V i (fun j => d (i j)+u j) where
  alphabet := ρ.alphabet
  card_le := ρ.card_le
  source_mem := ρ.source_mem
  target := ρ.target
  target_mem := ρ.target_mem
  offsets := d+ρ.offsets
  offsets_spec := by intro j; simp only [Pi.add_apply,ρ.offsets_spec,htarget]
  frame := ρ.frame.shift k d hd
  word := (MulAut.conj (B.t k)) ρ.word
  aligned := halign
  supported := hsupp
  transport := by
    intro j x
    have ht : (coverMap M (alternatingGenerator a r m hm) (B.t k)).val=trackTranslation d := by
      have hh := congrArg Subtype.val (DFunLike.congr_fun B.t_projection k)
      exact hh.trans hd
    have hp : (i j,translate a (d (i j)+u j) x.val) =
        (trackTranslation d).val (i j,translate a (u j) x.val) := by
      simp only [trackTranslation_apply,translate_add]
    rw [hp]
    change (coverMap M (alternatingGenerator a r m hm) (B.t k*ρ.word*(B.t k)⁻¹)).val.val _ = _
    rw [map_mul,map_mul,map_inv]
    change (coverMap M (alternatingGenerator a r m hm) (B.t k)).val.val
      ((coverMap M (alternatingGenerator a r m hm) ρ.word).val.val
        ((coverMap M (alternatingGenerator a r m hm) (B.t k)).val.val.symm _)) = _
    rw [ht,Equiv.symm_apply_apply,ρ.transport j x]
    simp only [trackTranslation_apply,htarget,translate_add]

theorem shift_star {V : polygonAlgebra a} {i : Fin 5 → Fin (m+1)}
    {u : Fin 5 → CutRing × CutRing} (ρ : B.SlotRouting hlarge h hr V i u)
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (d : Fin (m+1) → CutRing × CutRing)
    (hd : sourceLatticeFullMap a r m hm k=trackTranslation d)
    (htarget : ∀ j, d (ρ.target j)=d (i j))
    (halign : (MulAut.conj (B.t k)) ρ.word ∈
      ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range)
    (hsupp : (MulAut.conj (B.t k)) ρ.word ∈ sourceAlignedGroup a r m hm M B.t ρ.alphabet) :
    (ρ.shift k d hd htarget halign hsupp).star =
      (MulAut.conj (B.t k)).toMonoidHom.comp ρ.star := by
  ext s : 1
  have he := DFunLike.congr_fun (B.frameStar_shift hlarge h hr (orderedTrackAlphabet ρ.target)
    ρ.offsets ρ.frame k d hd V) (universalMap (orderedTrackHom ρ.target) s)
  change B.frameStar hlarge h hr _ _ _ V _ =
    B.t k*B.distinctSlotStar hlarge h hr ρ.target ρ.offsets ρ.frame V s*(B.t k)⁻¹ at he
  change (B.t k*ρ.word*(B.t k)⁻¹)⁻¹ *
    B.frameStar hlarge h hr (orderedTrackAlphabet ρ.target) (d+ρ.offsets) (ρ.frame.shift k d hd) V
      (universalMap (orderedTrackHom ρ.target) s) *((B.t k*ρ.word*(B.t k)⁻¹)⁻¹)⁻¹ =
    B.t k*(ρ.word⁻¹*B.distinctSlotStar hlarge h hr ρ.target ρ.offsets ρ.frame V s*(ρ.word⁻¹)⁻¹)*(B.t k)⁻¹
  rw [he]
  group

end SlotRouting

variable (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (hwide : 100 ≤ m+1)

include R hR

theorem slotStar_zero_commute (V : polygonAlgebra a) (i : Fin 5 → Fin (m+1))
    (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j))))
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (d : Fin (m+1) → CutRing × CutRing)
    (hd : sourceLatticeFullMap a r m hm k=trackTranslation d)
    (J : Finset (Fin (m+1))) (hJ : J.card≤28)
    (hsupp : ∀ t, t∉J → d t=0) (hz : ∀ j, d (i j)=0)
    (s : UniversalExtension (alternatingGroup (Fin 5))) :
    Commute (B.t k) (B.slotStar hlarge h hr hwide V i u hinj s) := by
  classical
  have hres : 20 ≤ ((Finset.univ : Finset (Fin (m+1))) \
      (J ∪ Finset.univ.image i)).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have h₁ := Finset.card_union_le J (Finset.univ.image i)
    have h₂ := Finset.card_image_le (f := i) (s := Finset.univ)
    simp only [Finset.card_univ,Fintype.card_fin] at h₂ ⊢
    omega
  obtain ⟨P,hP⟩ := exists_privateRoutingBank i J hres
  obtain ⟨b,_,hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show P.alphabet.card < (Finset.univ : Finset (Fin (m+1))).card by
      have hc := P.alphabet_card
      simp only [Finset.card_univ,Fintype.card_fin]
      omega)
  let ρ := SlotRouting.privateBank (B := B) (hlarge := hlarge) (h := h) (hr := hr)
    V i u P b hb hinj
  rw [B.slotStar_eq_routing hlarge h hr R hR hwide V i u hinj ρ]
  have hzrow (j l : Fin 5) : d (P.row j l)=0 := by
    by_cases hl : l=0
    · subst l; rw [P.source j]; exact hz j
    · exact hsupp _ (hP j l hl)
  have hw : Commute (B.t k) ρ.word := by
    change Commute (B.t k) (((List.finRange 5).map _).prod)
    apply Commute.list_prod_right
    intro z hmem
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hmem
    exact B.distinctSlotStar_zero_commute hlarge h hr (P.row j) b
      (fun ht => hb (P.row_subset j ht)) (fun _ => u j) _ V k d hd (hzrow j) privateCycleStar
  have ht : Commute (B.t k) (B.distinctSlotStar hlarge h hr ρ.target ρ.offsets ρ.frame V s) :=
    B.distinctSlotStar_zero_commute hlarge h hr ρ.target b
      (by intro ht; obtain ⟨j,_,he⟩ := Finset.mem_map.mp ht
          exact hb (he ▸ P.row_subset j (orderedTrackAlphabet_mem _ 1)))
      ρ.offsets ρ.frame V k d hd (fun j => hzrow j 1) s
  exact (hw.inv_right.mul_right ht).mul_right hw.inv_right.inv_right

end InitialCoverSystem
end ShiftedRouting

end SimpleAmenable
end
end

end OAI
