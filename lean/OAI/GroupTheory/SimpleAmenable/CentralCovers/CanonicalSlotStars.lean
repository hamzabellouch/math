import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.RoutingIndependence

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

namespace SlotRouting
variable {B hlarge h hr}

def restrict {V : polygonAlgebra a} {i : Fin 5 → Fin (m+1)}
    {u : Fin 5 → CutRing × CutRing} (ρ : B.SlotRouting hlarge h hr V i u)
    (W : polygonAlgebra a) (hW : W ≤ V) : B.SlotRouting hlarge h hr W i u where
  alphabet := ρ.alphabet
  card_le := ρ.card_le
  source_mem := ρ.source_mem
  target := ρ.target
  target_mem := ρ.target_mem
  offsets := ρ.offsets
  offsets_spec := ρ.offsets_spec
  frame := ρ.frame
  word := ρ.word
  aligned := ρ.aligned
  supported := ρ.supported
  transport := fun j x => ρ.transport j ⟨x.val,hW x.property⟩

noncomputable def identity (V : polygonAlgebra a) (ι : Fin 5 ↪ Fin (m+1))
    (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u) :
    B.SlotRouting hlarge h hr V (fun j => ι j) (fun j => u (ι j)) where
  alphabet := orderedTrackAlphabet ι
  card_le := by simp [orderedTrackAlphabet]
  source_mem := orderedTrackAlphabet_mem ι
  target := ι
  target_mem := orderedTrackAlphabet_mem ι
  offsets := u
  offsets_spec := fun _ => rfl
  frame := F
  word := 1
  aligned := Subgroup.one_mem _
  supported := Subgroup.one_mem _
  transport := by intro j x; simp

theorem identity_star (V : polygonAlgebra a) (ι : Fin 5 ↪ Fin (m+1))
    (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u) :
    (identity (B := B) (hlarge := hlarge) (h := h) (hr := hr) V ι u F).star =
      B.distinctSlotStar hlarge h hr ι u F V := by
  ext s : 1
  change 1⁻¹*B.distinctSlotStar hlarge h hr ι u F V s*(1⁻¹)⁻¹ = _
  simp

theorem star_union {V W : polygonAlgebra a} {i : Fin 5 → Fin (m+1)}
    {u : Fin 5 → CutRing × CutRing} (ρ : B.SlotRouting hlarge h hr (V ⊔ W) i u)
    (hd : Disjoint V.val W.val) (s : UniversalExtension (alternatingGroup (Fin 5))) :
    ρ.star s=(ρ.restrict V le_sup_left).star s*(ρ.restrict W le_sup_right).star s := by
  have he := B.frameStar_union hlarge h hr (orderedTrackAlphabet ρ.target)
    ρ.offsets ρ.frame V W hd (universalMap (orderedTrackHom ρ.target) s)
  change (MulAut.conj ρ.word⁻¹).toMonoidHom
    (B.frameStar hlarge h hr _ ρ.offsets ρ.frame (V ⊔ W)
      (universalMap (orderedTrackHom ρ.target) s)) = _
  rw [he,map_mul]
  rfl

theorem star_commute {V W : polygonAlgebra a} {i : Fin 5 → Fin (m+1)}
    {u : Fin 5 → CutRing × CutRing} (ρ : B.SlotRouting hlarge h hr (V ⊔ W) i u)
    (hd : Disjoint V.val W.val) (s t : UniversalExtension (alternatingGroup (Fin 5))) :
    Commute ((ρ.restrict V le_sup_left).star s) ((ρ.restrict W le_sup_right).star t) :=
  (B.frameStar_commute hlarge h hr (orderedTrackAlphabet ρ.target) ρ.offsets ρ.frame V W hd
    (universalMap (orderedTrackHom ρ.target) s) (universalMap (orderedTrackHom ρ.target) t)).map
      (MulAut.conj ρ.word⁻¹).toMonoidHom

end SlotRouting

noncomputable def slotStar (hwide : 100 ≤ m+1) (V : polygonAlgebra a)
    (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j)))) :
    UniversalExtension (alternatingGroup (Fin 5)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm) :=
  (B.slotRouting_nonempty hlarge h hr (by omega) V i u hinj).some.star

variable (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (hwide : 100 ≤ m+1)

include R hR

theorem slotStar_eq_routing (V : polygonAlgebra a)
    (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j))))
    (ρ : B.SlotRouting hlarge h hr V i u) :
    B.slotStar hlarge h hr hwide V i u hinj=ρ.star :=
  SlotRouting.independent R hR (by omega) _ ρ

theorem slotStar_distinct (V : polygonAlgebra a) (ι : Fin 5 ↪ Fin (m+1))
    (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (ι j,u (ι j))))) :
    B.slotStar hlarge h hr hwide V (fun j => ι j) (fun j => u (ι j)) hinj =
      B.distinctSlotStar hlarge h hr ι u F V := by
  rw [B.slotStar_eq_routing hlarge h hr R hR hwide V _ _ hinj (SlotRouting.identity V ι u F)]
  exact SlotRouting.identity_star V ι u F

theorem slotStar_aligned_transport (V : polygonAlgebra a)
    (i k : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (hi : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j))))
    (hk : Function.Injective (SlotMap a (m+1) V (fun j => (k j,u j))))
    (J : Finset (Fin (m+1))) (hJ : J.card ≤ 5)
    (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range)
    (hzJ : z ∈ sourceAlignedGroup a r m hm M B.t J)
    (htransport : ∀ (j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (i j,translate a (u j) x.val) =
        (k j,translate a (u j) x.val)) :
    (MulAut.conj z).toMonoidHom.comp (B.slotStar hlarge h hr hwide V i u hi) =
      B.slotStar hlarge h hr hwide V k u hk :=
  SlotRouting.aligned_transport R hR _ _ J (by omega) z hz hzJ htransport

theorem slotStar_union (V W : polygonAlgebra a)
    (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) (V ⊔ W) (fun j => (i j,u j))))
    (hd : Disjoint V.val W.val) (s : UniversalExtension (alternatingGroup (Fin 5))) :
    B.slotStar hlarge h hr hwide (V ⊔ W) i u hinj s =
      B.slotStar hlarge h hr hwide V i u (SlotMap_injective_mono _ le_sup_left hinj) s *
      B.slotStar hlarge h hr hwide W i u (SlotMap_injective_mono _ le_sup_right hinj) s := by
  let ρ := (B.slotRouting_nonempty hlarge h hr (by omega) (V ⊔ W) i u hinj).some
  rw [B.slotStar_eq_routing hlarge h hr R hR hwide _ _ _ hinj ρ,
    B.slotStar_eq_routing hlarge h hr R hR hwide _ _ _ _ (ρ.restrict V le_sup_left),
    B.slotStar_eq_routing hlarge h hr R hR hwide _ _ _ _ (ρ.restrict W le_sup_right)]
  exact ρ.star_union hd s

theorem slotStar_commute (V W : polygonAlgebra a)
    (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) (V ⊔ W) (fun j => (i j,u j))))
    (hd : Disjoint V.val W.val) (s t : UniversalExtension (alternatingGroup (Fin 5))) :
    Commute
      (B.slotStar hlarge h hr hwide V i u (SlotMap_injective_mono _ le_sup_left hinj) s)
      (B.slotStar hlarge h hr hwide W i u (SlotMap_injective_mono _ le_sup_right hinj) t) := by
  let ρ := (B.slotRouting_nonempty hlarge h hr (by omega) (V ⊔ W) i u hinj).some
  rw [B.slotStar_eq_routing hlarge h hr R hR hwide _ _ _ _ (ρ.restrict V le_sup_left),
    B.slotStar_eq_routing hlarge h hr R hR hwide _ _ _ _ (ρ.restrict W le_sup_right)]
  exact ρ.star_commute hd s t

end InitialCoverSystem

end SimpleAmenable

end OAI
