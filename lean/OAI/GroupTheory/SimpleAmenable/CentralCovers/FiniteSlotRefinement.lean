import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.InitialCoverSystem
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CanonicalSlotStars
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PeriodicSlotStars

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiniteSlotRefinement

theorem polygon_finite_cover_induction {a : ℕ} (P : polygonAlgebra a → Prop)
    (hbot : P ⊥)
    (hunion : ∀ U W : polygonAlgebra a, Disjoint U.val W.val → P U → P W → P (U ⊔ W))
    (s : Finset (polygonAlgebra a)) (V : polygonAlgebra a)
    (hcover : V ≤ s.sup id)
    (hlocal : ∀ U ∈ s, ∀ W : polygonAlgebra a, W ≤ U → P W) : P V := by
  classical
  induction s using Finset.induction_on generalizing V with
  | empty =>
    have he : V=⊥ := le_antisymm (by simpa using hcover) bot_le
    simpa only [he] using hbot
  | @insert U s hUs ih =>
    have hleft : P (V ⊓ U) := hlocal U (Finset.mem_insert_self _ _) _ inf_le_right
    have hright : P (V ⊓ Uᶜ) := by
      apply ih (V ⊓ Uᶜ)
      · intro x hx
        have hc := hcover hx.1
        rw [Finset.sup_insert] at hc
        exact hc.resolve_left hx.2
      · intro W hW Z hZ
        exact hlocal W (Finset.mem_insert_of_mem hW) Z hZ
    have hd : Disjoint (V ⊓ U).val (V ⊓ Uᶜ).val := Set.disjoint_left.mpr (by
      intro x hx hy
      exact hy.2 hx.2)
    have he : (V ⊓ U) ⊔ (V ⊓ Uᶜ)=V := by
      ext x
      change (x∈V.val ∧ x∈U.val) ∨ (x∈V.val ∧ x∉U.val) ↔ x∈V.val
      tauto
    rw [← he]
    exact hunion _ _ hd hleft hright

theorem polygon_mem_finset_inf {a : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → polygonAlgebra a) (x : GenericSquare a) :
    x∈(s.inf f).val ↔ ∀ j∈s, x∈(f j).val := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.inf_empty,Finset.notMem_empty,IsEmpty.forall_iff,implies_true]
             exact iff_true_intro (Set.mem_univ x)
  | @insert j s hjs ih =>
    rw [Finset.inf_insert]
    change x∈(f j).val ∧ x∈(s.inf f).val ↔ _
    rw [ih]
    simp only [Finset.mem_insert,forall_eq_or_imp]

theorem finite_slot_chart_cover {a m : ℕ} (f : TrackPoint a m → TrackPoint a m)
    (hf : HasTranslationTable f) (V : polygonAlgebra a)
    (i : Fin 5 → Fin m) (u : Fin 5 → CutRing × CutRing) :
    ∃ s : Finset (polygonAlgebra a), V ≤ s.sup id ∧
      ∀ W ∈ s, ∃ (k : Fin 5 → Fin m) (v : Fin 5 → CutRing × CutRing),
        ∀ (j : Fin 5) (x : W.val),
          f (i j,translate a (u j) x.val)=(k j,translate a (v j) x.val) := by
  classical
  obtain ⟨t,ht,hcover⟩ := hf
  let cell : (Fin 5 → t) → polygonAlgebra a := fun c =>
    V ⊓ (Finset.univ : Finset (Fin 5)).inf (fun j =>
      if (c j).val.source=i j then
        ⟨translate a (u j) ⁻¹' (c j).val.domain.val,
          polygon_preimage_translate _ (c j).val.domain.property⟩ else ⊥)
  have hcell (c : Fin 5 → t) (x : GenericSquare a) : x∈(cell c).val ↔
      x∈V.val ∧ ∀ j, (c j).val.source=i j ∧ translate a (u j) x∈(c j).val.domain.val := by
    change x∈V.val ∧ x∈((Finset.univ : Finset (Fin 5)).inf _ : polygonAlgebra a).val ↔ _
    rw [polygon_mem_finset_inf]
    simp only [Finset.mem_univ,true_implies]
    apply and_congr_right
    intro _
    apply forall_congr'
    intro j
    by_cases he : (c j).val.source=i j <;> simp [he]
  refine ⟨Finset.univ.image cell,?_,?_⟩
  · intro x hx
    have hchoice : ∀ j : Fin 5, ∃ c : t, c.val.source=i j ∧
        translate a (u j) x∈c.val.domain.val := by
      intro j
      obtain ⟨c,hc,hci,hcx⟩ := hcover (i j,translate a (u j) x)
      exact ⟨⟨c,hc⟩,hci.symm,hcx⟩
    choose c hc using hchoice
    have hxcell : x∈(cell c).val := (hcell c x).mpr ⟨hx,hc⟩
    have hh : cell c ≤ (Finset.univ.image cell).sup id :=
      Finset.le_sup (f := id) (s := Finset.univ.image cell) (b := cell c)
        (Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩)
    exact hh hxcell
  · intro W hW
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hW
    refine ⟨fun j => (c j).val.target,fun j => (c j).val.shift+u j,?_⟩
    intro j x
    have hx := ((hcell c x.val).mp x.property).2 j
    rw [← hx.1,ht (c j).val (c j).property _ hx.2,translate_add]

end FiniteSlotRefinement

section SlotTransportClosure

theorem SlotMap_injective_of_transport {a m : ℕ} (V : polygonAlgebra a)
    (i k : Fin 5 → Fin m) (u v : Fin 5 → CutRing × CutRing)
    (f : TrackPoint a m → TrackPoint a m) (hf : Function.Injective f)
    (hi : Function.Injective (SlotMap a m V (fun j => (i j,u j))))
    (htr : ∀ (j : Fin 5) (x : V.val),
      f (i j,translate a (u j) x.val)=(k j,translate a (v j) x.val)) :
    Function.Injective (SlotMap a m V (fun j => (k j,v j))) := by
  have he : SlotMap a m V (fun j => (k j,v j))=f ∘ SlotMap a m V (fun j => (i j,u j)) := by
    funext p
    exact (htr p.1 p.2).symm
  rw [he]
  exact hf.comp hi

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hwide : 100 ≤ m+1)

def ExactSlotTransport (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (V : polygonAlgebra a) (i k : Fin 5 → Fin (m+1))
    (u v : Fin 5 → CutRing × CutRing) : Prop :=
  ∀ (hi : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j)) ))
    (hk : Function.Injective (SlotMap a (m+1) V (fun j => (k j,v j)) )),
    (MulAut.conj z).toMonoidHom.comp (B.slotStar hlarge h hr hwide V i u hi) =
      B.slotStar hlarge h hr hwide V k v hk

def UniformSlotTransport (z : BoundedRelationCover M (alternatingGenerator a r m hm)) : Prop :=
  ∀ (V : polygonAlgebra a) (i k : Fin 5 → Fin (m+1)) (u v : Fin 5 → CutRing × CutRing),
    (∀ (j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (i j,translate a (u j) x.val)=
        (k j,translate a (v j) x.val)) →
    B.ExactSlotTransport hlarge h hr hwide z V i k u v

variable (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
include R hR

theorem exactSlotTransport_empty (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (i k : Fin 5 → Fin (m+1)) (u v : Fin 5 → CutRing × CutRing) :
    B.ExactSlotTransport hlarge h hr hwide z ⊥ i k u v := by
  intro hi hk
  rw [B.slotStar_empty hlarge h hr R hR hwide,B.slotStar_empty hlarge h hr R hR hwide]
  ext s : 1
  simp

theorem exactSlotTransport_union (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (V W : polygonAlgebra a) (i k : Fin 5 → Fin (m+1)) (u v : Fin 5 → CutRing × CutRing)
    (hd : Disjoint V.val W.val)
    (hV : B.ExactSlotTransport hlarge h hr hwide z V i k u v)
    (hW : B.ExactSlotTransport hlarge h hr hwide z W i k u v) :
    B.ExactSlotTransport hlarge h hr hwide z (V ⊔ W) i k u v := by
  intro hi hk
  ext s : 1
  change (MulAut.conj z).toMonoidHom (B.slotStar hlarge h hr hwide (V ⊔ W) i u hi s)=_
  rw [B.slotStar_union hlarge h hr R hR hwide V W i u hi hd,map_mul,
    B.slotStar_union hlarge h hr R hR hwide V W k v hk hd]
  rw [show (MulAut.conj z).toMonoidHom (B.slotStar hlarge h hr hwide V i u
    (SlotMap_injective_mono _ le_sup_left hi) s)=_ from
      DFunLike.congr_fun (hV _ _) s]
  rw [show (MulAut.conj z).toMonoidHom (B.slotStar hlarge h hr hwide W i u
    (SlotMap_injective_mono _ le_sup_right hi) s)=_ from
      DFunLike.congr_fun (hW _ _) s]

theorem exactSlotTransport_cover (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (V : polygonAlgebra a) (i k : Fin 5 → Fin (m+1)) (u v : Fin 5 → CutRing × CutRing)
    (s : Finset (polygonAlgebra a)) (hs : V ≤ s.sup id)
    (hl : ∀ W∈s, ∀ Z : polygonAlgebra a, Z≤W → Z≤V →
      B.ExactSlotTransport hlarge h hr hwide z Z i k u v) :
    B.ExactSlotTransport hlarge h hr hwide z V i k u v := by
  have hp : ∀ hV : V≤V, B.ExactSlotTransport hlarge h hr hwide z V i k u v := by
    refine polygon_finite_cover_induction
      (fun W => W≤V → B.ExactSlotTransport hlarge h hr hwide z W i k u v)
      (fun _ => B.exactSlotTransport_empty hlarge h hr hwide R hR z i k u v) ?_ s V hs ?_
    · intro U W hd hU hW he
      exact B.exactSlotTransport_union hlarge h hr hwide R hR z U W i k u v hd
        (hU (le_trans le_sup_left he)) (hW (le_trans le_sup_right he))
    · exact hl
  exact hp le_rfl

theorem uniformSlotTransport_one :
    B.UniformSlotTransport hlarge h hr hwide 1 := by
  intro V i k u v htr hi hk
  have he := B.slotStar_parameterwise hlarge h hr R hR hwide V i k u v hi hk (by
    intro j x
    simpa only [map_one,Subgroup.coe_one,Equiv.Perm.one_apply] using htr j x)
  rw [← he]
  ext s : 1
  simp

omit R hR in
theorem uniformSlotTransport_inv
    (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : B.UniformSlotTransport hlarge h hr hwide z) :
    B.UniformSlotTransport hlarge h hr hwide z⁻¹ := by
  intro V i k u v htr hi hk
  have htr' : ∀ (j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (k j,translate a (v j) x.val)=
        (i j,translate a (u j) x.val) := by
    intro j x
    have hh := congrArg (coverMap M (alternatingGenerator a r m hm) z).val.val (htr j x)
    simpa only [map_inv,Subgroup.coe_inv,Equiv.Perm.inv_def,Equiv.apply_symm_apply] using hh.symm
  have he := hz V k i v u htr' hk hi
  ext s : 1
  have hh := DFunLike.congr_fun he s
  change z*B.slotStar hlarge h hr hwide V k v hk s*z⁻¹=
    B.slotStar hlarge h hr hwide V i u hi s at hh
  change z⁻¹*B.slotStar hlarge h hr hwide V i u hi s*(z⁻¹)⁻¹=_
  rw [← hh]
  group

theorem uniformSlotTransport_mul
    (z y : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : B.UniformSlotTransport hlarge h hr hwide z)
    (hy : B.UniformSlotTransport hlarge h hr hwide y) :
    B.UniformSlotTransport hlarge h hr hwide (z*y) := by
  intro V i k u v htr
  obtain ⟨s,hs,hcharts⟩ := finite_slot_chart_cover
    (coverMap M (alternatingGenerator a r m hm) y).val.val
    (coverMap M (alternatingGenerator a r m hm) y).val.property V i u
  apply B.exactSlotTransport_cover hlarge h hr hwide R hR (z*y) V i k u v s hs
  intro W hW Z hZW hZV hi hk
  obtain ⟨l,b,hl⟩ := hcharts W hW
  have hytr : ∀ (j : Fin 5) (x : Z.val),
      (coverMap M (alternatingGenerator a r m hm) y).val.val (i j,translate a (u j) x.val)=
        (l j,translate a (b j) x.val) := fun j x => hl j ⟨x.val,hZW x.property⟩
  have hl_inj := SlotMap_injective_of_transport Z i l u b _
    (coverMap M (alternatingGenerator a r m hm) y).val.val.injective hi hytr
  have hztr : ∀ (j : Fin 5) (x : Z.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (l j,translate a (b j) x.val)=
        (k j,translate a (v j) x.val) := by
    intro j x
    have hh := htr j ⟨x.val,hZV x.property⟩
    rw [map_mul] at hh
    change (coverMap M (alternatingGenerator a r m hm) z).val.val
      ((coverMap M (alternatingGenerator a r m hm) y).val.val (i j,translate a (u j) x.val))=_ at hh
    rw [hytr j x] at hh
    exact hh
  have he_y := hy Z i l u b hytr hi hl_inj
  have he_z := hz Z l k b v hztr hl_inj hk
  ext t : 1
  have ey := DFunLike.congr_fun he_y t
  have ez := DFunLike.congr_fun he_z t
  change y*B.slotStar hlarge h hr hwide Z i u hi t*y⁻¹=
    B.slotStar hlarge h hr hwide Z l b hl_inj t at ey
  change z*B.slotStar hlarge h hr hwide Z l b hl_inj t*z⁻¹=
    B.slotStar hlarge h hr hwide Z k v hk t at ez
  change (z*y)*B.slotStar hlarge h hr hwide Z i u hi t*(z*y)⁻¹=_
  calc
    _ = z*(y*B.slotStar hlarge h hr hwide Z i u hi t*y⁻¹)*z⁻¹ := by group
    _ = _ := by rw [ey,ez]

def slotTransportSubgroup : Subgroup (BoundedRelationCover M (alternatingGenerator a r m hm)) where
  carrier := B.UniformSlotTransport hlarge h hr hwide
  one_mem' := B.uniformSlotTransport_one hlarge h hr hwide R hR
  mul_mem' := fun {z y} => B.uniformSlotTransport_mul hlarge h hr hwide R hR z y
  inv_mem' := fun {z} => B.uniformSlotTransport_inv hlarge h hr hwide z

end InitialCoverSystem
end SlotTransportClosure

end SimpleAmenable
end
end

end OAI
