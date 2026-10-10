import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonPlacementArea

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonPiecewiseSlots

open Classical Set
namespace PolygonArea

@[simp] theorem val_finset_inf {a : ℕ} {ι : Type*} (s : Finset ι) (f : ι → polygonAlgebra a) :
    (s.inf f).val=⋂i∈s,(f i).val := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.inf_insert,BooleanSubalgebra.val_inf,ih]

end PolygonArea
namespace PolygonObject

noncomputable def whole (a m : ℕ) : PolygonObject a := ⟨m,fun _ => ⊤⟩

theorem intoWhole_hasTable {a : ℕ} {U V : PolygonObject a} {f : U.Point → V.Point}
    (hf : HasTable f) :
    HasTable (fun x => (⟨(f x).val,by trivial⟩ : (whole a V.tracks).Point)) := hf

end PolygonObject
namespace PolygonPiecewise
variable {a m n : ℕ}

theorem even_slots (U : PolygonObject a) (f : Fin n → U.Point → TrackPoint a m)
    (hf : Function.Injective (fun p : Fin n × U.Point => f p.1 p.2))
    (ht : ∀i, PolygonObject.HasTable
      (fun x => (⟨f i x,by trivial⟩ : (PolygonObject.whole a m).Point)))
    (σ : Equiv.Perm (Fin n)) (hσ : σ∈alternatingGroup (Fin n)) :
    ∃g : polygonAlternatingGroup a m,
      (∀i x,g.val.val (f i x)=f (σ i) x) ∧
      (∀y∉Set.range (fun p : Fin n × U.Point => f p.1 p.2),g.val.val y=y) := by
  change ∀i, ∃S : Finset (PolygonObject.Chart U.tracks m),
    (∀c∈S,c.Holds (fun x => (⟨f i x,by trivial⟩ : (PolygonObject.whole a m).Point))) ∧
      (∀x : U.Point, ∃c∈S,c.Contains (V:=PolygonObject.whole a m) x) at ht
  choose S hS hcover using ht
  let C := ∀i : Fin n,{c : PolygonObject.Chart U.tracks m // c∈S i}
  let D (r : Fin U.tracks) (c : C) : polygonAlgebra a :=
    U.cell r ⊓ Finset.univ.inf (fun i => if (c i).val.source=r then (c i).val.domain else ⊥)
  have memD (r : Fin U.tracks) (c : C) (x : GenericSquare a) :
      x∈(D r c).val ↔ x∈(U.cell r).val ∧ ∀i,(c i).val.source=r ∧ x∈(c i).val.domain.val := by
    simp only [D,BooleanSubalgebra.val_inf,PolygonArea.val_finset_inf]
    constructor
    · rintro ⟨hx,hc⟩
      refine ⟨hx,fun i => ?_⟩
      have h := Set.mem_iInter₂.mp hc i (Finset.mem_univ i)
      split_ifs at h with hi
      · exact ⟨hi,h⟩
      · exact False.elim h
    · rintro ⟨hx,hc⟩
      exact ⟨hx,Set.mem_iInter₂.mpr (fun i _ => by simp only [(hc i).1,ite_true];exact (hc i).2)⟩
  have covD (r : Fin U.tracks) (x : GenericSquare a) (hx : x∈(U.cell r).val) :
      ∃c : C,x∈(D r c).val := by
    have hc (i : Fin n) : ∃c : {c : PolygonObject.Chart U.tracks m // c∈S i},
        c.val.source=r ∧ x∈c.val.domain.val := by
      obtain ⟨c,hc,hh⟩ := hcover i ⟨(r,x),hx⟩
      exact ⟨⟨c,hc⟩,hh.1.symm,hh.2⟩
    choose c hc using hc
    exact ⟨c,(memD r c x).mpr ⟨hx,hc⟩⟩
  have hp (r : Fin U.tracks) := Fintype.exists_disjointed_le (D r)
  choose P hP hSup hdis using hp
  have coverP (r : Fin U.tracks) (x : GenericSquare a) (hx : x∈(U.cell r).val) :
      ∃c : C,x∈(P r c).val := by
    obtain ⟨c,hc⟩ := covD r x hx
    have he := congrArg (fun Q : polygonAlgebra a => Q.val) (hSup r)
    simp only [PolygonArea.val_finset_sup,Finset.mem_univ,Set.iUnion_true] at he
    have hh : x∈⋃c,(D r c).val := Set.mem_iUnion.mpr ⟨c,hc⟩
    rw [←he] at hh
    exact Set.mem_iUnion.mp hh
  let J := Fin U.tracks × C
  let cell (j : J) := P j.1 j.2
  let member (j : J) (p : U.Point) : Prop := p.val.1=j.1 ∧ p.val.2∈(cell j).val
  have cell_sub (j : J) : (cell j).val⊆(U.cell j.1).val :=
    fun x hx => ((memD j.1 j.2 x).mp (hP j.1 j.2 hx)).1
  have member_unique (j l : J) (p : U.Point) (hj : member j p) (hl : member l p) : j=l := by
    have hr : j.1=l.1 := hj.1.symm.trans hl.1
    apply Prod.ext hr
    by_contra hc
    have h : Disjoint (P j.1 j.2) (P j.1 l.2) := hdis j.1 hc
    rw [disjoint_iff] at h
    have he := congrArg (fun Q : polygonAlgebra a => Q.val) h
    have hh : p.val.2∈(P j.1 j.2 ⊓ P j.1 l.2).val := ⟨hj.2,by simpa only [hr] using hl.2⟩
    rw [he] at hh
    exact hh
  let slots (j : J) (i : Fin n) : Fin m × (CutRing×CutRing) := ((j.2 i).val.target,(j.2 i).val.shift)
  have chart_eq (j : J) (i : Fin n) (x : (cell j).val) :
      f i ⟨(j.1,x.val),cell_sub j x.property⟩=SlotMap a m (cell j) (slots j) (i,x) := by
    have hd := (memD j.1 j.2 x.val).mp (hP j.1 j.2 x.property)
    obtain ⟨hu,he⟩ := hS i (j.2 i).val (j.2 i).property x.val (hd.2 i).2
    have hx : (⟨((j.2 i).val.source,x.val),hu⟩ : U.Point)=
        ⟨(j.1,x.val),cell_sub j x.property⟩ := Subtype.ext (Prod.ext (hd.2 i).1 rfl)
    change f i ⟨((j.2 i).val.source,x.val),hu⟩=SlotMap a m (cell j) (slots j) (i,x) at he
    rwa [hx] at he
  have slot_inj (j : J) : Function.Injective (SlotMap a m (cell j) (slots j)) := by
    rintro ⟨i,x⟩ ⟨l,y⟩ h
    rw [←chart_eq j i x,←chart_eq j l y] at h
    have hh := @hf (i,⟨(j.1,x.val),cell_sub j x.property⟩)
      (l,⟨(j.1,y.val),cell_sub j y.property⟩) h
    apply Prod.ext
    · exact congrArg (fun p : Fin n × U.Point => p.1) hh
    · exact Subtype.ext (congrArg (fun p : Fin n × U.Point => p.2.val.2) hh)
  let piece (j : J) : polygonAlternatingGroup a m :=
    ⟨slotHom (cell j) (slots j) (slot_inj j) σ,slotHom_alternating_mem _ _ _ hσ⟩
  have piece_on (j : J) (i : Fin n) (p : U.Point) :
      (piece j).val.val (f i p)=if member j p then f (σ i) p else f i p := by
    by_cases hp : member j p
    · rw [ite_eq_left hp]
      let x : (cell j).val := ⟨p.val.2,hp.2⟩
      have he : p=⟨(j.1,x.val),cell_sub j x.property⟩ := Subtype.ext (Prod.ext hp.1 rfl)
      rw [he,chart_eq j i x]
      exact (slotPerm_apply _ _ _ _ i x).trans (chart_eq j (σ i) x).symm
    · rw [ite_eq_right hp]
      apply slotPerm_apply_of_notMem
      rintro ⟨⟨l,x⟩,he⟩
      rw [←chart_eq j l x] at he
      have hh := @hf (l,⟨(j.1,x.val),cell_sub j x.property⟩) (i,p) he
      have he' : (⟨(j.1,x.val),cell_sub j x.property⟩ : U.Point)=p := congrArg Prod.snd hh
      exact hp ⟨(congrArg (fun p : U.Point => p.val.1) he').symm,
        by simpa only [←he'] using x.property⟩
  have piece_out (j : J) (y : TrackPoint a m)
      (hy : y∉Set.range (fun p : Fin n × U.Point => f p.1 p.2)) : (piece j).val.val y=y := by
    apply slotPerm_apply_of_notMem
    rintro ⟨⟨i,x⟩,he⟩
    exact hy ⟨(i,⟨(j.1,x.val),cell_sub j x.property⟩),(chart_eq j i x).trans he⟩
  have assemble (s : Finset J) : ∃g : polygonAlternatingGroup a m,
      (∀i p,g.val.val (f i p)=if ∃j∈s,member j p then f (σ i) p else f i p) ∧
      (∀y∉Set.range (fun p : Fin n × U.Point => f p.1 p.2),g.val.val y=y) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by simp,fun _ _ => rfl⟩
    | @insert j s hj ih =>
      obtain ⟨g,hg,hout⟩ := ih
      refine ⟨piece j*g,?_,?_⟩
      · intro i p
        change (piece j).val.val (g.val.val (f i p))=_
        rw [hg]
        by_cases hp : member j p
        · have hn : ¬∃l∈s,member l p := by
            rintro ⟨l,hl,hlp⟩
            exact hj ((member_unique j l p hp hlp).symm ▸ hl)
          rw [ite_eq_right hn,piece_on,ite_eq_left hp,ite_eq_left ⟨j,Finset.mem_insert_self _ _,hp⟩]
        · by_cases hs : ∃l∈s,member l p
          · rw [ite_eq_left hs,piece_on,ite_eq_right hp]
            rw [ite_eq_left (by obtain ⟨l,hl,hlp⟩ := hs;exact ⟨l,Finset.mem_insert_of_mem hl,hlp⟩)]
          · have hn : ¬∃l∈insert j s,member l p := by simpa only [Finset.mem_insert,exists_prop,
                or_and_right,exists_or,exists_eq_left] using not_or.mpr ⟨hp,hs⟩
            rw [ite_eq_right hs,piece_on,ite_eq_right hp,ite_eq_right hn]
      · intro y hy
        change (piece j).val.val (g.val.val y)=y
        rw [hout y hy,piece_out j y hy]
  obtain ⟨g,hg,hout⟩ := assemble Finset.univ
  refine ⟨g,?_,hout⟩
  intro i p
  rw [hg]
  obtain ⟨c,hc⟩ := coverP p.val.1 p.val.2 p.property
  exact ite_eq_left ⟨(p.val.1,c),Finset.mem_univ _,rfl,hc⟩

end PolygonPiecewise
end PolygonPiecewiseSlots

end SimpleAmenable
end
end

end OAI
