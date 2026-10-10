import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonGroupoidTracks

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section PolygonObjectSum

open Classical Set CategoryTheory
namespace PolygonObject
variable {a : ℕ}

@[simp] theorem arrow_id_apply (U : PolygonObject a) (x : U.Point) : (𝟙 U : U ⟶ U).toEquiv x=x := rfl
@[simp] theorem arrow_comp_apply {U V W : PolygonObject a} (f : U ⟶ V) (g : V ⟶ W) (x : U.Point) :
    (f≫g).toEquiv x=g.toEquiv (f.toEquiv x) := rfl

noncomputable def sum (U V : PolygonObject a) : PolygonObject a :=
  ⟨U.tracks+V.tracks,Fin.addCases U.cell V.cell⟩

noncomputable def sumPointEquiv (U V : PolygonObject a) :
    U.Point ⊕ V.Point ≃ (sum U V).Point where
  toFun := Sum.elim
    (fun x => ⟨(x.val.1.castAdd V.tracks,x.val.2),by simpa [sum] using x.property⟩)
    (fun x => ⟨(x.val.1.natAdd U.tracks,x.val.2),by simpa [sum] using x.property⟩)
  invFun x := Fin.addCases (motive:=fun i => x.val.2∈((sum U V).cell i).val → U.Point ⊕ V.Point)
    (fun i => fun h : x.val.2∈((sum U V).cell (i.castAdd V.tracks)).val =>
      Sum.inl ⟨(i,x.val.2),by simpa [sum] using h⟩)
    (fun i => fun h : x.val.2∈((sum U V).cell (i.natAdd U.tracks)).val =>
      Sum.inr ⟨(i,x.val.2),by simpa [sum] using h⟩) x.val.1 x.property
  left_inv x := by cases x <;> simp
  right_inv x := by
    obtain ⟨⟨i,x⟩,hx⟩ := x
    induction i using Fin.addCases <;> simp

@[simp] theorem sumPointEquiv_inl (U V : PolygonObject a) (x : U.Point) :
    (sumPointEquiv U V (.inl x)).val=(x.val.1.castAdd V.tracks,x.val.2) := rfl
@[simp] theorem sumPointEquiv_inr (U V : PolygonObject a) (x : V.Point) :
    (sumPointEquiv U V (.inr x)).val=(x.val.1.natAdd U.tracks,x.val.2) := rfl

theorem positional_hasTable {U V : PolygonObject a} (f : U.Point → V.Point)
    (hf : ∀x,(f x).val.2=x.val.2)
    (hpoly : ∀i j,{x : GenericSquare a | ∃hx : x∈(U.cell i).val,
      (f ⟨(i,x),hx⟩).val.1=j} ∈ polygonAlgebra a) : HasTable f := by
  let c : Fin U.tracks × Fin V.tracks → Chart (a:=a) U.tracks V.tracks :=
    fun ij => ⟨ij.1,ij.2,0,⟨_,hpoly ij.1 ij.2⟩⟩
  refine ⟨Finset.univ.image c,?_,?_⟩
  · intro d hd
    obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp hd
    rintro x ⟨hx,hj⟩
    refine ⟨hx,?_⟩
    apply Prod.ext hj
    exact (hf ⟨(i,x),hx⟩).trans (translate_zero a x).symm
  · intro x
    refine ⟨c (x.val.1,(f x).val.1),Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,rfl,?_⟩
    exact ⟨x.property,rfl⟩

noncomputable def sumArrow {U V W Z : PolygonObject a} (f : U ⟶ W) (g : V ⟶ Z) :
    sum U V ⟶ sum W Z where
  toEquiv := (sumPointEquiv U V).symm.trans ((Equiv.sumCongr f.toEquiv g.toEquiv).trans (sumPointEquiv W Z))
  hasTable := by
    obtain ⟨s,hs,hcover⟩ := f.hasTable
    obtain ⟨t,ht,htcover⟩ := g.hasTable
    let L : Chart (a:=a) U.tracks W.tracks → Chart (a:=a) (U.tracks+V.tracks) (W.tracks+Z.tracks) :=
      fun c => ⟨c.source.castAdd V.tracks,c.target.castAdd Z.tracks,c.shift,c.domain⟩
    let R : Chart (a:=a) V.tracks Z.tracks → Chart (a:=a) (U.tracks+V.tracks) (W.tracks+Z.tracks) :=
      fun c => ⟨c.source.natAdd U.tracks,c.target.natAdd W.tracks,c.shift,c.domain⟩
    refine ⟨s.image L ∪ t.image R,?_,?_⟩
    · intro c hc
      rcases Finset.mem_union.mp hc with hc|hc
      · obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
        intro x hx
        obtain ⟨hu,he⟩ := hs d hd x hx
        refine ⟨by simpa [sum,L] using hu,?_⟩
        change (sumPointEquiv W Z (Equiv.sumCongr f.toEquiv g.toEquiv
          ((sumPointEquiv U V).symm (sumPointEquiv U V (.inl ⟨(d.source,x),hu⟩))))).val=_
        rw [Equiv.symm_apply_apply]
        change (sumPointEquiv W Z (.inl (f.toEquiv ⟨(d.source,x),hu⟩))).val=_
        rw [sumPointEquiv_inl,he]
        rfl
      · obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
        intro x hx
        obtain ⟨hv,he⟩ := ht d hd x hx
        refine ⟨by simpa [sum,R] using hv,?_⟩
        change (sumPointEquiv W Z (Equiv.sumCongr f.toEquiv g.toEquiv
          ((sumPointEquiv U V).symm (sumPointEquiv U V (.inr ⟨(d.source,x),hv⟩))))).val=_
        rw [Equiv.symm_apply_apply]
        change (sumPointEquiv W Z (.inr (g.toEquiv ⟨(d.source,x),hv⟩))).val=_
        rw [sumPointEquiv_inr,he]
        rfl
    · intro x
      obtain ⟨y,rfl⟩ := (sumPointEquiv U V).surjective x
      cases y with
      | inl y =>
        obtain ⟨c,hc,hy⟩ := hcover y
        exact ⟨L c,Finset.mem_union_left _ (Finset.mem_image_of_mem L hc),
          congrArg (Fin.castAdd V.tracks) hy.1,hy.2⟩
      | inr y =>
        obtain ⟨c,hc,hy⟩ := htcover y
        exact ⟨R c,Finset.mem_union_right _ (Finset.mem_image_of_mem R hc),
          congrArg (Fin.natAdd U.tracks) hy.1,hy.2⟩

@[simp] theorem sumArrow_inl {U V W Z : PolygonObject a} (f : U ⟶ W) (g : V ⟶ Z) (x : U.Point) :
    (sumArrow f g).toEquiv (sumPointEquiv U V (.inl x))=sumPointEquiv W Z (.inl (f.toEquiv x)) := by
  change sumPointEquiv W Z (Equiv.sumCongr f.toEquiv g.toEquiv ((sumPointEquiv U V).symm (sumPointEquiv U V (.inl x))))=_
  rw [Equiv.symm_apply_apply];rfl
@[simp] theorem sumArrow_inr {U V W Z : PolygonObject a} (f : U ⟶ W) (g : V ⟶ Z) (x : V.Point) :
    (sumArrow f g).toEquiv (sumPointEquiv U V (.inr x))=sumPointEquiv W Z (.inr (g.toEquiv x)) := by
  change sumPointEquiv W Z (Equiv.sumCongr f.toEquiv g.toEquiv ((sumPointEquiv U V).symm (sumPointEquiv U V (.inr x))))=_
  rw [Equiv.symm_apply_apply];rfl

theorem sumArrow_id (U V : PolygonObject a) : sumArrow (𝟙 U) (𝟙 V)=𝟙 (sum U V) := by
  apply Arrow.ext;apply Equiv.ext;intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv U V).surjective x
  cases y <;> simp

theorem sumArrow_comp {U U' U'' V V' V'' : PolygonObject a}
    (f : U ⟶ U') (f' : U' ⟶ U'') (g : V ⟶ V') (g' : V' ⟶ V'') :
    sumArrow (f≫f') (g≫g')=sumArrow f g ≫ sumArrow f' g' := by
  apply Arrow.ext;apply Equiv.ext;intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv U V).surjective x
  cases y <;> simp only [arrow_comp_apply,sumArrow_inl,sumArrow_inr]

end PolygonObject
end PolygonObjectSum

open Classical Set CategoryTheory
namespace PolygonObject
variable {a : ℕ}

noncomputable def complement (U : PolygonObject a) : PolygonObject a :=
  ⟨U.tracks,fun i => (U.cell i)ᶜ⟩

noncomputable def splitPointEquiv (U : PolygonObject a) :
    U.Point ⊕ (complement U).Point ≃ TrackPoint a U.tracks where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun x := if hx : x.2∈(U.cell x.1).val then .inl ⟨x,hx⟩ else .inr ⟨x,hx⟩
  left_inv := by
    rintro (x|x)
    · dsimp only
      exact dite_eq_left x.property
    · dsimp only
      exact dite_eq_right x.property
  right_inv x := by dsimp;split <;> rfl

@[simp] theorem splitPointEquiv_inl (U : PolygonObject a) (x : U.Point) :
    splitPointEquiv U (.inl x)=x.val := rfl
@[simp] theorem splitPointEquiv_inr (U : PolygonObject a) (x : (complement U).Point) :
    splitPointEquiv U (.inr x)=x.val := rfl

noncomputable def complementArrow (U : PolygonObject a) : sum U (complement U) ⟶ standard a U.tracks where
  toEquiv := (sumPointEquiv U (complement U)).symm.trans ((splitPointEquiv U).trans (standardPointEquiv a U.tracks).symm)
  hasTable := by
    let L (i : Fin U.tracks) : Chart (a:=a) (U.tracks+U.tracks) U.tracks := ⟨i.castAdd _,i,0,U.cell i⟩
    let R (i : Fin U.tracks) : Chart (a:=a) (U.tracks+U.tracks) U.tracks := ⟨i.natAdd _,i,0,(U.cell i)ᶜ⟩
    refine ⟨Finset.univ.image L ∪ Finset.univ.image R,?_,?_⟩
    · intro c hc
      rcases Finset.mem_union.mp hc with hc|hc
      · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hc
        intro x hx
        refine ⟨by simpa [sum,complement,L] using hx,?_⟩
        change (splitPointEquiv U ((sumPointEquiv U (complement U)).symm
          (sumPointEquiv U (complement U) (.inl ⟨(i,x),hx⟩))))=(i,translate a 0 x)
        rw [Equiv.symm_apply_apply,splitPointEquiv_inl,translate_zero]
      · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hc
        intro x hx
        refine ⟨(sumPointEquiv U (complement U) (.inr ⟨(i,x),hx⟩)).property,?_⟩
        change (splitPointEquiv U ((sumPointEquiv U (complement U)).symm
          (sumPointEquiv U (complement U) (.inr ⟨(i,x),hx⟩))))=(i,translate a 0 x)
        rw [Equiv.symm_apply_apply,splitPointEquiv_inr,translate_zero]
        rfl
    · intro x
      obtain ⟨y,rfl⟩ := (sumPointEquiv U (complement U)).surjective x
      cases y with
      | inl y => exact ⟨L y.val.1,Finset.mem_union_left _ (Finset.mem_image_of_mem L (Finset.mem_univ _)),rfl,y.property⟩
      | inr y => exact ⟨R y.val.1,Finset.mem_union_right _ (Finset.mem_image_of_mem R (Finset.mem_univ _)),rfl,y.property⟩

@[simp] theorem complementArrow_inl (U : PolygonObject a) (x : U.Point) :
    ((complementArrow U).toEquiv (sumPointEquiv U (complement U) (.inl x))).val=x.val := by
  change splitPointEquiv U ((sumPointEquiv U (complement U)).symm (sumPointEquiv U (complement U) (.inl x)))=x.val
  rw [Equiv.symm_apply_apply];rfl
@[simp] theorem complementArrow_inr (U : PolygonObject a) (x : (complement U).Point) :
    ((complementArrow U).toEquiv (sumPointEquiv U (complement U) (.inr x))).val=x.val := by
  change splitPointEquiv U ((sumPointEquiv U (complement U)).symm (sumPointEquiv U (complement U) (.inr x)))=x.val
  rw [Equiv.symm_apply_apply];rfl

theorem complementArrow_positional (U : PolygonObject a) : Positional (complementArrow U) := by
  intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv U (complement U)).surjective x
  cases y <;> simp only [complementArrow_inl,complementArrow_inr,sumPointEquiv_inl,sumPointEquiv_inr]

noncomputable def complementIso (U : PolygonObject a) : sum U (complement U) ≅ standard a U.tracks :=
  asIso (complementArrow U)

end PolygonObject

end SimpleAmenable

end OAI
