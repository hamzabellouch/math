import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.MarkedBlockDifferentials

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite HomologicalComplex
namespace MarkedH1
open FreeChains ComponentTranslation IntervalBar.Diagram RegularLabels

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma differential1 :
    ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 1 0 ≫ (gradedIso 0).hom =
      (gradedIso 1).hom ≫ (homologyRow (C:=C) 1).d 2 1 := by
  apply total_hom_ext (homologyDiagram (C:=C) 1)
  rintro ⟨⟨⟨h,v⟩,hn⟩,y,p,x⟩
  change h+v=1 at hn
  have hh:h≤1:=by omega
  interval_cases h
  · have hv:v=1:=by omega
    subst v
    have hy:y=![y 0]:=by ext index; fin_cases index; rfl
    have hx:x=![]:=Subsingleton.elim _ _
    rw [hy,hx]
    exact compat01 (y 0) (p)
  · have hv:v=0:=by omega
    subst v
    have hy:y=![]:=Subsingleton.elim _ _
    have hx:x=![x 0]:=by ext index; fin_cases index; rfl
    rw [hy,hx]
    exact compat10 (p) (x 0)
lemma differential2 :
    ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 2 1 ≫ (gradedIso 1).hom =
      (gradedIso 2).hom ≫ (homologyRow (C:=C) 1).d 3 2 := by
  apply total_hom_ext (homologyDiagram (C:=C) 1)
  rintro ⟨⟨⟨h,v⟩,hn⟩,y,p,x⟩
  change h+v=2 at hn
  have hh:h≤2:=by omega
  interval_cases h
  · have hv:v=2:=by omega
    subst v
    have hy:y=![y 0,y 1]:=by ext i; fin_cases i <;> rfl
    have hx:x=![]:=Subsingleton.elim _ _
    rw [hy,hx]
    exact compat02 (y 0) (y 1) (p)
  · have hv:v=1:=by omega
    subst v
    have hy:y=![y 0]:=by ext index; fin_cases index; rfl
    have hx:x=![x 0]:=by ext index; fin_cases index; rfl
    rw [hy,hx]
    exact compat11 (y 0) (p) (x 0)
  · have hv:v=0:=by omega
    subst v
    have hy:y=![]:=Subsingleton.elim _ _
    have hx:x=![x 0,x 1]:=by ext i; fin_cases i <;> rfl
    rw [hy,hx]
    exact compat20 (p) (x 1) (x 0)
lemma differential3 :
    ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 3 2 ≫ (gradedIso 2).hom =
      (gradedIso 3).hom ≫ (homologyRow (C:=C) 1).d 4 3 := by
  apply total_hom_ext (homologyDiagram (C:=C) 1)
  rintro ⟨⟨⟨h,v⟩,hn⟩,y,p,x⟩
  change h+v=3 at hn
  have hh:h≤3:=by omega
  interval_cases h
  · have hv:v=3:=by omega
    subst v
    have hy:y=![y 0,y 1,y 2]:=by ext i; fin_cases i <;> rfl
    have hx:x=![]:=Subsingleton.elim _ _
    rw [hy,hx]
    exact compat03 (y 0) (y 1) (y 2) (p)
  · have hv:v=2:=by omega
    subst v
    have hy:y=![y 0,y 1]:=by ext i; fin_cases i <;> rfl
    have hx:x=![x 0]:=by ext index; fin_cases index; rfl
    rw [hy,hx]
    exact compat12 (y 0) (y 1) (p) (x 0)
  · have hv:v=1:=by omega
    subst v
    have hy:y=![y 0]:=by ext index; fin_cases index; rfl
    have hx:x=![x 0,x 1]:=by ext i; fin_cases i <;> rfl
    rw [hy,hx]
    exact compat21 (y 0) (p) (x 1) (x 0)
  · have hv:v=0:=by omega
    subst v
    have hy:y=![]:=Subsingleton.elim _ _
    have hx:x=![x 0,x 1,x 2]:=by ext i; fin_cases i <;> rfl
    rw [hy,hx]
    exact compat30 (p) (x 2) (x 1) (x 0)
noncomputable def lowHomologyIso :
    ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).homology 2 ≅
      (homologyRow (C:=C) 1).homology 3 :=
  by
    let K := (RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c
    let L := homologyRow (C:=C) 1
    let e : K.sc' 3 2 1 ≅ L.sc' 4 3 2 :=
      ShortComplex.isoMk (gradedIso 3) (gradedIso 2) (gradedIso 1)
        (differential3 (C:=C)).symm (differential2 (C:=C)).symm
    exact (ShortComplex.homologyFunctor A).mapIso
      (K.isoSc' 3 2 1 (c.prev_eq' rfl) (c.next_eq' rfl) ≪≫ e ≪≫
        (L.isoSc' 4 3 2 (c.prev_eq' rfl) (c.next_eq' rfl)).symm)
end MarkedH1

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Opposite
namespace CommMonoidOpposite
open FreeChains

variable (P:Type) [CommMonoid P]
def functor : (SingleObj P)ᵒᵖ ⥤ SingleObj P where
  obj _ := SingleObj.star _
  map f := f.unop
  map_id _ := rfl
  map_comp _ _ := mul_comm _ _
instance : (functor P).Faithful where
  map_injective h := Quiver.Hom.unop_inj h
instance : (functor P).Full where
  map_surjective morphism := ⟨morphism.op,rfl⟩
instance : (functor P).EssSurj where
  mem_essImage _ := ⟨op (SingleObj.star _), ⟨eqToIso (Subsingleton.elim _ _)⟩⟩
instance : (functor P).IsEquivalence := ⟨inferInstance,inferInstance,inferInstance⟩
noncomputable def homologyIso (n:ℕ) :
    (nerve (SingleObj P)ᵒᵖ).homology Z n ≅ (nerve (SingleObj P)).homology Z n := by
  haveI:=NerveHomotopy.homologyMap_isIso (functor P) Z n
  exact asIso (SSet.homologyMap (nerveMap (functor P)) Z n)
end CommMonoidOpposite

end

end OAI
