import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.IntervalBar

namespace OAI

section

section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal
universe u v u' v' w
namespace IntervalBar.Diagram

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C]
variable {D : Type u'} [Groupoid.{v'} D] [MonoidalCategory D]
variable {I : Type w} [Preorder I]

noncomputable def mapObj (F : C ⥤ D) [F.Monoidal] (A : Diagram C I) : Diagram D I where
  obj i j h := F.obj (A.obj i j h)
  unit i := F.mapIso (A.unit i) ≪≫ (Functor.Monoidal.εIso F).symm
  cut i j k hij hjk := Functor.Monoidal.μIso F _ _ ≪≫ F.mapIso (A.cut i j k hij hjk)
  left_unit i j h := by
    simp only [Iso.trans_hom,Functor.mapIso_hom,Functor.Monoidal.μIso_hom,
      Iso.symm_hom,Functor.Monoidal.εIso_inv]
    rw [A.left_unit,Functor.map_comp,Functor.Monoidal.map_whiskerRight,
      Functor.Monoidal.map_leftUnitor]
    simp only [Category.assoc,Functor.Monoidal.μ_δ_assoc,comp_whiskerRight]
  right_unit i j h := by
    simp only [Iso.trans_hom,Functor.mapIso_hom,Functor.Monoidal.μIso_hom,
      Iso.symm_hom,Functor.Monoidal.εIso_inv]
    rw [A.right_unit,Functor.map_comp,Functor.Monoidal.map_whiskerLeft,
      Functor.Monoidal.map_rightUnitor]
    simp only [Category.assoc,Functor.Monoidal.μ_δ_assoc,whiskerLeft_comp]
  associativity i j k l hij hjk hkl := by
    simp only [Iso.trans_hom,Functor.mapIso_hom,Functor.Monoidal.μIso_hom]
    simp only [comp_whiskerRight,whiskerLeft_comp,Category.assoc]
    rw [μ_natural_left_assoc,←F.map_comp, A.associativity]
    simp only [Functor.map_comp]
    rw [Functor.LaxMonoidal.associativity_assoc, μ_natural_right_assoc]

noncomputable def map (F : C ⥤ D) [F.Monoidal] : Diagram C I ⥤ Diagram D I where
  obj := mapObj F
  map f := {
    app i j h := F.map (f.app i j h)
    unit i := by
      simp only [mapObj,Iso.trans_hom,Functor.mapIso_hom,Iso.symm_hom,Functor.Monoidal.εIso_inv]
      rw [←Category.assoc,←F.map_comp,f.unit]
    cut i j k hij hjk := by
      simp only [mapObj,Iso.trans_hom,Functor.mapIso_hom,Functor.Monoidal.μIso_hom]
      rw [μ_natural_assoc,←F.map_comp,f.cut,F.map_comp,Category.assoc] }
  map_id A := by apply Hom.ext; intro i j h; exact F.map_id _
  map_comp f g := by apply Hom.ext; intro i j h; exact F.map_comp _ _

noncomputable def pair (A : Diagram C I) (B : Diagram D I) : Diagram (C×D) I where
  obj i j h := (A.obj i j h,B.obj i j h)
  unit i := (A.unit i).prod (B.unit i)
  cut i j k hij hjk := (A.cut i j k hij hjk).prod (B.cut i j k hij hjk)
  left_unit i j h := by ext; exacts [A.left_unit i j h,B.left_unit i j h]
  right_unit i j h := by ext; exacts [A.right_unit i j h,B.right_unit i j h]
  associativity i j k l hij hjk hkl := by
    ext; exacts [A.associativity i j k l hij hjk hkl,B.associativity i j k l hij hjk hkl]

noncomputable def pairHom {A A' : Diagram C I} {B B' : Diagram D I}
    (f : A ⟶ A') (g : B ⟶ B') : pair A B ⟶ pair A' B' where
  app i j h := (f.app i j h,g.app i j h)
  unit i := by ext; exacts [f.unit i,g.unit i]
  cut i j k hij hjk := by ext; exacts [f.cut i j k hij hjk,g.cut i j k hij hjk]

noncomputable def constantUnit : Diagram C I where
  obj _ _ _ := 𝟙_ C
  unit _ := Iso.refl _
  cut _ _ _ _ _ := λ_ _
  left_unit _ _ _ := by simp
  right_unit _ _ _ := by simp; exact unitors_equal
  associativity _ _ _ _ _ _ _ := by monoidal

end IntervalBar.Diagram

end

section
open CategoryTheory MonoidalCategory BraidedCategory
universe u v
namespace IntervalBar
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

lemma tensorμ_braiding (W X Y Z : C) :
    ((β_ W X).hom ⊗ₘ (β_ Y Z).hom) ≫ tensorμ X W Z Y =
      tensorμ W X Y Z ≫ (β_ (W⊗Y) (X⊗Z)).hom := by
  simp [tensorμ, SymmetricCategory.braiding_swap_eq_inv_braiding Y X,
    MonoidalCategory.tensorHom_def]
end IntervalBar

end

section

open CategoryTheory MonoidalCategory
universe u v w
namespace IntervalBar
namespace Normal

variable {A : Type u}
open FreeMonoidalCategory

def fold : List A → FreeMonoidalCategory A
  | [] => .unit
  | a::l => .tensor (.of a) (fold l)

def appendIso : ∀ l r : List A, fold l ⊗ fold r ≅ fold (l++r)
  | [],_ => λ_ _
  | a::l,r => (α_ _ _ _ ) ≪≫ (whiskerLeftIso (.of a) (appendIso l r))

lemma segment_append (l : List A) (i j k : ℕ) (hij : i≤j) (hjk : j≤k) :
    (l.drop i).take (j-i) ++ (l.drop j).take (k-j) = (l.drop i).take (k-i) := by
  have hji : j=i+(j-i) := by omega
  have hki : k-i=(j-i)+(k-j) := by omega
  rw [hki,List.take_add,List.drop_drop,←hji]

def segment (l : List A) (i j : ℕ) : List A := (l.drop i).take (j-i)
@[simp] lemma segment_self (l : List A) (i : ℕ) : segment l i i=[] := by
  simp [segment]

def diagram {n : ℕ} (l : List A) : Diagram (FreeMonoidalCategory A) (Fin (n+1)) where
  obj i j _ := fold (segment l i.val j.val)
  unit i := eqToIso (by simp [fold])
  cut i j k hij hjk := appendIso _ _ ≪≫ eqToIso (congrArg fold (segment_append l i j k hij hjk))
  left_unit _ _ _ := Subsingleton.elim _ _
  right_unit _ _ _ := Subsingleton.elim _ _
  associativity _ _ _ _ _ _ _ := Subsingleton.elim _ _

variable {C : Type v} [Groupoid.{w} C] [MonoidalCategory C]

@[simp] lemma project_whiskerLeft (f : A → C) (X : FreeMonoidalCategory A)
    {Y Z : FreeMonoidalCategory A} (h : Y ⟶ Z) :
    (project f).map (X ◁ h) = (project f).obj X ◁ (project f).map h := by
  induction h using Quotient.inductionOn with | h h => rfl
@[simp] lemma project_whiskerRight (f : A → C) {Y Z : FreeMonoidalCategory A}
    (h : Y ⟶ Z) (X : FreeMonoidalCategory A) :
    (project f).map (h ▷ X) = (project f).map h ▷ (project f).obj X := by
  induction h using Quotient.inductionOn with | h h => rfl

@[simp] lemma project_leftUnitor (f : A → C) (X : FreeMonoidalCategory A) :
    (project f).map (λ_ X).hom = (λ_ ((project f).obj X)).hom := rfl
@[simp] lemma project_rightUnitor (f : A → C) (X : FreeMonoidalCategory A) :
    (project f).map (ρ_ X).hom = (ρ_ ((project f).obj X)).hom := rfl
@[simp] lemma project_associator (f : A → C) (X Y Z : FreeMonoidalCategory A) :
    (project f).map (α_ X Y Z).hom =
      (α_ ((project f).obj X) ((project f).obj Y) ((project f).obj Z)).hom := rfl

variable {I : Type u} [Preorder I]
def projectDiagram (f : A → C) (D : Diagram (FreeMonoidalCategory A) I) : Diagram C I where
  obj i j h := (project f).obj (D.obj i j h)
  unit i := (project f).mapIso (D.unit i)
  cut i j k hij hjk := (project f).mapIso (D.cut i j k hij hjk)
  left_unit i j h := by
    have he := congrArg ((project f).map) (D.left_unit i j h)
    simp only [Functor.map_comp,project_whiskerRight,project_leftUnitor] at he
    exact he
  right_unit i j h := by
    have he := congrArg ((project f).map) (D.right_unit i j h)
    simp only [Functor.map_comp,project_whiskerLeft,project_rightUnitor] at he
    exact he
  associativity i j k l hij hjk hkl := by
    have he := congrArg ((project f).map) (D.associativity i j k l hij hjk hkl)
    simp only [Functor.map_comp,project_whiskerLeft,project_whiskerRight,project_associator] at he
    exact he

lemma segment_finRange {n : ℕ} (i : Fin n) :
    segment (List.finRange n) i.val (i.val+1) = [i] := by
  simp only [segment,Nat.add_sub_cancel_left]
  rw [List.take_one_drop_eq_of_lt_length (by simp)]
  congr 1
  apply Fin.ext
  simp

noncomputable def elementaryDiagram {n : ℕ} (f : Fin n → C) : Diagram C (Fin (n+1)) :=
  projectDiagram f (diagram (List.finRange n))

noncomputable def elementaryIso {n : ℕ} (f : Fin n → C) :
    (Diagram.eval n).obj (elementaryDiagram f) ≅ f where
  hom i := (eqToIso (by
    change (project f).obj (fold (segment (List.finRange n) i.val (i.val+1))) = _
    rw [segment_finRange]
    rfl) ≪≫ ρ_ (f i)).hom
  inv i := (eqToIso (by
    change (project f).obj (fold (segment (List.finRange n) i.val (i.val+1))) = _
    rw [segment_finRange]
    rfl) ≪≫ ρ_ (f i)).inv
  hom_inv_id := by funext i; exact Iso.hom_inv_id _
  inv_hom_id := by funext i; exact Iso.inv_hom_id _

noncomputable instance {n : ℕ} : (Diagram.eval (C:=C) n).EssSurj where
  mem_essImage f := ⟨elementaryDiagram f,⟨elementaryIso f⟩⟩

end Normal
end IntervalBar

end

end

end OAI
