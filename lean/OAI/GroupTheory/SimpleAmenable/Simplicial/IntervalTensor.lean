import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.IntervalMap
import OAI.GroupTheory.SimpleAmenable.Simplicial.IntervalExtension

namespace OAI

section

section

open CategoryTheory MonoidalCategory BraidedCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe u v w
namespace IntervalBar.Diagram

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {I : Type w} [Preorder I]

noncomputable def tensorObj (A B : Diagram C I) : Diagram C I :=
  mapObj (tensor C) (pair A B)

noncomputable def tensorHom {A A' B B' : Diagram C I} (f : A ⟶ A') (g : B ⟶ B') :
    tensorObj A B ⟶ tensorObj A' B' := (map (tensor C)).map (pairHom f g)

@[simp] lemma tensorObj_obj (A B : Diagram C I) (i j : I) (h : i≤j) :
    (tensorObj A B).obj i j h = A.obj i j h ⊗ B.obj i j h := rfl
@[simp] lemma tensorObj_unit (A B : Diagram C I) (i : I) :
    ((tensorObj A B).unit i).hom = ((A.unit i).hom ⊗ₘ (B.unit i).hom) ≫ (λ_ (𝟙_ C)).hom := rfl
@[simp] lemma tensorObj_cut (A B : Diagram C I) (i j k : I) (hij : i≤j) (hjk : j≤k) :
    ((tensorObj A B).cut i j k hij hjk).hom =
      tensorμ (A.obj i j hij) (B.obj i j hij) (A.obj j k hjk) (B.obj j k hjk) ≫
        ((A.cut i j k hij hjk).hom ⊗ₘ (B.cut i j k hij hjk).hom) := rfl
@[simp] lemma tensorHom_app {A A' B B' : Diagram C I} (f : A ⟶ A') (g : B ⟶ B')
    (i j : I) (h : i≤j) : (tensorHom f g).app i j h = f.app i j h ⊗ₘ g.app i j h := rfl

omit [SymmetricCategory C] in
lemma associator_unit_square {X Y Z : C} (f : X ⟶ 𝟙_ C) (g : Y ⟶ 𝟙_ C) (h : Z ⟶ 𝟙_ C) :
    (α_ X Y Z).hom ≫ (f ⊗ₘ ((g ⊗ₘ h) ≫ (λ_ (𝟙_ C)).hom)) ≫ (λ_ (𝟙_ C)).hom =
      (((f ⊗ₘ g) ≫ (λ_ (𝟙_ C)).hom) ⊗ₘ h) ≫ (λ_ (𝟙_ C)).hom := by
  rw [←tensorHom_comp_whiskerLeft,←tensorHom_comp_whiskerRight]
  simp only [Category.assoc]
  rw [←associator_naturality_assoc]
  congr 1
  monoidal

lemma associator_cut_square {X₁ X₂ X₃ Y₁ Y₂ Y₃ Z₁ Z₂ Z₃ : C}
    (f : X₁ ⊗ Y₁ ⟶ Z₁) (g : X₂ ⊗ Y₂ ⟶ Z₂) (h : X₃ ⊗ Y₃ ⟶ Z₃) :
    ((α_ X₁ X₂ X₃).hom ⊗ₘ (α_ Y₁ Y₂ Y₃).hom) ≫
      tensorμ X₁ (X₂ ⊗ X₃) Y₁ (Y₂ ⊗ Y₃) ≫
        (f ⊗ₘ (tensorμ X₂ X₃ Y₂ Y₃ ≫ (g ⊗ₘ h))) =
      (tensorμ (X₁ ⊗ X₂) X₃ (Y₁ ⊗ Y₂) Y₃ ≫
        ((tensorμ X₁ X₂ Y₁ Y₂ ≫ (f ⊗ₘ g)) ⊗ₘ h)) ≫ (α_ Z₁ Z₂ Z₃).hom := by
  rw [←whiskerLeft_comp_tensorHom,←whiskerRight_comp_tensorHom]
  simp only [Category.assoc]
  rw [←associator_monoidal_assoc,associator_naturality]

lemma leftUnitor_cut_square {X Y Z : C} (f : X ⊗ Y ⟶ Z) :
    ((λ_ X).hom ⊗ₘ (λ_ Y).hom) ≫ f =
      (tensorμ (𝟙_ C) X (𝟙_ C) Y ≫ ((λ_ (𝟙_ C)).hom ⊗ₘ f)) ≫ (λ_ Z).hom := by
  rw [leftUnitor_monoidal_assoc]
  simp only [MonoidalCategory.tensorHom_def,Category.assoc,leftUnitor_naturality]

lemma rightUnitor_cut_square {X Y Z : C} (f : X ⊗ Y ⟶ Z) :
    ((ρ_ X).hom ⊗ₘ (ρ_ Y).hom) ≫ f =
      (tensorμ X (𝟙_ C) Y (𝟙_ C) ≫ (f ⊗ₘ (λ_ (𝟙_ C)).hom)) ≫ (ρ_ Z).hom := by
  rw [rightUnitor_monoidal_assoc]
  simp only [MonoidalCategory.tensorHom_def',Category.assoc,rightUnitor_naturality]

noncomputable def associatorHom (A B D : Diagram C I) :
    tensorObj (tensorObj A B) D ⟶ tensorObj A (tensorObj B D) where
  app i j h := (α_ (A.obj i j h) (B.obj i j h) (D.obj i j h)).hom
  unit i := associator_unit_square (A.unit i).hom (B.unit i).hom (D.unit i).hom
  cut i j k hij hjk := associator_cut_square (A.cut i j k hij hjk).hom
    (B.cut i j k hij hjk).hom (D.cut i j k hij hjk).hom

noncomputable def leftUnitorHom (A : Diagram C I) : tensorObj constantUnit A ⟶ A where
  app i j h := (λ_ (A.obj i j h)).hom
  unit i := by
    change (λ_ _).hom ≫ (A.unit i).hom = (𝟙 _ ⊗ₘ (A.unit i).hom) ≫ (λ_ _).hom
    rw [id_tensorHom,leftUnitor_naturality]
  cut i j k hij hjk := leftUnitor_cut_square (A.cut i j k hij hjk).hom

noncomputable def rightUnitorHom (A : Diagram C I) : tensorObj A constantUnit ⟶ A where
  app i j h := (ρ_ (A.obj i j h)).hom
  unit i := by
    change (ρ_ _).hom ≫ (A.unit i).hom = ((A.unit i).hom ⊗ₘ 𝟙 _) ≫ (λ_ _).hom
    rw [tensorHom_id,unitors_equal,rightUnitor_naturality]
  cut i j k hij hjk := rightUnitor_cut_square (A.cut i j k hij hjk).hom

noncomputable instance monoidalStruct : MonoidalCategoryStruct (Diagram C I) where
  tensorObj := tensorObj
  tensorHom := tensorHom
  whiskerLeft A _ _ f := tensorHom (𝟙 A) f
  whiskerRight f A := tensorHom f (𝟙 A)
  tensorUnit := constantUnit
  associator A B D := asIso (associatorHom A B D)
  leftUnitor A := asIso (leftUnitorHom A)
  rightUnitor A := asIso (rightUnitorHom A)

@[simp] lemma whiskerLeft_app (A : Diagram C I) {B D : Diagram C I} (f : B ⟶ D)
    (i j : I) (h : i≤j) : (A ◁ f).app i j h = A.obj i j h ◁ f.app i j h := by
  change (𝟙 (A.obj i j h) ⊗ₘ f.app i j h) = _
  exact MonoidalCategory.id_tensorHom (A.obj i j h) (f.app i j h)
@[simp] lemma whiskerRight_app {A B : Diagram C I} (f : A ⟶ B) (D : Diagram C I)
    (i j : I) (h : i≤j) : (f ▷ D).app i j h = f.app i j h ▷ D.obj i j h := by
  change (f.app i j h ⊗ₘ 𝟙 (D.obj i j h)) = _
  exact MonoidalCategory.tensorHom_id (f.app i j h) (D.obj i j h)
@[simp] lemma associator_app (A B D : Diagram C I) (i j : I) (h : i≤j) :
    (α_ A B D).hom.app i j h = (α_ (A.obj i j h) (B.obj i j h) (D.obj i j h)).hom := rfl
@[simp] lemma leftUnitor_app (A : Diagram C I) (i j : I) (h : i≤j) :
    (λ_ A).hom.app i j h = (λ_ (A.obj i j h)).hom := rfl
@[simp] lemma rightUnitor_app (A : Diagram C I) (i j : I) (h : i≤j) :
    (ρ_ A).hom.app i j h = (ρ_ (A.obj i j h)).hom := rfl
@[simp] lemma tensor_app {A A' B B' : Diagram C I} (f : A ⟶ A') (g : B ⟶ B')
    (i j : I) (h : i≤j) : (f ⊗ₘ g).app i j h = f.app i j h ⊗ₘ g.app i j h := rfl
@[simp] lemma tensor_obj (A B : Diagram C I) (i j : I) (h : i≤j) :
    (A⊗B).obj i j h = A.obj i j h ⊗ B.obj i j h := rfl
@[simp] lemma tensorUnit_obj (i j : I) (h : i≤j) :
    (𝟙_ (Diagram C I)).obj i j h = 𝟙_ C := rfl

noncomputable instance monoidal : MonoidalCategory (Diagram C I) where
  tensorHom_def f g := by apply Hom.ext; intro i j h; simp [MonoidalCategory.tensorHom_def]
  id_tensorHom_id A B := by apply Hom.ext; intro i j h; simp
  tensorHom_comp_tensorHom f g h k := by apply Hom.ext; intro i j hij; simp
  whiskerLeft_id A B := by apply Hom.ext; intro i j h; simp
  id_whiskerRight A B := by apply Hom.ext; intro i j h; simp
  associator_naturality f g h := by apply Hom.ext; intro i j hij; simp
  leftUnitor_naturality f := by apply Hom.ext; intro i j h; simp
  rightUnitor_naturality f := by apply Hom.ext; intro i j h; simp
  pentagon A B D E := by apply Hom.ext; intro i j h; simp
  triangle A B := by apply Hom.ext; intro i j h; simp

noncomputable instance evalMonoidal (n : ℕ) : (eval (C:=C) n).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso := fun A B => Iso.refl _
    μIso_hom_natural_left := by intros; ext i; simp [eval]
    μIso_hom_natural_right := by intros; ext i; simp [eval]
    associativity := by intros; ext i; simp [eval]
    left_unitality := by intros; ext i; simp [eval]
    right_unitality := by intros; ext i; simp [eval] }

lemma braiding_unit_square {X Y : C} (f : X ⟶ 𝟙_ C) (g : Y ⟶ 𝟙_ C) :
    (β_ X Y).hom ≫ (g ⊗ₘ f) ≫ (λ_ (𝟙_ C)).hom =
      (f ⊗ₘ g) ≫ (λ_ (𝟙_ C)).hom := by
  rw [←braiding_naturality_assoc]
  simp only [braiding_tensorUnit_right,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rw [←unitors_equal]

lemma braiding_cut_square {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C}
    (f : X₁ ⊗ Y₁ ⟶ Z₁) (g : X₂ ⊗ Y₂ ⟶ Z₂) :
    ((β_ X₁ X₂).hom ⊗ₘ (β_ Y₁ Y₂).hom) ≫
      (tensorμ X₂ X₁ Y₂ Y₁ ≫ (g ⊗ₘ f)) =
      (tensorμ X₁ X₂ Y₁ Y₂ ≫ (f ⊗ₘ g)) ≫ (β_ Z₁ Z₂).hom := by
  rw [←Category.assoc,IntervalBar.tensorμ_braiding,Category.assoc,
    ←braiding_naturality,Category.assoc]

noncomputable def braidingHom (A B : Diagram C I) : A⊗B ⟶ B⊗A where
  app i j h := (β_ (A.obj i j h) (B.obj i j h)).hom
  unit i := braiding_unit_square (A.unit i).hom (B.unit i).hom
  cut i j k hij hjk := braiding_cut_square (A.cut i j k hij hjk).hom (B.cut i j k hij hjk).hom

omit [SymmetricCategory C] in
@[simp] lemma inv_app {A B : Diagram C I} (f : A ⟶ B) (i j : I) (h : i≤j) :
    (CategoryTheory.inv f).app i j h = CategoryTheory.inv (f.app i j h) := by
  rw [←Groupoid.inv_eq_inv]
  rfl

@[simp] lemma associator_inv_app (A B D : Diagram C I) (i j : I) (h : i≤j) :
    (α_ A B D).inv.app i j h = (α_ (A.obj i j h) (B.obj i j h) (D.obj i j h)).inv := by
  change (CategoryTheory.inv (associatorHom A B D)).app i j h = _
  rw [inv_app]
  apply IsIso.inv_eq_of_hom_inv_id
  exact Iso.hom_inv_id _

noncomputable instance braided : BraidedCategory (Diagram C I) where
  braiding A B := asIso (braidingHom A B)
  braiding_naturality_right A B D f := by
    apply Hom.ext; intro i j h
    change (𝟙 _ ⊗ₘ f.app i j h) ≫ (β_ _ _).hom = (β_ _ _).hom ≫ (f.app i j h ⊗ₘ 𝟙 _)
    simp
  braiding_naturality_left f D := by
    apply Hom.ext; intro i j h
    change (f.app i j h ⊗ₘ 𝟙 _) ≫ (β_ _ _).hom = (β_ _ _).hom ≫ (𝟙 _ ⊗ₘ f.app i j h)
    simp
  hexagon_forward A B D := by
    apply Hom.ext; intro i j h
    change (α_ _ _ _).hom ≫ (β_ _ _).hom ≫ (α_ _ _ _).hom =
      ((β_ _ _).hom ⊗ₘ 𝟙 _) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ₘ (β_ _ _).hom)
    simp only [tensorHom_id,id_tensorHom]
    exact hexagon_forward _ _ _
  hexagon_reverse A B D := by
    apply Hom.ext; intro i j h
    simp only [comp_app,associator_inv_app,whiskerLeft_app,whiskerRight_app]
    change (α_ _ _ _).inv ≫ (β_ _ _).hom ≫ (α_ _ _ _).inv =
      (_ ◁ (β_ _ _).hom) ≫ (α_ _ _ _).inv ≫ ((β_ _ _).hom ▷ _)
    exact hexagon_reverse _ _ _

@[simp] lemma braiding_app (A B : Diagram C I) (i j : I) (h : i≤j) :
    (β_ A B).hom.app i j h = (β_ (A.obj i j h) (B.obj i j h)).hom := rfl

noncomputable instance symmetric : SymmetricCategory (Diagram C I) where
  symmetry A B := by apply Hom.ext; intro i j h; simp

noncomputable instance evalEquivalence (n : ℕ) : (eval (C:=C) n).IsEquivalence where

noncomputable def evaluationEquivalence (n : ℕ) : Diagram C (Fin (n+1)) ≌ (Fin n → C) :=
  (eval n).asEquivalence

end IntervalBar.Diagram

end

end

end OAI
