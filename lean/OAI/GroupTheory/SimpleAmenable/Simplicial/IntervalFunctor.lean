import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.IntervalTensor

namespace OAI

section

open CategoryTheory MonoidalCategory BraidedCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe u v u' v' w
namespace IntervalBar.Diagram

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {D : Type u'} [Groupoid.{v'} D] [MonoidalCategory D] [SymmetricCategory D]
variable {I : Type w} [Preorder I]
noncomputable instance reindexMonoidal {J : Type w} [Preorder J] (f : I →o J) :
    (reindex (C:=C) f).Monoidal := Functor.CoreMonoidal.toMonoidal {
  εIso := Iso.refl _
  μIso A B := Iso.refl _
  μIso_hom_natural_left := by
    intro X Y g X'
    apply Hom.ext
    intro i j h
    have hf : f i ≤ f j := f.monotone h
    change (g.app (f i) (f j) hf ⊗ₘ 𝟙 (X'.obj (f i) (f j) hf)) ≫ 𝟙 _ =
      𝟙 _ ≫ (g.app (f i) (f j) hf ⊗ₘ 𝟙 (X'.obj (f i) (f j) hf))
    simp
  μIso_hom_natural_right := by
    intro X Y X' g
    apply Hom.ext
    intro i j h
    have hf : f i ≤ f j := f.monotone h
    change (𝟙 (X'.obj (f i) (f j) hf) ⊗ₘ g.app (f i) (f j) hf) ≫ 𝟙 _ =
      𝟙 _ ≫ (𝟙 (X'.obj (f i) (f j) hf) ⊗ₘ g.app (f i) (f j) hf)
    simp
  associativity := by
    intro X Y Z
    apply Hom.ext
    intro i j h
    have hf : f i ≤ f j := f.monotone h
    let x := X.obj (f i) (f j) hf
    let y := Y.obj (f i) (f j) hf
    let z := Z.obj (f i) (f j) hf
    change (𝟙 (x ⊗ y) ⊗ₘ 𝟙 z) ≫ 𝟙 _ ≫ (α_ x y z).hom =
      (α_ x y z).hom ≫ (𝟙 x ⊗ₘ 𝟙 (y ⊗ z)) ≫ 𝟙 _
    simp
  left_unitality := by
    intro X
    apply Hom.ext
    intro i j h
    have hf : f i ≤ f j := f.monotone h
    let x := X.obj (f i) (f j) hf
    change (λ_ x).hom = (𝟙 (𝟙_ C) ⊗ₘ 𝟙 x) ≫ 𝟙 _ ≫ (λ_ x).hom
    simp
  right_unitality := by
    intro X
    apply Hom.ext
    intro i j h
    have hf : f i ≤ f j := f.monotone h
    let x := X.obj (f i) (f j) hf
    change (ρ_ x).hom = (𝟙 x ⊗ₘ 𝟙 (𝟙_ C)) ≫ 𝟙 _ ≫ (ρ_ x).hom
    simp }


noncomputable def mapεHom (F : C ⥤ D) [F.Monoidal] :
    (𝟙_ (Diagram D I)) ⟶ (map F).obj (𝟙_ (Diagram C I)) where
  app _ _ _ := ε F
  unit i := by
    change ε F ≫ (F.map (𝟙 _) ≫ η F) = 𝟙 _
    simp
  cut i j k hij hjk := by
    change (ε F ⊗ₘ ε F) ≫ (μ F _ _ ≫ F.map (λ_ _).hom) = (λ_ _).hom ≫ ε F
    rw [←Category.assoc,ε_tensorHom_comp_μ]
    simp

noncomputable def mapμHom (F : C ⥤ D) [F.Braided]
    (A B : Diagram C I) : (map F).obj A ⊗ (map F).obj B ⟶ (map F).obj (A⊗B) where
  app i j h := μ F (A.obj i j h) (B.obj i j h)
  unit i := by
    change μ F _ _ ≫ (F.map (((A.unit i).hom ⊗ₘ (B.unit i).hom) ≫ (λ_ _).hom) ≫ η F) =
      ((F.map (A.unit i).hom ≫ η F) ⊗ₘ (F.map (B.unit i).hom ≫ η F)) ≫ (λ_ _).hom
    rw [F.map_comp]
    simp only [Category.assoc]
    rw [←μ_natural_assoc,Functor.Monoidal.map_leftUnitor]
    simp only [Category.assoc,Functor.Monoidal.μ_δ_assoc]
    rw [←leftUnitor_naturality,←tensorHom_comp_tensorHom]
    simp [MonoidalCategory.tensorHom_def]
  cut i j k hij hjk := by
    change (μ F _ _ ⊗ₘ μ F _ _) ≫ (μ F _ _ ≫ F.map
      (tensorμ _ _ _ _ ≫ ((A.cut i j k hij hjk).hom ⊗ₘ (B.cut i j k hij hjk).hom))) =
      (tensorμ _ _ _ _ ≫ ((μ F _ _ ≫ F.map (A.cut i j k hij hjk).hom) ⊗ₘ
        (μ F _ _ ≫ F.map (B.cut i j k hij hjk).hom))) ≫ μ F _ _
    simp only [F.map_comp,←tensorHom_comp_tensorHom,Category.assoc]
    rw [←tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc,←μ_natural]

noncomputable instance mapMonoidal (F : C ⥤ D) [F.Braided] :
    (map (I:=I) F).Monoidal := Functor.CoreMonoidal.toMonoidal {
  εIso := asIso (mapεHom F)
  μIso A B := asIso (mapμHom F A B)
  μIso_hom_natural_left := by
    intros; apply Hom.ext; intro i j h
    simp [map,mapObj,mapμHom]
  μIso_hom_natural_right := by
    intros; apply Hom.ext; intro i j h
    simp [map,mapObj,mapμHom]
  associativity := by
    intros; apply Hom.ext; intro i j h
    simp [map,mapObj,mapμHom]
  left_unitality := by
    intros; apply Hom.ext; intro i j h
    simp [map,mapObj,mapμHom,mapεHom]
  right_unitality := by
    intros; apply Hom.ext; intro i j h
    simp [map,mapObj,mapμHom,mapεHom] }

noncomputable instance reindexBraided {J : Type w} [Preorder J] (f : I →o J) :
    (reindex (C:=C) f).Braided where
  braided A B := by
    apply Hom.ext; intro i j h
    change 𝟙 _ ≫ (β_ _ _).hom = (β_ _ _).hom ≫ 𝟙 _
    simp

noncomputable instance mapBraided (F : C ⥤ D) [F.Braided] : (map (I:=I) F).Braided where
  braided A B := by
    apply Hom.ext; intro i j h
    change μ F _ _ ≫ F.map (β_ _ _).hom = (β_ _ _).hom ≫ μ F _ _
    exact Functor.LaxBraided.braided (F:=F) _ _

noncomputable instance evalBraided (n : ℕ) : (eval (C:=C) n).Braided where
  braided A B := by
    funext i
    change 𝟙 _ ≫ (β_ _ _).hom = (β_ _ _).hom ≫ 𝟙 _
    simp

end IntervalBar.Diagram

end

open CategoryTheory MonoidalCategory BraidedCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe u v u' v' u'' v'' w
namespace IntervalBar.Diagram

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C]
variable {D : Type u'} [Groupoid.{v'} D] [MonoidalCategory D]
variable {E : Type u''} [Groupoid.{v''} E] [MonoidalCategory E]
variable {I : Type w} [Preorder I]

lemma ext_heq {A B : Diagram C I} (hobj : A.obj=B.obj)
    (hunit : HEq A.unit B.unit) (hcut : HEq A.cut B.cut) : A=B := by
  cases A; cases B; cases hobj; cases hunit; cases hcut; rfl

@[simp] lemma eqToHom_app {A B : Diagram C I} (h : A=B) (i j : I) (hij : i≤j) :
    (eqToHom h).app i j hij=eqToHom (congrArg (fun X : Diagram C I => X.obj i j hij) h) := by
  cases h; rfl

@[simp] lemma mapObj_id (A : Diagram C I) : mapObj (𝟭 C) A=A := by
  refine ext_heq ?_ ?_ ?_
  · rfl
  · apply heq_of_eq
    funext i
    apply Iso.ext
    simp [mapObj]
  · apply heq_of_eq
    funext i j k hij hjk
    apply Iso.ext
    simp [mapObj]
@[simp] lemma map_id : map (I:=I) (𝟭 C)=𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun A => mapObj_id A) ?_
  intro A B f
  apply Hom.ext; intro i j h
  erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
  simp [map]
  change f.app i j h = 𝟙 _ ≫ f.app i j h ≫ 𝟙 _
  simp

@[simp] lemma mapObj_comp (F : C ⥤ D) (G : D ⥤ E) [F.Monoidal] [G.Monoidal]
    (A : Diagram C I) : mapObj (F⋙G) A=mapObj G (mapObj F A) := by
  refine ext_heq ?_ ?_ ?_
  · rfl
  · apply heq_of_eq
    funext i
    apply Iso.ext
    simp [mapObj]
  · apply heq_of_eq
    funext i j k hij hjk
    apply Iso.ext
    simp [mapObj,Category.assoc]
@[simp] lemma map_comp (F : C ⥤ D) (G : D ⥤ E) [F.Monoidal] [G.Monoidal] :
    map (I:=I) (F⋙G)=map F ⋙ map G := by
  refine CategoryTheory.Functor.ext (fun A => mapObj_comp F G A) ?_
  intro A B f
  apply Hom.ext; intro i j h
  erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
  simp [map]
  change G.map (F.map (f.app i j h)) =
    𝟙 _ ≫ G.map (F.map (f.app i j h)) ≫ 𝟙 _
  simp

variable {J : Type w} [Preorder J]
@[simp] lemma reindex_map (F : C ⥤ D) [F.Monoidal] (f : I →o J) :
    reindex (C:=C) f ⋙ map F = map F ⋙ reindex f := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro A B g
  apply Hom.ext
  intro i j h
  change F.map (g.app (f i) (f j) (f.monotone h)) =
    𝟙 _ ≫ F.map (g.app (f i) (f j) (f.monotone h)) ≫ 𝟙 _
  simp

end IntervalBar.Diagram

end OAI
