import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.RestrictedMonoidal

namespace OAI

section
open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal
namespace InducedMonoidal

variable {C D : Type} [cC : Category.{0} C] [cD : Category.{0} D] [mC : MonoidalCategory C] [mD : MonoidalCategory D]
variable (F : C ⥤ D)
section
variable [F.Monoidal]
abbrev Cat := InducedCategory D F.obj
abbrev inclusion : Cat F ⥤ D := inducedFunctor F.obj
noncomputable instance monoidalStruct : MonoidalCategoryStruct (Cat F) where
  tensorObj X Y := @MonoidalCategoryStruct.tensorObj C cC mC.toMonoidalCategoryStruct X Y
  tensorUnit := 𝟙_ C
  tensorHom {X Y X' Y'} f g := InducedCategory.homMk (δ F X X' ≫ (f.hom ⊗ₘ g.hom) ≫ μ F Y Y')
  whiskerLeft X _ _ f := InducedCategory.homMk (δ F X _ ≫ (F.obj X ◁ f.hom) ≫ μ F X _)
  whiskerRight f Y := InducedCategory.homMk (δ F _ Y ≫ (f.hom ▷ F.obj Y) ≫ μ F _ Y)
  associator X Y Z := InducedCategory.isoMk (F.mapIso (@MonoidalCategoryStruct.associator C cC mC.toMonoidalCategoryStruct X Y Z))
  leftUnitor X := InducedCategory.isoMk (F.mapIso (@MonoidalCategoryStruct.leftUnitor C cC mC.toMonoidalCategoryStruct X))
  rightUnitor X := InducedCategory.isoMk (F.mapIso (@MonoidalCategoryStruct.rightUnitor C cC mC.toMonoidalCategoryStruct X))
noncomputable def data : Monoidal.InducingFunctorData (inclusion F) where
  μIso X Y := Functor.Monoidal.μIso F X Y
  εIso := Functor.Monoidal.εIso F
  whiskerLeft_eq := by intros; rfl
  whiskerRight_eq _ _ := rfl
  tensorHom_eq _ _ := rfl
  associator_eq X Y Z := by
    change F.map (@MonoidalCategoryStruct.associator C cC mC.toMonoidalCategoryStruct X Y Z).hom = _
    simpa only [inclusion,inducedFunctor, MonoidalCategoryStruct.tensorObj, MonoidalCategoryStruct.tensorUnit, monoidalStruct, Iso.trans_hom,Iso.symm_hom,tensorIso_hom,Iso.refl_hom,tensorHom_id,id_tensorHom,
      Functor.Monoidal.μIso_hom,Functor.Monoidal.μIso_inv,Category.assoc] using
      Functor.Monoidal.map_associator F X Y Z
  leftUnitor_eq X := by
    change F.map (@MonoidalCategoryStruct.leftUnitor C cC mC.toMonoidalCategoryStruct X).hom = _
    simpa only [inclusion,inducedFunctor, MonoidalCategoryStruct.tensorObj, MonoidalCategoryStruct.tensorUnit, monoidalStruct, Iso.trans_hom,Iso.symm_hom,tensorIso_hom,Iso.refl_hom,tensorHom_id,id_tensorHom,
      Functor.Monoidal.μIso_hom,Functor.Monoidal.μIso_inv,Functor.Monoidal.εIso_inv,Category.assoc] using
      Functor.Monoidal.map_leftUnitor F X
  rightUnitor_eq X := by
    change F.map (@MonoidalCategoryStruct.rightUnitor C cC mC.toMonoidalCategoryStruct X).hom = _
    simpa only [inclusion,inducedFunctor, MonoidalCategoryStruct.tensorObj, MonoidalCategoryStruct.tensorUnit, monoidalStruct, Iso.trans_hom,Iso.symm_hom,tensorIso_hom,Iso.refl_hom,tensorHom_id,id_tensorHom,
      Functor.Monoidal.μIso_hom,Functor.Monoidal.μIso_inv,Functor.Monoidal.εIso_inv,Category.assoc] using
      Functor.Monoidal.map_rightUnitor F X
noncomputable instance monoidal : MonoidalCategory (Cat F) := Monoidal.induced (inclusion F) (data F)
noncomputable instance inclusionMonoidal : (inclusion F).Monoidal := Monoidal.fromInducedMonoidal (inclusion F) (data F)
noncomputable def source : C ⥤ Cat F where
  obj X := X
  map f := InducedCategory.homMk (F.map f)
  map_id X := InducedCategory.hom_ext (F.map_id X)
  map_comp f g := InducedCategory.hom_ext (F.map_comp f g)
noncomputable instance sourceMonoidal : (source F).Monoidal := Functor.CoreMonoidal.toMonoidal {
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _
  μIso_hom_natural_left := by
    intros; apply InducedCategory.hom_ext
    change (δ F _ _ ≫ _ ▷ _ ≫ μ F _ _) ≫ 𝟙 _ = 𝟙 _ ≫ F.map (_ ▷ _)
    simp only [Category.id_comp,Category.comp_id]
    exact (Functor.Monoidal.map_whiskerRight F _ _).symm
  μIso_hom_natural_right := by
    intros; apply InducedCategory.hom_ext
    change (δ F _ _ ≫ _ ◁ _ ≫ μ F _ _) ≫ 𝟙 _ = 𝟙 _ ≫ F.map (_ ◁ _)
    simp only [Category.id_comp,Category.comp_id]
    exact (Functor.Monoidal.map_whiskerLeft F _ _).symm
  associativity := by
    intros; apply InducedCategory.hom_ext
    simp only [id_whiskerRight,whiskerLeft_id,source, InducedCategory.homMk_hom, Iso.refl_hom,
      Category.id_comp,Category.comp_id]
    rfl
  left_unitality := by
    intros; apply InducedCategory.hom_ext
    simp only [id_whiskerRight,source, InducedCategory.homMk_hom, Iso.refl_hom,
      Category.id_comp]
    rfl
  right_unitality := by
    intros; apply InducedCategory.hom_ext
    simp only [whiskerLeft_id,source, InducedCategory.homMk_hom, Iso.refl_hom,
      Category.id_comp]
    rfl }
end
section
variable [BraidedCategory C] [BraidedCategory D] [F.Braided]
noncomputable instance braided : BraidedCategory (Cat F) :=
  BraidedCategory.ofFaithful (inclusion F)
    (fun X Y => InducedCategory.isoMk (F.mapIso (@BraidedCategory.braiding C cC mC _ X Y))) (by
      intro X Y
      change μ F X Y ≫ F.map (@BraidedCategory.braiding C cC mC _ X Y).hom = (β_ _ _).hom ≫ μ F Y X
      exact Functor.LaxBraided.braided X Y)
noncomputable instance inclusionBraided : (inclusion F).Braided where
  braided X Y := by
    change μ F X Y ≫ F.map (@BraidedCategory.braiding C cC mC _ X Y).hom = (β_ _ _).hom ≫ μ F Y X
    exact Functor.LaxBraided.braided X Y
noncomputable instance sourceBraided : (source F).Braided where
  braided X Y := by
    apply InducedCategory.hom_ext
    change 𝟙 _ ≫ F.map (@BraidedCategory.braiding C cC mC _ X Y).hom = F.map (@BraidedCategory.braiding C cC mC _ X Y).hom ≫ 𝟙 _
    simp
end
variable [BraidedCategory C] [SymmetricCategory D] [F.Braided]
noncomputable instance symmetric : SymmetricCategory (Cat F) :=
  SymmetricCategory.ofFaithful (inclusion F)
end InducedMonoidal

end

open CategoryTheory MonoidalCategory
namespace RestrictedNerve
open IntervalBar IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable (I : Type) [Preorder I]
noncomputable instance posDiagramIsIso {X Y : PosDiagrams W I} (f : X ⟶ Y) : IsIso f := by
  refine ⟨⟨InducedCategory.homMk (inv f.hom),?_,?_⟩⟩
  · apply InducedCategory.hom_ext; exact IsIso.hom_inv_id f.hom
  · apply InducedCategory.hom_ext; exact IsIso.inv_hom_id f.hom
noncomputable instance posDiagramGroupoid : Groupoid (PosDiagrams W I) :=
  Groupoid.ofIsIso (fun _ => inferInstance)
noncomputable instance posDiagramMonoidal : MonoidalCategory (PosDiagrams W I) :=
  InducedMonoidal.monoidal (diagramInclusion W I)
noncomputable instance posDiagramBraided : BraidedCategory (PosDiagrams W I) :=
  InducedMonoidal.braided (diagramInclusion W I)
noncomputable instance posDiagramSymmetric : SymmetricCategory (PosDiagrams W I) :=
  InducedMonoidal.symmetric (diagramInclusion W I)
instance diagramPropertyInverse : Fact (diagramProperty W I).StableUnderInverse where
  out _ _ e h i j hij := by
    let he : _ ≅ _ := {
      hom := e.hom.hom.app i j hij
      inv := e.inv.hom.app i j hij
      hom_inv_id := congrArg (fun f => f.hom.app i j hij) e.hom_inv_id
      inv_hom_id := congrArg (fun f => f.hom.app i j hij) e.inv_hom_id }
    exact (Fact.out : W.StableUnderInverse) he (h i j hij)
open Functor.LaxMonoidal Functor.OplaxMonoidal
@[simp] lemma diagram_μ_app (A B : Diagram (WideSubcategory W) I) (i j : I) (h:i≤j) :
    (μ (diagramInclusion W I) A B).app i j h = 𝟙 _ := rfl
@[simp] lemma diagram_δ_app (A B : Diagram (WideSubcategory W) I) (i j : I) (h:i≤j) :
    (δ (diagramInclusion W I) A B).app i j h = 𝟙 _ := by
  change (CategoryTheory.inv (mapμHom (inclusion W) A B)).app i j h = 𝟙 _
  rw [inv_app]
  change CategoryTheory.inv (𝟙 _) = 𝟙 _
  simp
@[simp] lemma posTensor_app {A B A' B' : PosDiagrams W I} (f : A ⟶ B) (g : A' ⟶ B')
    (i j:I) (h:i≤j) : (f ⊗ₘ g).hom.app i j h = f.hom.app i j h ⊗ₘ g.hom.app i j h := by
  change (δ (diagramInclusion W I) A A' ≫ (f.hom ⊗ₘ g.hom) ≫ μ (diagramInclusion W I) B B').app i j h = _
  simp only [comp_app,diagram_δ_app,diagram_μ_app,tensor_app]
  erw [Category.id_comp, Category.comp_id]
@[simp] lemma posWhiskerLeft_app (A : PosDiagrams W I) {B D : PosDiagrams W I} (f : B ⟶ D)
    (i j:I) (h:i≤j) : (A ◁ f).hom.app i j h = ((diagramInclusion W I).obj A).obj i j h ◁ f.hom.app i j h := by
  change (δ (diagramInclusion W I) A B ≫ _ ◁ f.hom ≫ μ (diagramInclusion W I) A D).app i j h = _
  simp only [comp_app,diagram_δ_app,diagram_μ_app,whiskerLeft_app]
  erw [Category.id_comp, Category.comp_id]
@[simp] lemma posWhiskerRight_app {A B : PosDiagrams W I} (f : A ⟶ B) (D : PosDiagrams W I)
    (i j:I) (h:i≤j) : (f ▷ D).hom.app i j h = f.hom.app i j h ▷ ((diagramInclusion W I).obj D).obj i j h := by
  change (δ (diagramInclusion W I) A D ≫ f.hom ▷ _ ≫ μ (diagramInclusion W I) B D).app i j h = _
  simp only [comp_app,diagram_δ_app,diagram_μ_app,whiskerRight_app]
  erw [Category.id_comp, Category.comp_id]
@[simp] lemma posAssoc_app (A B D : PosDiagrams W I) (i j:I) (h:i≤j) :
    (α_ A B D).hom.hom.app i j h =
      (α_ ((diagramInclusion W I).obj A |>.obj i j h)
        ((diagramInclusion W I).obj B |>.obj i j h) ((diagramInclusion W I).obj D |>.obj i j h)).hom := rfl
@[simp] lemma posLeft_app (A : PosDiagrams W I) (i j:I) (h:i≤j) :
    (λ_ A).hom.hom.app i j h = (λ_ ((diagramInclusion W I).obj A |>.obj i j h)).hom := rfl
@[simp] lemma posRight_app (A : PosDiagrams W I) (i j:I) (h:i≤j) :
    (ρ_ A).hom.hom.app i j h = (ρ_ ((diagramInclusion W I).obj A |>.obj i j h)).hom := rfl
@[simp] lemma posBraiding_app (A B : PosDiagrams W I) (i j:I) (h:i≤j) :
    (β_ A B).hom.hom.app i j h =
      (β_ ((diagramInclusion W I).obj A |>.obj i j h) ((diagramInclusion W I).obj B |>.obj i j h)).hom := rfl
instance diagramPropertyMonoidal : (diagramProperty W I).IsMonoidalStable where
  whiskerLeft A _ _ f hf i j h := by
    change W ((δ (diagramInclusion W I) A _ ≫ _ ◁ f.hom ≫ μ (diagramInclusion W I) A _).app i j h)
    simp only [comp_app,whiskerLeft_app,diagram_δ_app,diagram_μ_app]
    erw [Category.id_comp, Category.comp_id]
    exact W.whiskerLeft_mem _ _ (hf i j h)
  whiskerRight f hf B i j h := by
    change W ((δ (diagramInclusion W I) _ B ≫ f.hom ▷ _ ≫ μ (diagramInclusion W I) _ B).app i j h)
    simp only [comp_app,whiskerRight_app,diagram_δ_app,diagram_μ_app]
    erw [Category.id_comp, Category.comp_id]
    exact W.whiskerRight_mem _ (hf i j h) _
  associator_hom_mem first second third lower upper bound := W.associator_hom_mem
    (((diagramInclusion W I).obj first).obj lower upper bound)
    (((diagramInclusion W I).obj second).obj lower upper bound)
    (((diagramInclusion W I).obj third).obj lower upper bound)
  associator_inv_mem first second third :=
    (Fact.out : (diagramProperty W I).StableUnderInverse) (α_ first second third)
      (fun lower upper bound => W.associator_hom_mem
        (((diagramInclusion W I).obj first).obj lower upper bound)
        (((diagramInclusion W I).obj second).obj lower upper bound)
        (((diagramInclusion W I).obj third).obj lower upper bound))
  leftUnitor_hom_mem diagram lower upper bound := W.leftUnitor_hom_mem
    (((diagramInclusion W I).obj diagram).obj lower upper bound)
  leftUnitor_inv_mem diagram :=
    (Fact.out : (diagramProperty W I).StableUnderInverse) (λ_ diagram)
      (fun lower upper bound => W.leftUnitor_hom_mem
        (((diagramInclusion W I).obj diagram).obj lower upper bound))
  rightUnitor_hom_mem diagram lower upper bound := W.rightUnitor_hom_mem
    (((diagramInclusion W I).obj diagram).obj lower upper bound)
  rightUnitor_inv_mem diagram :=
    (Fact.out : (diagramProperty W I).StableUnderInverse) (ρ_ diagram)
      (fun lower upper bound => W.rightUnitor_hom_mem
        (((diagramInclusion W I).obj diagram).obj lower upper bound))
instance diagramPropertyBraided : (diagramProperty W I).IsStableUnderBraiding where
  braiding_hom_mem first second lower upper bound := W.braiding_hom_mem
    (((diagramInclusion W I).obj first).obj lower upper bound)
    (((diagramInclusion W I).obj second).obj lower upper bound)
  braiding_inv_mem first second :=
    (Fact.out : (diagramProperty W I).StableUnderInverse) (β_ first second)
      (fun lower upper bound => W.braiding_hom_mem
        (((diagramInclusion W I).obj first).obj lower upper bound)
        (((diagramInclusion W I).obj second).obj lower upper bound))
end RestrictedNerve

end OAI
