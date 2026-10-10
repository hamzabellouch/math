import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.RestrictedFunctorial

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I J:Type} [Preorder I] [Preorder J]
noncomputable def diagramHorizontalReindex (u:I→oJ) :
    diagramHorizontal (I:=J) W ⟶ diagramHorizontal (I:=I) W where
  app n := (Diagram.reindex (C:=Strings W n.unop.len) u).toCatHom
  naturality p q f := by
    apply Cat.ext
    exact (Diagram.reindex_map (reindex W f.unop.toOrderHom.toFunctor) u).symm
lemma diagramTranspose_posReindex (u:I→oJ) :
    diagramHorizontalReindex W u ≫ diagramTranspose (I:=I) W =
      diagramTranspose (I:=J) W ≫ horizontalMap (diagramProperty W J) (diagramProperty W I)
        (posReindex W u) (posReindex_property W u) := by
  apply NatTrans.ext; funext n; apply Cat.ext
  exact transpose_posReindex W u n.unop.len
private lemma compose_three_squares {D : Type*} [Category D]
    {X₀ X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ : D}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₀ ⟶ Y₁) (d : Y₁ ⟶ X₂)
    (e : X₂ ⟶ X₃) (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ X₃) (h : X₃ ⟶ X₄)
    (i : Y₂ ⟶ Y₃) (j : Y₃ ⟶ X₄)
    (h₁ : a ≫ b = c ≫ d) (h₂ : d ≫ e = f ≫ g) (h₃ : g ≫ h = i ≫ j) :
    a ≫ (b ≫ e ≫ h) = (c ≫ f ≫ i) ≫ j := by
  rw [← Category.assoc a b, h₁]
  simp only [Category.assoc]
  rw [← Category.assoc d e, h₂]
  simp only [Category.assoc]
  rw [h₃]

lemma diagramResolutionHomologyIso_natural {p q:ℕ}
    (u:Fin (p+1)→oFin (q+1)) (j:ℕ) :
    SSet.homologyMap (SimplicialDiagonal.nerveDiagonal.map (diagramHorizontalReindex W u))
      DiagonalResolution.Z j ≫ (diagramResolutionHomologyIso W p j).hom =
      (diagramResolutionHomologyIso W q j).hom ≫
        SSet.homologyMap (nerveMap (Diagram.reindex (C:=C) u)) DiagonalResolution.Z j := by
  let H := SSet.homologyFunctor DiagonalResolution.Z j
  let N := SimplicialDiagonal.nerveDiagonal
  have ht := congrArg (fun f=>H.map (N.map f)) (diagramTranspose_posReindex W u)
  simp only [Functor.map_comp] at ht
  have hr := homologyIso_natural (diagramProperty W (Fin (q+1))) (diagramProperty W (Fin (p+1)))
    (posReindex W u) (posReindex_property W u) j
  change H.map (N.map (horizontalMap (diagramProperty W (Fin (q+1))) (diagramProperty W (Fin (p+1)))
    (posReindex W u) (posReindex_property W u))) ≫ (homologyIso (diagramProperty W (Fin (p+1))) j).hom =
      (homologyIso (diagramProperty W (Fin (q+1))) j).hom ≫ H.map (nerveMap (posReindex W u)) at hr
  have he : nerveMap (posReindex W u) ≫ nerveMap (posDiagramInclusion W (Fin (p+1))) =
      nerveMap (posDiagramInclusion W (Fin (q+1))) ≫ nerveMap (Diagram.reindex (C:=C) u) := by
    change nerveMap (posReindex W u ⋙ posDiagramInclusion W (Fin (p+1))) =
      nerveMap (posDiagramInclusion W (Fin (q+1)) ⋙ Diagram.reindex u)
    rw [posReindex_inclusion]
  have hi := congrArg H.map he
  simp only [Functor.map_comp] at hi
  change H.map (N.map (diagramHorizontalReindex W u)) ≫
    (H.map (N.map (diagramTranspose (I:=Fin (p+1)) W)) ≫
      (homologyIso (diagramProperty W (Fin (p+1))) j).hom ≫
      H.map (nerveMap (posDiagramInclusion W (Fin (p+1))))) =
    (H.map (N.map (diagramTranspose (I:=Fin (q+1)) W)) ≫
      (homologyIso (diagramProperty W (Fin (q+1))) j).hom ≫
      H.map (nerveMap (posDiagramInclusion W (Fin (q+1))))) ≫
        H.map (nerveMap (Diagram.reindex (C:=C) u))
  exact compose_three_squares _ _ _ _ _ _ _ _ _ _ ht hr hi

noncomputable instance posReindexMonoidal (u:I→oJ) : (posReindex W u).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso _ _ := Iso.refl _
    μIso_hom_natural_left := by
      intros
      simp only [Iso.refl_hom]
      repeat' first | erw [id_whiskerRight] | erw [whiskerLeft_id] | erw [Category.comp_id] | erw [Category.id_comp]
      apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
      simp [posReindex,posWhiskerRight_app]
      rfl
    μIso_hom_natural_right := by
      intros
      simp only [Iso.refl_hom]
      repeat' first | erw [id_whiskerRight] | erw [whiskerLeft_id] | erw [Category.comp_id] | erw [Category.id_comp]
      apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
      simp [posReindex,posWhiskerLeft_app]
      rfl
    associativity := by
      intros
      simp only [Iso.refl_hom]
      repeat' first | erw [id_whiskerRight] | erw [whiskerLeft_id] | erw [Category.comp_id] | erw [Category.id_comp]
      apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
      rfl
    left_unitality := by
      intros
      simp only [Iso.refl_hom]
      repeat' first | erw [id_whiskerRight] | erw [whiskerLeft_id] | erw [Category.comp_id] | erw [Category.id_comp]
      apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
      rfl
    right_unitality := by
      intros
      simp only [Iso.refl_hom]
      repeat' first | erw [id_whiskerRight] | erw [whiskerLeft_id] | erw [Category.comp_id] | erw [Category.id_comp]
      apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
      rfl }
noncomputable instance posReindexBraided (u:I→oJ) : (posReindex W u).Braided where
  braided A B := by
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    change 𝟙 _ ≫ (β_ _ _).hom = (β_ _ _).hom ≫ 𝟙 _
    simp
noncomputable def widePosReindex (u:I→oJ) :
    WideSubcategory (diagramProperty W J) ⥤ WideSubcategory (diagramProperty W I) where
  obj A := ⟨(posReindex W u).obj A.obj⟩
  map f := ⟨(posReindex W u).map f.hom,posReindex_property W u f.hom f.property⟩
  map_id A := by apply WideSubcategory.hom_ext; exact (posReindex W u).map_id _
  map_comp f g := by apply WideSubcategory.hom_ext; exact (posReindex W u).map_comp _ _
noncomputable instance widePosReindexMonoidal (u:I→oJ) : (widePosReindex W u).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso _ _ := Iso.refl _
    μIso_hom_natural_left := by
      intros
      simp only [Iso.refl_hom]
      repeat' first | erw [id_whiskerRight] | erw [whiskerLeft_id] | erw [Category.comp_id] | erw [Category.id_comp]
      apply WideSubcategory.hom_ext; apply InducedCategory.hom_ext
      apply Hom.ext; intro i j h
      simp [widePosReindex,posReindex,posWhiskerRight_app]
      rfl
    μIso_hom_natural_right := by
      intros
      simp only [Iso.refl_hom]
      repeat' first | erw [id_whiskerRight] | erw [whiskerLeft_id] | erw [Category.comp_id] | erw [Category.id_comp]
      apply WideSubcategory.hom_ext; apply InducedCategory.hom_ext
      apply Hom.ext; intro i j h
      simp [widePosReindex,posReindex,posWhiskerLeft_app]
      rfl
    associativity := by
      intros
      simp only [Iso.refl_hom]
      repeat' first | erw [id_whiskerRight] | erw [whiskerLeft_id] | erw [Category.comp_id] | erw [Category.id_comp]
      apply WideSubcategory.hom_ext; apply InducedCategory.hom_ext
      apply Hom.ext; intro i j h; rfl
    left_unitality := by
      intros
      simp only [Iso.refl_hom]
      repeat' first | erw [id_whiskerRight] | erw [whiskerLeft_id] | erw [Category.comp_id] | erw [Category.id_comp]
      apply WideSubcategory.hom_ext; apply InducedCategory.hom_ext
      apply Hom.ext; intro i j h; rfl
    right_unitality := by
      intros
      simp only [Iso.refl_hom]
      repeat' first | erw [id_whiskerRight] | erw [whiskerLeft_id] | erw [Category.comp_id] | erw [Category.id_comp]
      apply WideSubcategory.hom_ext; apply InducedCategory.hom_ext
      apply Hom.ext; intro i j h; rfl }
noncomputable instance widePosReindexBraided (u:I→oJ) : (widePosReindex W u).Braided where
  braided A B := by
    apply WideSubcategory.hom_ext; apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    change 𝟙 _ ≫ (β_ _ _).hom = (β_ _ _).hom ≫ 𝟙 _
    simp
end RestrictedNerve

end OAI
