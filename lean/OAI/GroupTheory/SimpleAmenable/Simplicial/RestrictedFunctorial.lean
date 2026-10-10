import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.RestrictedMonoidalTranspose

namespace OAI

namespace RestrictedNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory SimplicialObject Simplicial Opposite

section

variable {C D:Type} [Groupoid.{0} C] [Groupoid.{0} D]
  (W:MorphismProperty C) (V:MorphismProperty D) [W.IsMultiplicative] [V.IsMultiplicative]
  (F:C⥤D) (hF:∀{X Y:C} (f:X⟶Y),W f→V (F.map f))
def stringsMap (n:ℕ) : Strings W n ⥤ Strings V n where
  obj A := ⟨A.obj⋙F⟩
  map f := ⟨Functor.whiskerRight f.hom F,fun i=>hF _ (f.property i)⟩
  map_id _ := by apply WideSubcategory.hom_ext; ext i; exact F.map_id _
  map_comp _ _ := by apply WideSubcategory.hom_ext; ext i; exact F.map_comp _ _
def verticalMap (n:ℕ) : Vertical W n ⥤ Vertical V n where
  obj A := ⟨A.obj⋙F,fun i j f=>hF _ (A.property i j f)⟩
  map f := ObjectProperty.homMk (Functor.whiskerRight f.hom F)
  map_id _ := by apply ObjectProperty.hom_ext; ext i; exact F.map_id _
  map_comp _ _ := by apply ObjectProperty.hom_ext; ext i; exact F.map_comp _ _
def horizontalMap : horizontal W ⟶ horizontal V where
  app p := (stringsMap W V F hF p.unop.len).toCatHom
  naturality _ _ f := by
    apply Cat.ext
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro source target arrow
    erw [Category.id_comp, Category.comp_id]
    apply WideSubcategory.hom_ext; ext index; rfl
def verticalMapNat : vertical W ⟶ vertical V where
  app p := (verticalMap W V F hF p.unop.len).toCatHom
  naturality _ _ f := by
    apply Cat.ext
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro source target arrow
    erw [Category.id_comp, Category.comp_id]
    apply ObjectProperty.hom_ext; ext index; rfl
lemma diagonalIso_natural :
    SimplicialDiagonal.nerveDiagonal.map (horizontalMap W V F hF) ≫ (diagonalIso V).hom =
      (diagonalIso W).hom ≫ SimplicialDiagonal.nerveDiagonal.map (verticalMapNat W V F hF) := by
  ext p x
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro source target arrow
  erw [Category.id_comp, Category.comp_id]
  apply ObjectProperty.hom_ext; ext index; rfl
omit [W.IsMultiplicative] in
@[simp] lemma eqToHom_vertical_app {n:ℕ} {A B:Vertical W n} (e:A=B) (i:Fin (n+1)) :
    (eqToHom e).hom.app i=eqToHom (congrArg (fun A:Vertical W n=>A.obj.obj i) e) := by
  cases e; rfl
lemma constantMap_natural :
    (Functor.const SimplexCategoryᵒᵖ).map F.toCatHom ≫ constantMap V =
      constantMap W ≫ verticalMapNat W V F hF := by
  apply NatTrans.ext; funext p; apply Cat.ext
  refine CategoryTheory.Functor.ext (fun A=>?_) ?_
  · apply ObjectProperty.FullSubcategory.ext
    refine CategoryTheory.Functor.ext (fun i=>?_) ?_
    · rfl
    · intro i j f
      change (𝟙 (F.obj A)) = 𝟙 _ ≫ F.map (𝟙 A) ≫ 𝟙 _
      rw [F.map_id, Category.id_comp, Category.comp_id]
  · intro A B f
    apply ObjectProperty.hom_ext
    apply NatTrans.ext; funext i
    change F.map f =
      (eqToHom _ : (constant V p.unop.len).obj (F.obj A) ⟶
        (verticalMap W V F hF p.unop.len).obj ((constant W p.unop.len).obj A)).hom.app i ≫
      F.map f ≫
      (eqToHom _ : (verticalMap W V F hF p.unop.len).obj ((constant W p.unop.len).obj B) ⟶
        (constant V p.unop.len).obj (F.obj B)).hom.app i
    erw [eqToHom_vertical_app, eqToHom_vertical_app, Category.id_comp]
    change F.map f = F.map f ≫ 𝟙 (F.obj B)
    exact (Category.comp_id _).symm
lemma constantDiagonalIso_natural :
    SimplicialDiagonal.nerveDiagonal.map ((Functor.const SimplexCategoryᵒᵖ).map F.toCatHom) ≫
      (constantDiagonalIso (C:=D)).hom =
      (constantDiagonalIso (C:=C)).hom ≫ nerveMap F := by
  ext p x; rfl
end

variable {C D:Type} [Groupoid.{0} C] [Groupoid.{0} D]
  (W:MorphismProperty C) (V:MorphismProperty D) [W.IsMultiplicative] [V.IsMultiplicative]
  (F:C⥤D) (hF:∀{X Y:C} (f:X⟶Y),W f→V (F.map f))

lemma homologyIso_natural (j:ℕ) :
    SSet.homologyMap (SimplicialDiagonal.nerveDiagonal.map (horizontalMap W V F hF))
      DiagonalResolution.Z j ≫ (homologyIso V j).hom =
    (homologyIso W j).hom ≫ SSet.homologyMap (nerveMap F) DiagonalResolution.Z j := by
  let H := SSet.homologyFunctor DiagonalResolution.Z j
  let N := SimplicialDiagonal.nerveDiagonal
  have : IsIso (H.map (N.map (constantMap W))) :=
    SimplicialDiagonal.nerveDiagonal_isIso (constantMap W)
      (fun p=>inferInstanceAs (constant W p.unop.len).IsEquivalence) j
  have : IsIso (H.map (N.map (constantMap V))) :=
    SimplicialDiagonal.nerveDiagonal_isIso (constantMap V)
      (fun p=>inferInstanceAs (constant V p.unop.len).IsEquivalence) j
  have h₁ := congrArg H.map (diagonalIso_natural W V F hF)
  simp only [Functor.map_comp] at h₁
  have h₂ := congrArg (fun f=>H.map (N.map f)) (constantMap_natural W V F hF)
  simp only [Functor.map_comp] at h₂
  have h₃ := congrArg H.map (constantDiagonalIso_natural F)
  simp only [Functor.map_comp] at h₃
  have hc : H.map (N.map (verticalMapNat W V F hF)) ≫
      inv (H.map (N.map (constantMap V))) =
      inv (H.map (N.map (constantMap W))) ≫
      H.map (N.map ((Functor.const SimplexCategoryᵒᵖ).map F.toCatHom)) := by
    apply (IsIso.eq_inv_comp _).mpr
    rw [←Category.assoc,←h₂,Category.assoc,IsIso.hom_inv_id,Category.comp_id]
  change H.map (N.map (horizontalMap W V F hF)) ≫
    (H.map (diagonalIso V).hom ≫ inv (H.map (N.map (constantMap V))) ≫
      H.map (constantDiagonalIso (C:=D)).hom) =
    (H.map (diagonalIso W).hom ≫ inv (H.map (N.map (constantMap W))) ≫
      H.map (constantDiagonalIso (C:=C)).hom) ≫ H.map (nerveMap F)
  rw [←Category.assoc _ (H.map (diagonalIso V).hom),h₁]
  simp only [Category.assoc]
  rw [←Category.assoc (H.map (N.map (verticalMapNat W V F hF))),hc]
  simp only [Category.assoc]
  rw [h₃]
end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I J K:Type} [Preorder I] [Preorder J] [Preorder K]

noncomputable def posReindex (u:I→oJ) : PosDiagrams W J ⥤ PosDiagrams W I where
  obj A := (Diagram.reindex (C:=WideSubcategory W) u).obj A
  map f := InducedCategory.homMk {
    app i j h := f.hom.app (u i) (u j) (u.monotone h)
    unit i := f.hom.unit (u i)
    cut i j k hij hjk := f.hom.cut (u i) (u j) (u k) (u.monotone hij) (u.monotone hjk) }
lemma posReindex_property (u:I→oJ) {A B:PosDiagrams W J} (f:A⟶B)
    (hf:diagramProperty W J f) : diagramProperty W I ((posReindex W u).map f) :=
  fun i j h=>hf (u i) (u j) (u.monotone h)
lemma posReindex_inclusion (u:I→oJ) :
    posReindex W u ⋙ posDiagramInclusion W I =
      posDiagramInclusion W J ⋙ Diagram.reindex u := by
  refine CategoryTheory.Functor.ext (fun A=>rfl) ?_
  intro A B f
  erw [Category.id_comp, Category.comp_id]
  rfl
lemma posReindex_id : posReindex W (OrderHom.id (α:=I))=𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun A=>?_) ?_
  · cases A; rfl
  · intro A B f
    erw [Category.id_comp, Category.comp_id]
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h; rfl
lemma posReindex_comp (u:I→oJ) (v:J→oK) :
    posReindex W (v.comp u)=posReindex W v ⋙ posReindex W u := by
  refine CategoryTheory.Functor.ext (fun A=>rfl) ?_
  intro A B f
  erw [Category.id_comp, Category.comp_id]
  rfl
lemma transpose_posReindex (u:I→oJ) (n:ℕ) :
    Diagram.reindex (C:=Strings W n) u ⋙ transposeDiagram (I:=I) W n =
      transposeDiagram (I:=J) W n ⋙ stringsMap (diagramProperty W J) (diagramProperty W I)
        (posReindex W u) (posReindex_property W u) n := by
  refine CategoryTheory.Functor.ext (fun A=>?_) ?_
  · apply WideSubcategory.ext
    refine CategoryTheory.Functor.ext (fun i=>rfl) ?_
    intro i j f
    erw [Category.id_comp, Category.comp_id]
    rfl
  · intro A B f
    erw [Category.id_comp, Category.comp_id]
    rfl
end

end RestrictedNerve

end OAI
