import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.PositionalInclusionMonoidal

namespace OAI

namespace RestrictedNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory SimplicialObject Simplicial Opposite

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C) [W.IsMultiplicative]

def verticalDiagonalFunctor {n:ℕ} (F:Fin (n+1)⥤Vertical W n) : Fin (n+1)⥤C where
  obj i := (F.obj i).obj.obj i
  map {i j} f := (F.map f).hom.app i ≫ (F.obj j).obj.map f
  map_id _ := by simp
  map_comp {i j k} f g := by
    have hn := (F.map g).hom.naturality f
    simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
    simp only [Category.assoc]
    rw [←Category.assoc ((F.map g).hom.app i),←hn]
    simp only [Category.assoc]
def verticalAugmentation : SimplicialDiagonal.nerveDiagonal.obj (vertical W) ⟶ nerve C where
  app _ := ↾(verticalDiagonalFunctor W)
  naturality _ _ _ := by
    ext F
    refine CategoryTheory.Functor.ext (fun _=>rfl) ?_
    intro i j g
    erw [Category.id_comp, Category.comp_id]
    rfl
lemma constantMap_verticalAugmentation :
    SimplicialDiagonal.nerveDiagonal.map (constantMap W) ≫ verticalAugmentation W =
      (constantDiagonalIso (C:=C)).hom := by
  ext n F
  refine CategoryTheory.Functor.ext (fun _=>rfl) ?_
  intro i j f
  erw [Category.id_comp, Category.comp_id]
  change F.map f ≫ 𝟙 _ = F.map f
  simp

noncomputable def resolutionAugmentation :
    SimplicialDiagonal.nerveDiagonal.obj (horizontal W) ⟶ nerve C :=
  (diagonalIso W).hom ≫ verticalAugmentation W
lemma resolutionAugmentation_homology (j:ℕ) :
    SSet.homologyMap (resolutionAugmentation W) DiagonalResolution.Z j = (homologyIso W j).hom := by
  let H := SSet.homologyFunctor DiagonalResolution.Z j
  let N := SimplicialDiagonal.nerveDiagonal
  have constantMap_isIso : IsIso (H.map (N.map (constantMap W))) :=
    SimplicialDiagonal.nerveDiagonal_isIso (constantMap W)
      (fun p=>inferInstanceAs (constant W p.unop.len).IsEquivalence) j
  have hc := congrArg H.map (constantMap_verticalAugmentation W)
  simp only [Functor.map_comp] at hc
  have hv : H.map (verticalAugmentation W) = inv (H.map (N.map (constantMap W))) ≫
      H.map (constantDiagonalIso (C:=C)).hom := by
    rw [←hc,←Category.assoc,IsIso.inv_hom_id,Category.id_comp]
  change H.map ((diagonalIso W).hom ≫ verticalAugmentation W) =
    H.map (diagonalIso W).hom ≫ inv (H.map (N.map (constantMap W))) ≫ H.map (constantDiagonalIso (C:=C)).hom
  rw [Functor.map_comp,hv]
noncomputable instance resolutionAugmentation_isIso (j:ℕ) :
    IsIso (SSet.homologyMap (resolutionAugmentation W) DiagonalResolution.Z j) := by
  rw [resolutionAugmentation_homology]
  infer_instance
variable {D:Type} [Groupoid.{0} D] (V:MorphismProperty D) [V.IsMultiplicative]
  (F:C⥤D) (hF:∀{X Y:C} (f:X⟶Y),W f→V (F.map f))
omit [W.IsMultiplicative] [V.IsMultiplicative] in
lemma verticalAugmentation_natural :
    SimplicialDiagonal.nerveDiagonal.map (verticalMapNat W V F hF) ≫ verticalAugmentation V =
      verticalAugmentation W ≫ nerveMap F := by
  ext n A
  refine CategoryTheory.Functor.ext (fun _=>rfl) ?_
  intro i j f
  erw [Category.id_comp, Category.comp_id]
  change F.map ((A.map f).hom.app i) ≫ F.map ((A.obj j).obj.map f) = F.map (_ ≫ _)
  rw [F.map_comp]
lemma resolutionAugmentation_natural :
    SimplicialDiagonal.nerveDiagonal.map (horizontalMap W V F hF) ≫ resolutionAugmentation V =
      resolutionAugmentation W ≫ nerveMap F := by
  unfold resolutionAugmentation
  rw [←Category.assoc,diagonalIso_natural]
  simp only [Category.assoc]
  rw [verticalAugmentation_natural]
end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]

noncomputable def tripleResolutionAugmentation (p q r:ℕ) :
    SimplicialDiagonal.nerveDiagonal.obj (tripleDiagramHorizontal W p q r) ⟶
      nerve (Diagram (Diagram (Diagram C (Fin (p+1))) (Fin (q+1))) (Fin (r+1))) :=
  SimplicialDiagonal.nerveDiagonal.map (tripleDiagramTranspose W p q r) ≫
    resolutionAugmentation (property₃ W p q r) ≫ nerveMap (triplePosInclusion W p q r)
lemma tripleResolutionAugmentation_homology (p q r j:ℕ) :
    SSet.homologyMap (tripleResolutionAugmentation W p q r) DiagonalResolution.Z j =
      (tripleDiagramResolutionHomologyIso W p q r j).hom := by
  change (SSet.homologyFunctor DiagonalResolution.Z j).map
      (SimplicialDiagonal.nerveDiagonal.map (tripleDiagramTranspose W p q r) ≫
        resolutionAugmentation (property₃ W p q r) ≫ nerveMap (triplePosInclusion W p q r)) = _
  simp only [Functor.map_comp]
  rw [show (SSet.homologyFunctor DiagonalResolution.Z j).map (resolutionAugmentation (property₃ W p q r)) =
    (homologyIso (property₃ W p q r) j).hom from resolutionAugmentation_homology _ j]
  rfl
noncomputable instance tripleResolutionAugmentation_isIso (p q r j:ℕ) :
    IsIso (SSet.homologyMap (tripleResolutionAugmentation W p q r) DiagonalResolution.Z j) := by
  rw [tripleResolutionAugmentation_homology]
  infer_instance
lemma tripleResolutionAugmentation_outer_natural (p q:ℕ) {r s:ℕ}
    (u:Fin (r+1)→oFin (s+1)) :
    SimplicialDiagonal.nerveDiagonal.map (tripleOuterReindex W p q u) ≫
      tripleResolutionAugmentation W p q r =
      tripleResolutionAugmentation W p q s ≫ nerveMap (Diagram.reindex u) := by
  have ht := congrArg SimplicialDiagonal.nerveDiagonal.map (tripleDiagramTranspose_outerReindex W p q u)
  simp only [Functor.map_comp] at ht
  unfold tripleResolutionAugmentation
  rw [←Category.assoc _ (SimplicialDiagonal.nerveDiagonal.map (tripleDiagramTranspose W p q r)),ht]
  simp only [Category.assoc]
  rw [←Category.assoc _ (resolutionAugmentation (property₃ W p q r)),resolutionAugmentation_natural]
  simp only [Category.assoc]
  have he : nerveMap (posReindex (property₂ W p q) u) ≫ nerveMap (triplePosInclusion W p q r) =
      nerveMap (triplePosInclusion W p q s) ≫ nerveMap (Diagram.reindex u) := by
    change nerveMap (posReindex (property₂ W p q) u ⋙ triplePosInclusion W p q r) =
      nerveMap (triplePosInclusion W p q s ⋙ Diagram.reindex u)
    rw [triplePosInclusion_outerReindex]
  rw [he]
lemma tripleResolutionAugmentation_middle_natural (p r:ℕ) {q s:ℕ}
    (u:Fin (q+1)→oFin (s+1)) :
    SimplicialDiagonal.nerveDiagonal.map (tripleMiddleReindex W p r u) ≫
      tripleResolutionAugmentation W p q r =
      tripleResolutionAugmentation W p s r ≫ nerveMap (Diagram.map (Diagram.reindex u)) := by
  have ht := congrArg SimplicialDiagonal.nerveDiagonal.map (tripleDiagramTranspose_middleReindex W p r u)
  simp only [Functor.map_comp] at ht
  unfold tripleResolutionAugmentation
  rw [←Category.assoc _ (SimplicialDiagonal.nerveDiagonal.map (tripleDiagramTranspose W p q r)),ht]
  simp only [Category.assoc]
  rw [←Category.assoc _ (resolutionAugmentation (property₃ W p q r)),resolutionAugmentation_natural]
  simp only [Category.assoc]
  have he : nerveMap (nestedPosReindex (diagramProperty W (Fin (p+1))) u) ≫ nerveMap (triplePosInclusion W p q r) =
      nerveMap (triplePosInclusion W p s r) ≫ nerveMap (Diagram.map (Diagram.reindex u)) := by
    change nerveMap (nestedPosReindex (diagramProperty W (Fin (p+1))) u ⋙ triplePosInclusion W p q r) =
      nerveMap (triplePosInclusion W p s r ⋙ Diagram.map (Diagram.reindex u))
    rw [triplePosInclusion_middleReindex]
  rw [he]
end

end RestrictedNerve

end OAI
