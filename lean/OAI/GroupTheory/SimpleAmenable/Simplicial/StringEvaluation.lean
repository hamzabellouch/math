import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.ResolutionAugmentation

namespace OAI

namespace RestrictedNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory

section
open IntervalBar IntervalBar.Diagram

section
variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C) [W.IsMultiplicative]
noncomputable def stringEvaluation {n:ℕ} (t:Fin (n+1)) : Strings W n ⥤ C where
  obj A := A.obj.obj t
  map f := f.hom.app t
  map_id _ := rfl
  map_comp _ _ := rfl
@[simp] lemma stringEvaluation_obj {n:ℕ} (t:Fin (n+1)) (A:Strings W n) :
    (stringEvaluation W t).obj A=A.obj.obj t := rfl
@[simp] lemma stringEvaluation_map {n:ℕ} (t:Fin (n+1)) {A B:Strings W n} (f:A⟶B) :
    (stringEvaluation W t).map f=f.hom.app t := rfl
end

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
noncomputable instance stringEvaluationMonoidal {n:ℕ} (t:Fin (n+1)) :
    (stringEvaluation W t).Monoidal := Functor.CoreMonoidal.toMonoidal {
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _
  μIso_hom_natural_left := by intros; simp
  μIso_hom_natural_right := by intros; simp
  associativity := by intros; simp
  left_unitality := by intros; simp
  right_unitality := by intros; simp }
noncomputable instance stringEvaluationBraided {n:ℕ} (t:Fin (n+1)) :
    (stringEvaluation W t).Braided where
  braided _ _ := by
    change 𝟙 _ ≫ (β_ _ _).hom = (β_ _ _).hom ≫ 𝟙 _
    simp
omit [Fact W.StableUnderInverse] in
@[simp] lemma stringEvaluation_η {n:ℕ} (t:Fin (n+1)) :
    Functor.OplaxMonoidal.η (stringEvaluation W t)=𝟙 _ := rfl
omit [Fact W.StableUnderInverse] in
@[simp] lemma stringEvaluation_ε {n:ℕ} (t:Fin (n+1)) :
    Functor.LaxMonoidal.ε (stringEvaluation W t)=𝟙 _ := rfl
omit [Fact W.StableUnderInverse] in
@[simp] lemma stringEvaluation_μ {n:ℕ} (t:Fin (n+1)) (A B:Strings W n) :
    Functor.LaxMonoidal.μ (stringEvaluation W t) A B=𝟙 _ := rfl
variable {I:Type} [Preorder I]
lemma transpose_evaluation {n:ℕ} (t:Fin (n+1)) :
    transposeDiagram (I:=I) W n ⋙ stringEvaluation (diagramProperty W I) t ⋙
      posDiagramInclusion W I = Diagram.map (stringEvaluation W t) := by
  refine CategoryTheory.Functor.ext (fun _=>?_) ?_
  · refine ext_heq rfl ?_ ?_
    · apply heq_of_eq; funext i; apply Iso.ext
      simp [transposeDiagram,transposeDiagramObj,stringVertex,mapObj,diagramInclusion]
      rfl
    · apply heq_of_eq; funext i j k hij hjk; apply Iso.ext
      simp [transposeDiagram,transposeDiagramObj,stringVertex,mapObj,diagramInclusion]
      rfl
  · intro A B f
    apply Hom.ext; intro i j h
    simp [transposeDiagram,transposeDiagramHom,Diagram.map]
    erw [Diagram.eqToHom_app, Diagram.eqToHom_app]
    change (f.app i j h).hom.app t = 𝟙 _ ≫ (f.app i j h).hom.app t ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
end

section
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
omit [Fact W.StableUnderInverse] in
@[simp] lemma restrictionInclusion_ε : Functor.LaxMonoidal.ε (inclusion W)=𝟙 _ := rfl
variable {I:Type} [Preorder I]
noncomputable instance transpose_evaluation_monoidal {n:ℕ} (t:Fin (n+1)) :
    NatTrans.IsMonoidal (eqToHom (transpose_evaluation (I:=I) W t)) where
  unit := by
    apply Hom.ext; intro i j h
    simp only [Functor.LaxMonoidal.comp_ε,posInclusion_ε,stringEvaluation_ε,
      IntervalBar.Diagram.map_ε,transpose_ε]
    simp [transposeε, mapεHom,diagramInclusion]
    erw [Diagram.eqToHom_app]
    change (𝟙 (𝟙_ C) ≫ 𝟙 _) ≫ 𝟙 _ = 𝟙 _
    simp only [Category.comp_id]
  tensor A B := by
    apply Hom.ext; intro i j h
    simp only [Functor.LaxMonoidal.comp_μ,posInclusion_μ,stringEvaluation_μ,
      IntervalBar.Diagram.map_μ,transpose_μ]
    simp [transposeμ,mapμHom,diagramInclusion]
    erw [Diagram.eqToHom_app, Diagram.eqToHom_app, Diagram.eqToHom_app]
    change (𝟙 ((A.obj i j h).obj.obj t ⊗ (B.obj i j h).obj.obj t) ≫ 𝟙 _) ≫ 𝟙 _ =
      (𝟙 _ ⊗ₘ 𝟙 _) ≫ 𝟙 _
    simp only [id_tensorHom_id, Category.comp_id]
end

open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
lemma tripleTranspose_evaluation (p q r:ℕ) {n:ℕ} (t:Fin (n+1)) :
    tripleTranspose W p q r n ⋙ stringEvaluation (property₃ W p q r) t ⋙
      triplePosInclusion W p q r =
    Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1))
      (Diagram.map (I:=Fin (p+1)) (stringEvaluation W t))) := by
  have h₁ := Diagram.map₂_congr (I:=Fin (q+1)) (J:=Fin (r+1))
    (transpose_evaluation (I:=Fin (p+1)) W t) (transpose_evaluation_monoidal W t)
  simp only [map₂_comp] at h₁
  have h₂ := Diagram.map_congr (I:=Fin (r+1))
    (transpose_evaluation (I:=Fin (q+1)) (diagramProperty W (Fin (p+1))) t)
    (transpose_evaluation_monoidal (diagramProperty W (Fin (p+1))) t)
  simp only [Diagram.map_comp] at h₂
  have h₃ := transpose_evaluation (I:=Fin (r+1)) (property₂ W p q) t
  change Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1)) (transposeDiagram (I:=Fin (p+1)) W n)) ⋙
    Diagram.map (I:=Fin (r+1)) (transposeDiagram (I:=Fin (q+1)) (diagramProperty W (Fin (p+1))) n) ⋙
    (transposeDiagram (I:=Fin (r+1)) (property₂ W p q) n ⋙ stringEvaluation (property₃ W p q r) t ⋙
      posDiagramInclusion (property₂ W p q) (Fin (r+1))) ⋙
    Diagram.map (I:=Fin (r+1)) (posDiagramInclusion (diagramProperty W (Fin (p+1))) (Fin (q+1))) ⋙
    Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1)) (posDiagramInclusion W (Fin (p+1)))) = _
  rw [h₃]
  change Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1)) (transposeDiagram (I:=Fin (p+1)) W n)) ⋙
    (Diagram.map (I:=Fin (r+1)) (transposeDiagram (I:=Fin (q+1)) (diagramProperty W (Fin (p+1))) n) ⋙
      Diagram.map (I:=Fin (r+1)) (stringEvaluation (property₂ W p q) t) ⋙
      Diagram.map (I:=Fin (r+1)) (posDiagramInclusion (diagramProperty W (Fin (p+1))) (Fin (q+1)))) ⋙
    Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1)) (posDiagramInclusion W (Fin (p+1)))) = _
  rw [h₂]
  exact h₁
end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]

noncomputable def tripleInnerReindex (q r:ℕ) {p s:ℕ} (u:Fin (p+1)→oFin (s+1)) :
    tripleDiagramHorizontal W s q r ⟶ tripleDiagramHorizontal W p q r where
  app n := (Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1))
    (Diagram.reindex (C:=Strings W n.unop.len) u))).toCatHom
  naturality _ _ f := by
    apply Cat.ext
    have he := Diagram.map₂_congr (I:=Fin (q+1)) (J:=Fin (r+1))
      (Diagram.reindex_map (reindex W f.unop.toOrderHom.toFunctor) u)
      (Diagram.reindex_map_monoidal (reindex W f.unop.toOrderHom.toFunctor) u)
    simp only [map₂_comp] at he
    exact he.symm
lemma tripleResolutionAugmentation_inner_natural (q r:ℕ) {p s:ℕ}
    (u:Fin (p+1)→oFin (s+1)) :
    SimplicialDiagonal.nerveDiagonal.map (tripleInnerReindex W q r u) ≫
      tripleResolutionAugmentation W p q r =
      tripleResolutionAugmentation W s q r ≫
        nerveMap (Diagram.map (Diagram.map (Diagram.reindex u))) := by
  ext n A
  refine CategoryTheory.Functor.ext (fun i=> ?_) ?_
  · change ((Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1))
          (Diagram.reindex (C:=Strings W n.unop.len) u)) ⋙
        tripleTranspose W p q r n.unop.len ⋙ stringEvaluation (property₃ W p q r) i ⋙
          triplePosInclusion W p q r).obj (A.obj i)) =
      ((tripleTranspose W s q r n.unop.len ⋙ stringEvaluation (property₃ W s q r) i ⋙
          triplePosInclusion W s q r ⋙ Diagram.map (I:=Fin (r+1))
            (Diagram.map (I:=Fin (q+1)) (Diagram.reindex (C:=C) u))).obj (A.obj i))
    rw [tripleTranspose_evaluation W p q r i]
    change _ = (((tripleTranspose W s q r n.unop.len ⋙ stringEvaluation (property₃ W s q r) i ⋙
          triplePosInclusion W s q r) ⋙ Diagram.map (I:=Fin (r+1))
            (Diagram.map (I:=Fin (q+1)) (Diagram.reindex (C:=C) u))).obj (A.obj i))
    rw [tripleTranspose_evaluation W s q r i]
    exact congrArg (fun F=>F.obj (A.obj i))
      (Diagram.map_map_map_reindex (K:=Fin (q+1)) (L:=Fin (r+1)) (stringEvaluation W i) u).symm
  · intro i j f
    apply Hom.ext; intro a b h
    apply Hom.ext; intro c d k
    apply Hom.ext; intro e g l
    simp only [Diagram.comp_app,Diagram.eqToHom_app]
    erw [Category.id_comp, Category.comp_id]
    rfl
end

end RestrictedNerve

end OAI
