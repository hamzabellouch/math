import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.TripleComposition
import OAI.GroupTheory.SimpleAmenable.Simplicial.RestrictedTripleDegree

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace IntervalBar.Diagram

variable {C D:Type} [Groupoid.{0} C] [Groupoid.{0} D]
  [MonoidalCategory C] [MonoidalCategory D]
lemma monoidal_congr {F G:C⥤D} [hF:F.Monoidal] [hG:G.Monoidal] (e:F=G)
    (h:NatTrans.IsMonoidal (eqToHom e)) : HEq hF hG := by
  cases e
  apply heq_of_eq
  have hε : hF.ε=hG.ε := by
    have hh := h.unit
    simpa only [eqToHom_refl,NatTrans.id_app,Category.comp_id] using hh
  have hμ : hF.μ=hG.μ := by
    funext X Y
    have hh := h.tensor X Y
    simpa only [eqToHom_refl,NatTrans.id_app,Category.comp_id,id_tensorHom_id,Category.id_comp] using hh
  apply Functor.Monoidal.ext hε hμ
  · have he : @Functor.Monoidal.εIso _ _ _ _ _ _ F hF = @Functor.Monoidal.εIso _ _ _ _ _ _ F hG := Iso.ext hε
    exact congrArg Iso.inv he
  · funext X Y
    have he : @Functor.Monoidal.μIso _ _ _ _ _ _ F hF X Y = @Functor.Monoidal.μIso _ _ _ _ _ _ F hG X Y :=
      Iso.ext (congrFun (congrFun hμ X) Y)
    exact congrArg Iso.inv he
lemma map_congr {I:Type} [Preorder I] {F G:C⥤D} [hF:F.Monoidal] [hG:G.Monoidal]
    (e:F=G) (h:NatTrans.IsMonoidal (eqToHom e)) : map (I:=I) F=map G := by
  have hm := monoidal_congr e h
  cases e
  have hh : hF=hG := eq_of_heq hm
  cases hh
  rfl
end IntervalBar.Diagram

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I:Type} [Preorder I]
@[simp] lemma transpose_ε (n:ℕ) :
    Functor.LaxMonoidal.ε (transposeDiagram (I:=I) W n)=transposeε W n := rfl
@[simp] lemma transpose_μ (n:ℕ) (A B:Diagram (Strings W n) I) :
    Functor.LaxMonoidal.μ (transposeDiagram W n) A B=transposeμ W n A B := rfl
omit [Fact W.StableUnderInverse] in
@[simp] lemma reindex_ε {n m:ℕ} (u:Fin (n+1)⥤Fin (m+1)) :
    Functor.LaxMonoidal.ε (reindex W u)=𝟙 _ := rfl
@[simp] lemma map_reindex_ε {n m:ℕ} (u:Fin (n+1)⥤Fin (m+1)) :
    Functor.LaxMonoidal.ε (Diagram.map (I:=I) (reindex W u))=Diagram.mapεHom (reindex W u) := rfl
@[simp] lemma map_reindex_μ {n m:ℕ} (u:Fin (n+1)⥤Fin (m+1)) (A B:Diagram (Strings W m) I) :
    Functor.LaxMonoidal.μ (Diagram.map (reindex W u)) A B=Diagram.mapμHom (reindex W u) A B := rfl
lemma transpose_reindex {p q:SimplexCategoryᵒᵖ} (f:p⟶q) :
    Diagram.map (I:=I) (reindex W f.unop.toOrderHom.toFunctor) ⋙ transposeDiagram W q.unop.len =
      transposeDiagram W p.unop.len ⋙ reindex (diagramProperty W I) f.unop.toOrderHom.toFunctor :=
  congrArg Cat.Hom.toFunctor ((diagramTranspose (I:=I) W).naturality f)
private noncomputable abbrev transposeReindexLeft {p q:SimplexCategoryᵒᵖ} (f:p⟶q) := (Diagram.map (I:=I) (reindex W f.unop.toOrderHom.toFunctor) ⋙ transposeDiagram W q.unop.len)
private noncomputable abbrev transposeReindexRight {p q:SimplexCategoryᵒᵖ} (f:p⟶q) := (transposeDiagram (I:=I) W p.unop.len ⋙ reindex (diagramProperty W I) f.unop.toOrderHom.toFunctor)
private noncomputable abbrev transposeReindexHom {p q:SimplexCategoryᵒᵖ} (f:p⟶q) :
    transposeReindexLeft (I:=I) W f ⟶ transposeReindexRight (I:=I) W f := (eqToHom (transpose_reindex (I:=I) W f))
private lemma transpose_comp_app {n : ℕ}
    {A B D : Strings (diagramProperty W I) n} (f : A ⟶ B) (g : B ⟶ D)
    (t : Fin (n+1)) (i j : I) (h : i ≤ j) :
    ((f ≫ g).hom.app t).hom.app i j h =
      (f.hom.app t).hom.app i j h ≫ (g.hom.app t).hom.app i j h := rfl
private lemma transpose_tensor_app {n : ℕ}
    {A B D E : Strings (diagramProperty W I) n} (f : A ⟶ B) (g : D ⟶ E)
    (t : Fin (n+1)) (i j : I) (h : i ≤ j) :
    ((f ⊗ₘ g).hom.app t).hom.app i j h =
      (f.hom.app t).hom.app i j h ⊗ₘ (g.hom.app t).hom.app i j h := by
  change ((f.hom.app t ⊗ₘ g.hom.app t).hom.app i j h) = _
  exact posTensor_app W I (f.hom.app t) (g.hom.app t) i j h
private lemma transpose_reindex_unit {p q:SimplexCategoryᵒᵖ} (f:p⟶q) :
    Functor.LaxMonoidal.ε (transposeReindexLeft (I:=I) W f) ≫
      (transposeReindexHom (I:=I) W f).app (𝟙_ _) =
    Functor.LaxMonoidal.ε (transposeReindexRight (I:=I) W f) := by
  apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
  apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
  simp only [transposeReindexHom, CategoryTheory.eqToHom_app]
  simp only [Functor.LaxMonoidal.comp_ε,transpose_ε,reindex_ε,map_reindex_ε]
  simp [transposeDiagram,transposeDiagramHom,transposeε,
    Diagram.mapεHom,reindex]
  erw [comp_app, comp_app, eqToHom_transposed_app]
  change (𝟙 (𝟙_ C)) ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  simp only [Category.id_comp]
private lemma transposeReindexHom_app {p q:SimplexCategoryᵒᵖ} (f:p⟶q)
    (A:Diagram (Strings W p.unop.len) I)
    (t:Fin (q.unop.len+1)) (i j:I) (h:i≤j) :
    (((transposeReindexHom (I:=I) W f).app A).hom.app t).hom.app i j h =
      𝟙 ((A.obj i j h).obj.obj (f.unop.toOrderHom.toFunctor.obj t)) := by
  simp only [transposeReindexHom, CategoryTheory.eqToHom_app]
  erw [eqToHom_transposed_app]
  rfl
private lemma transposeReindexLeft_μ_app {p q:SimplexCategoryᵒᵖ} (f:p⟶q)
    (A B:Diagram (Strings W p.unop.len) I)
    (t:Fin (q.unop.len+1)) (i j:I) (h:i≤j) :
    ((Functor.LaxMonoidal.μ (transposeReindexLeft (I:=I) W f) A B).hom.app t).hom.app i j h =
      𝟙 ((A.obj i j h).obj.obj (f.unop.toOrderHom.toFunctor.obj t) ⊗
        (B.obj i j h).obj.obj (f.unop.toOrderHom.toFunctor.obj t)) := by
  change (𝟙 _) ≫ 𝟙 _ = 𝟙 _
  exact Category.id_comp _
private lemma transpose_reindex_tensor {p q:SimplexCategoryᵒᵖ} (f:p⟶q)
    (A B:Diagram (Strings W p.unop.len) I) :
    Functor.LaxMonoidal.μ (transposeReindexLeft (I:=I) W f) A B ≫
      (transposeReindexHom (I:=I) W f).app (A ⊗ B) =
    ((transposeReindexHom (I:=I) W f).app A ⊗ₘ
      (transposeReindexHom (I:=I) W f).app B) ≫
    Functor.LaxMonoidal.μ (transposeReindexRight (I:=I) W f) A B := by
  apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
  apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
  erw [transpose_comp_app W (Functor.LaxMonoidal.μ (transposeReindexLeft (I:=I) W f) A B)
      ((transposeReindexHom (I:=I) W f).app (A ⊗ B))]
  erw [transpose_comp_app W
      ((transposeReindexHom (I:=I) W f).app A ⊗ₘ (transposeReindexHom (I:=I) W f).app B)
      (Functor.LaxMonoidal.μ (transposeReindexRight (I:=I) W f) A B)]
  erw [transpose_tensor_app]
  erw [transposeReindexLeft_μ_app, transposeReindexHom_app]
  erw [transposeReindexHom_app W f A, transposeReindexHom_app W f B]
  change (𝟙 ((A.obj i j h).obj.obj (f.unop.toOrderHom.toFunctor.obj t) ⊗
      (B.obj i j h).obj.obj (f.unop.toOrderHom.toFunctor.obj t))) ≫ 𝟙 _ =
    (𝟙 _ ⊗ₘ 𝟙 _) ≫ 𝟙 _
  simp only [id_tensorHom_id, Category.comp_id]
noncomputable instance transpose_reindex_monoidal {p q:SimplexCategoryᵒᵖ} (f:p⟶q) :
    NatTrans.IsMonoidal (eqToHom (transpose_reindex (I:=I) W f)) where
  unit := transpose_reindex_unit W f
  tensor A B := transpose_reindex_tensor W f A B
end RestrictedNerve

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace IntervalBar.Diagram

variable {C D:Type} [Groupoid.{0} C] [Groupoid.{0} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [SymmetricCategory C] [SymmetricCategory D]
lemma braided_congr {F G:C⥤D} [hF:F.Braided] [hG:G.Braided] (e:F=G)
    (h:NatTrans.IsMonoidal (eqToHom e)) : HEq hF hG := by
  have hm := monoidal_congr e h
  cases e
  apply heq_of_eq
  apply Functor.Braided.ext
  · exact congrArg (fun h:F.Monoidal=>h.ε) (eq_of_heq hm)
  · exact congrArg (fun h:F.Monoidal=>h.μ) (eq_of_heq hm)
  · exact congrArg (fun h:F.Monoidal=>h.η) (eq_of_heq hm)
  · exact congrArg (fun h:F.Monoidal=>h.δ) (eq_of_heq hm)
lemma map₂_congr {I J:Type} [Preorder I] [Preorder J]
    {F G:C⥤D} [hF:F.Braided] [hG:G.Braided] (e:F=G)
    (h:NatTrans.IsMonoidal (eqToHom e)) :
    map (I:=J) (map (I:=I) F)=map (map G) := by
  have hm := braided_congr e h
  cases e
  have hh : hF=hG := eq_of_heq hm
  cases hh
  rfl
end IntervalBar.Diagram

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
lemma tripleTranspose_reindex (p q r:ℕ) {u v:SimplexCategoryᵒᵖ} (f:u⟶v) :
    Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1)) (Diagram.map (I:=Fin (p+1))
      (reindex W f.unop.toOrderHom.toFunctor))) ⋙ tripleTranspose W p q r v.unop.len =
      tripleTranspose W p q r u.unop.len ⋙ reindex (property₃ W p q r) f.unop.toOrderHom.toFunctor := by
  have h₁ := map₂_congr (I:=Fin (q+1)) (J:=Fin (r+1))
    (transpose_reindex (I:=Fin (p+1)) W f) (transpose_reindex_monoidal W f)
  rw [map₂_comp,map₂_comp] at h₁
  have h₂ := map_congr (I:=Fin (r+1))
    (transpose_reindex (I:=Fin (q+1)) (diagramProperty W (Fin (p+1))) f)
      (transpose_reindex_monoidal (diagramProperty W (Fin (p+1))) f)
  rw [Diagram.map_comp,Diagram.map_comp] at h₂
  have h₃ := transpose_reindex (I:=Fin (r+1)) (property₂ W p q) f
  unfold tripleTranspose
  rw [←Functor.assoc,←Functor.assoc,h₁]
  simp only [Functor.assoc]
  rw [←Functor.assoc
    (Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1))
      (reindex (diagramProperty W (Fin (p+1))) f.unop.toOrderHom.toFunctor)))
    (Diagram.map (I:=Fin (r+1)) (transposeDiagram (I:=Fin (q+1))
      (diagramProperty W (Fin (p+1))) v.unop.len))
    (transposeDiagram (I:=Fin (r+1)) (property₂ W p q) v.unop.len),h₂]
  simp only [Functor.assoc]
  rw [h₃]
noncomputable def tripleDiagramTranspose (p q r:ℕ) :
    tripleDiagramHorizontal W p q r ⟶ horizontal (property₃ W p q r) where
  app n := (tripleTranspose W p q r n.unop.len).toCatHom
  naturality u v f := by apply Cat.ext; exact tripleTranspose_reindex W p q r f

noncomputable def tripleDiagramResolutionHomologyIso (p q r j:ℕ) :
    (SimplicialDiagonal.nerveDiagonal.obj (tripleDiagramHorizontal W p q r)).homology
      DiagonalResolution.Z j ≅
    (nerve (Diagram (Diagram (Diagram C (Fin (p+1))) (Fin (q+1))) (Fin (r+1)))).homology
      DiagonalResolution.Z j := by
  haveI := SimplicialDiagonal.nerveDiagonal_isIso (tripleDiagramTranspose W p q r)
    (fun n=>inferInstanceAs (tripleTranspose W p q r n.unop.len).IsEquivalence) j
  exact asIso (SSet.homologyMap
    (SimplicialDiagonal.nerveDiagonal.map (tripleDiagramTranspose W p q r))
      DiagonalResolution.Z j) ≪≫ tripleRestrictedHomologyIso W p q r j
end RestrictedNerve

end OAI
