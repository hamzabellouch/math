import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.NestedPosReindex

namespace OAI

namespace RestrictedNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
open IntervalBar IntervalBar.Diagram

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


variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I J K:Type} [Preorder I] [Preorder J] [Preorder K]
@[simp] lemma posInclusion_ε : Functor.LaxMonoidal.ε (posDiagramInclusion W I)=mapεHom (inclusion W) := rfl
@[simp] lemma posInclusion_μ (A B:PosDiagrams W I) :
    Functor.LaxMonoidal.μ (posDiagramInclusion W I) A B=mapμHom (inclusion W) A B := rfl
@[simp] lemma posReindex_ε (u:I→oJ) : Functor.LaxMonoidal.ε (posReindex W u)=𝟙 _ := rfl
noncomputable instance posReindex_inclusion_monoidal (u:I→oJ) :
    NatTrans.IsMonoidal (eqToHom (posReindex_inclusion W u)) where
  unit := by
    apply Hom.ext; intro i j h
    simp only [CategoryTheory.eqToHom_app]
    simp only [Functor.LaxMonoidal.comp_ε,posInclusion_ε,posReindex_ε,IntervalBar.Diagram.reindex_ε]
    simp [posReindex,diagramInclusion,Diagram.reindex,mapεHom]
    erw [Diagram.eqToHom_app]
    change (𝟙 (𝟙_ C) ≫ 𝟙 _) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    simp only [Category.comp_id]
  tensor A B := by
    apply Hom.ext; intro i j h
    simp only [CategoryTheory.eqToHom_app]
    simp only [Functor.LaxMonoidal.comp_μ,posInclusion_μ,posReindex_μ,IntervalBar.Diagram.reindex_μ]
    simp [posReindex,diagramInclusion,Diagram.reindex,mapμHom]
    erw [Diagram.eqToHom_app, Diagram.eqToHom_app, Diagram.eqToHom_app]
    change (𝟙 ((A.obj (u i) (u j) (u.monotone h)).obj ⊗
      (B.obj (u i) (u j) (u.monotone h)).obj) ≫ 𝟙 _) ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _
    simp only [id_tensorHom_id, Category.comp_id]
lemma map_posReindex_inclusion (u:I→oJ) :
    Diagram.map (I:=K) (posReindex W u) ⋙ Diagram.map (posDiagramInclusion W I) =
      Diagram.map (posDiagramInclusion W J) ⋙ Diagram.map (Diagram.reindex u) := by
  have he := map_congr (I:=K) (posReindex_inclusion W u) (posReindex_inclusion_monoidal W u)
  simpa only [Diagram.map_comp] using he
end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]

noncomputable def tripleOuterReindex (p q:ℕ) {r s:ℕ} (u:Fin (r+1)→oFin (s+1)) :
    tripleDiagramHorizontal W p q s ⟶ tripleDiagramHorizontal W p q r where
  app n := (Diagram.reindex (C:=Diagram (Diagram (Strings W n.unop.len)
    (Fin (p+1))) (Fin (q+1))) u).toCatHom
  naturality _ _ f := by
    apply Cat.ext
    exact (Diagram.reindex_map (Diagram.map (I:=Fin (q+1))
      (Diagram.map (I:=Fin (p+1)) (reindex W f.unop.toOrderHom.toFunctor))) u).symm
lemma tripleTranspose_outerReindex (p q n:ℕ) {r s:ℕ} (u:Fin (r+1)→oFin (s+1)) :
    Diagram.reindex (C:=Diagram (Diagram (Strings W n) (Fin (p+1))) (Fin (q+1))) u ⋙
      tripleTranspose W p q r n =
      tripleTranspose W p q s n ⋙ stringsMap (property₃ W p q s) (property₃ W p q r)
        (posReindex (property₂ W p q) u) (posReindex_property (property₂ W p q) u) n := by
  unfold tripleTranspose
  rw [←Functor.assoc,Diagram.reindex_map]
  simp only [Functor.assoc]
  rw [←Functor.assoc (Diagram.reindex u),Diagram.reindex_map]
  simp only [Functor.assoc]
  rw [transpose_posReindex (property₂ W p q) u n]
lemma tripleDiagramTranspose_outerReindex (p q:ℕ) {r s:ℕ} (u:Fin (r+1)→oFin (s+1)) :
    tripleOuterReindex W p q u ≫ tripleDiagramTranspose W p q r =
      tripleDiagramTranspose W p q s ≫ horizontalMap (property₃ W p q s) (property₃ W p q r)
        (posReindex (property₂ W p q) u) (posReindex_property (property₂ W p q) u) := by
  apply NatTrans.ext; funext n; apply Cat.ext
  exact tripleTranspose_outerReindex W p q n.unop.len u
lemma triplePosInclusion_outerReindex (p q:ℕ) {r s:ℕ} (u:Fin (r+1)→oFin (s+1)) :
    posReindex (property₂ W p q) u ⋙ triplePosInclusion W p q r =
      triplePosInclusion W p q s ⋙ Diagram.reindex u := by
  unfold triplePosInclusion
  rw [←Functor.assoc,←Functor.assoc,posReindex_inclusion]
  simp only [Functor.assoc]
  rw [←Functor.assoc (Diagram.reindex u),Diagram.reindex_map]
  simp only [Functor.assoc]
  rw [Diagram.reindex_map]
lemma tripleDiagramResolutionHomologyIso_outer_natural (p q:ℕ) {r s:ℕ}
    (u:Fin (r+1)→oFin (s+1)) (j:ℕ) :
    SSet.homologyMap (SimplicialDiagonal.nerveDiagonal.map (tripleOuterReindex W p q u))
      DiagonalResolution.Z j ≫ (tripleDiagramResolutionHomologyIso W p q r j).hom =
      (tripleDiagramResolutionHomologyIso W p q s j).hom ≫
        SSet.homologyMap (nerveMap (Diagram.reindex u)) DiagonalResolution.Z j := by
  let H := SSet.homologyFunctor DiagonalResolution.Z j
  let N := SimplicialDiagonal.nerveDiagonal
  have ht := congrArg (fun f=>H.map (N.map f)) (tripleDiagramTranspose_outerReindex W p q u)
  simp only [Functor.map_comp] at ht
  have hr := homologyIso_natural (property₃ W p q s) (property₃ W p q r)
    (posReindex (property₂ W p q) u) (posReindex_property (property₂ W p q) u) j
  change H.map (N.map (horizontalMap (property₃ W p q s) (property₃ W p q r)
    (posReindex (property₂ W p q) u) (posReindex_property (property₂ W p q) u))) ≫
      (homologyIso (property₃ W p q r) j).hom =
      (homologyIso (property₃ W p q s) j).hom ≫
        H.map (nerveMap (posReindex (property₂ W p q) u)) at hr
  have he : nerveMap (posReindex (property₂ W p q) u) ≫ nerveMap (triplePosInclusion W p q r) =
      nerveMap (triplePosInclusion W p q s) ≫ nerveMap (Diagram.reindex u) := by
    change nerveMap (posReindex (property₂ W p q) u ⋙ triplePosInclusion W p q r) =
      nerveMap (triplePosInclusion W p q s ⋙ Diagram.reindex u)
    rw [triplePosInclusion_outerReindex]
  have hi := congrArg H.map he
  simp only [Functor.map_comp] at hi
  change H.map (N.map (tripleOuterReindex W p q u)) ≫
    (H.map (N.map (tripleDiagramTranspose W p q r)) ≫
      (homologyIso (property₃ W p q r) j).hom ≫
      H.map (nerveMap (triplePosInclusion W p q r))) =
    (H.map (N.map (tripleDiagramTranspose W p q s)) ≫
      (homologyIso (property₃ W p q s) j).hom ≫
      H.map (nerveMap (triplePosInclusion W p q s))) ≫
        H.map (nerveMap (Diagram.reindex u))
  exact compose_three_squares _ _ _ _ _ _ _ _ _ _ ht hr hi
noncomputable def tripleMiddleReindex (p r:ℕ) {q s:ℕ} (u:Fin (q+1)→oFin (s+1)) :
    tripleDiagramHorizontal W p s r ⟶ tripleDiagramHorizontal W p q r where
  app n := (Diagram.map (I:=Fin (r+1)) (Diagram.reindex (C:=Diagram (Strings W n.unop.len)
    (Fin (p+1))) u)).toCatHom
  naturality _ _ f := by
    apply Cat.ext
    exact (Diagram.map_reindex_map (I:=Fin (q+1)) (J:=Fin (s+1)) (K:=Fin (r+1))
      (Diagram.map (I:=Fin (p+1)) (reindex W f.unop.toOrderHom.toFunctor)) u).symm
lemma tripleTranspose_middleReindex (p r n:ℕ) {q s:ℕ} (u:Fin (q+1)→oFin (s+1)) :
    Diagram.map (I:=Fin (r+1)) (Diagram.reindex (C:=Diagram (Strings W n) (Fin (p+1))) u) ⋙
      tripleTranspose W p q r n =
      tripleTranspose W p s r n ⋙ stringsMap (property₃ W p s r) (property₃ W p q r)
        (nestedPosReindex (diagramProperty W (Fin (p+1))) u)
        (nestedPosReindex_property (diagramProperty W (Fin (p+1))) u) n := by
  have he := Diagram.map_reindex_map (K:=Fin (r+1)) (transposeDiagram (I:=Fin (p+1)) W n) u
  unfold tripleTranspose
  rw [←Functor.assoc,←Functor.assoc,he]
  simp only [Functor.assoc]
  rw [doubleTranspose_innerReindex (K:=Fin (r+1)) (diagramProperty W (Fin (p+1))) u n]
lemma tripleDiagramTranspose_middleReindex (p r:ℕ) {q s:ℕ} (u:Fin (q+1)→oFin (s+1)) :
    tripleMiddleReindex W p r u ≫ tripleDiagramTranspose W p q r =
      tripleDiagramTranspose W p s r ≫ horizontalMap (property₃ W p s r) (property₃ W p q r)
        (nestedPosReindex (diagramProperty W (Fin (p+1))) u)
        (nestedPosReindex_property (diagramProperty W (Fin (p+1))) u) := by
  apply NatTrans.ext; funext n; apply Cat.ext
  exact tripleTranspose_middleReindex W p r n.unop.len u
lemma triplePosInclusion_middleReindex (p r:ℕ) {q s:ℕ} (u:Fin (q+1)→oFin (s+1)) :
    nestedPosReindex (diagramProperty W (Fin (p+1))) u ⋙ triplePosInclusion W p q r =
      triplePosInclusion W p s r ⋙ Diagram.map (Diagram.reindex u) := by
  unfold triplePosInclusion
  rw [←Functor.assoc,←Functor.assoc,nestedPosReindex_inclusion]
  simp only [Functor.assoc]
  rw [←Functor.assoc (Diagram.map (posReindex (diagramProperty W (Fin (p+1))) u)),
    map_posReindex_inclusion]
  simp only [Functor.assoc]
  rw [Diagram.map_reindex_map]
lemma tripleDiagramResolutionHomologyIso_middle_natural (p r:ℕ) {q s:ℕ}
    (u:Fin (q+1)→oFin (s+1)) (j:ℕ) :
    SSet.homologyMap (SimplicialDiagonal.nerveDiagonal.map (tripleMiddleReindex W p r u))
      DiagonalResolution.Z j ≫ (tripleDiagramResolutionHomologyIso W p q r j).hom =
      (tripleDiagramResolutionHomologyIso W p s r j).hom ≫
        SSet.homologyMap (nerveMap (Diagram.map (Diagram.reindex u))) DiagonalResolution.Z j := by
  let H := SSet.homologyFunctor DiagonalResolution.Z j
  let N := SimplicialDiagonal.nerveDiagonal
  have ht := congrArg (fun f=>H.map (N.map f)) (tripleDiagramTranspose_middleReindex W p r u)
  simp only [Functor.map_comp] at ht
  have hr := homologyIso_natural (property₃ W p s r) (property₃ W p q r)
    (nestedPosReindex (diagramProperty W (Fin (p+1))) u) (nestedPosReindex_property (diagramProperty W (Fin (p+1))) u) j
  change H.map (N.map (horizontalMap (property₃ W p s r) (property₃ W p q r)
    (nestedPosReindex (diagramProperty W (Fin (p+1))) u) (nestedPosReindex_property (diagramProperty W (Fin (p+1))) u))) ≫
      (homologyIso (property₃ W p q r) j).hom =
      (homologyIso (property₃ W p s r) j).hom ≫
        H.map (nerveMap (nestedPosReindex (diagramProperty W (Fin (p+1))) u)) at hr
  have he : nerveMap (nestedPosReindex (diagramProperty W (Fin (p+1))) u) ≫ nerveMap (triplePosInclusion W p q r) =
      nerveMap (triplePosInclusion W p s r) ≫ nerveMap (Diagram.map (Diagram.reindex u)) := by
    change nerveMap (nestedPosReindex (diagramProperty W (Fin (p+1))) u ⋙ triplePosInclusion W p q r) =
      nerveMap (triplePosInclusion W p s r ⋙ Diagram.map (Diagram.reindex u))
    rw [triplePosInclusion_middleReindex]
  have hi := congrArg H.map he
  simp only [Functor.map_comp] at hi
  change H.map (N.map (tripleMiddleReindex W p r u)) ≫
    (H.map (N.map (tripleDiagramTranspose W p q r)) ≫
      (homologyIso (property₃ W p q r) j).hom ≫
      H.map (nerveMap (triplePosInclusion W p q r))) =
    (H.map (N.map (tripleDiagramTranspose W p s r)) ≫
      (homologyIso (property₃ W p s r) j).hom ≫
      H.map (nerveMap (triplePosInclusion W p s r))) ≫
        H.map (nerveMap (Diagram.map (Diagram.reindex u)))
  exact compose_three_squares _ _ _ _ _ _ _ _ _ _ ht hr hi
end

end RestrictedNerve

end OAI
