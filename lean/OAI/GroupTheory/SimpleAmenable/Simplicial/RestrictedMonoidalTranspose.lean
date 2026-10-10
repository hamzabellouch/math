import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.TripleBarMaps
import OAI.GroupTheory.SimpleAmenable.Simplicial.InducedMonoidal

namespace OAI

namespace RestrictedNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal
open IntervalBar IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I : Type} [Preorder I] (n : ℕ)
noncomputable def transposeε : (𝟙_ (Strings (diagramProperty W I) n)) ⟶
    (transposeDiagram W n).obj (𝟙_ (Diagram (Strings W n) I)) := ⟨{
  app t := InducedCategory.homMk {
    app i j h := 𝟙 _
    unit i := by
      simp [transposeDiagram,transposeDiagramObj,stringVertex,diagramInclusion,mapObj]
      erw [Category.id_comp]
      rfl
    cut i j k hij hjk := by
      simp [transposeDiagram,transposeDiagramObj,stringVertex,diagramInclusion,mapObj]
      erw [id_tensorHom_id, Category.id_comp, Category.comp_id]
      rfl }
  naturality t s f := by
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    simp [transposeDiagram,transposeDiagramObj,stringVertexMap,diagramInclusion]
    change (𝟙 (𝟙_ C)) = 𝟙 _ ≫ 𝟙 _
    exact (Category.id_comp _).symm },
  by intro t i j h; exact W.id_mem _⟩
noncomputable def transposeμ (A B : Diagram (Strings W n) I) :
    (transposeDiagram W n).obj A ⊗ (transposeDiagram W n).obj B ⟶
    (transposeDiagram W n).obj (A ⊗ B) := ⟨{
  app t := InducedCategory.homMk {
    app i j h := 𝟙 _
    unit i := by
      simp [transposeDiagram,transposeDiagramObj,stringVertex,diagramInclusion,mapObj]
      erw [Category.id_comp]
      rfl
    cut i j k hij hjk := by
      simp [transposeDiagram,transposeDiagramObj,stringVertex,diagramInclusion,mapObj]
      erw [id_tensorHom_id, Category.id_comp, Category.comp_id]
      rfl }
  naturality t s f := by
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    change (stringVertexMap W A f ⊗ₘ stringVertexMap W B f).hom.app i j h ≫ 𝟙 _ =
      𝟙 _ ≫ ((A.obj i j h).obj.map f ⊗ₘ (B.obj i j h).obj.map f)
    erw [posTensor_app]
    change ((A.obj i j h).obj.map f ⊗ₘ (B.obj i j h).obj.map f) ≫ 𝟙 _ =
      𝟙 _ ≫ ((A.obj i j h).obj.map f ⊗ₘ (B.obj i j h).obj.map f)
    simp only [Category.comp_id, Category.id_comp] },
  by intro t i j h; exact W.id_mem _⟩
private lemma transposeμ_natural_left {A B : Diagram (Strings W n) I}
    (f : A ⟶ B) (D : Diagram (Strings W n) I) :
    ((transposeDiagram W n).map f ▷ (transposeDiagram W n).obj D) ≫ transposeμ W n B D =
      transposeμ W n A D ≫ (transposeDiagram W n).map (f ▷ D) := by
  apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
  apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
  change ((transposeDiagramHom W f).hom.app t ▷ (transposeDiagramObj W D).obj.obj t).hom.app i j h ≫ 𝟙 _ =
    𝟙 _ ≫ ((transposeDiagramHom W (f ▷ D)).hom.app t).hom.app i j h
  erw [posWhiskerRight_app]
  change ((f.app i j h).hom.app t ▷ (D.obj i j h).obj.obj t) ≫ 𝟙 _ =
    𝟙 _ ≫ ((f ▷ D).app i j h).hom.app t
  erw [Diagram.whiskerRight_app]
  change ((f.app i j h).hom.app t ▷ (D.obj i j h).obj.obj t) ≫ 𝟙 _ =
    𝟙 _ ≫ ((f.app i j h).hom.app t ▷ (D.obj i j h).obj.obj t)
  simp only [Category.comp_id, Category.id_comp]

private lemma transposeμ_natural_right {A B : Diagram (Strings W n) I}
    (D : Diagram (Strings W n) I) (f : A ⟶ B) :
    ((transposeDiagram W n).obj D ◁ (transposeDiagram W n).map f) ≫ transposeμ W n D B =
      transposeμ W n D A ≫ (transposeDiagram W n).map (D ◁ f) := by
  apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
  apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
  change ((transposeDiagramObj W D).obj.obj t ◁ (transposeDiagramHom W f).hom.app t).hom.app i j h ≫ 𝟙 _ =
    𝟙 _ ≫ ((transposeDiagramHom W (D ◁ f)).hom.app t).hom.app i j h
  erw [posWhiskerLeft_app]
  change ((D.obj i j h).obj.obj t ◁ (f.app i j h).hom.app t) ≫ 𝟙 _ =
    𝟙 _ ≫ ((D ◁ f).app i j h).hom.app t
  erw [Diagram.whiskerLeft_app]
  change ((D.obj i j h).obj.obj t ◁ (f.app i j h).hom.app t) ≫ 𝟙 _ =
    𝟙 _ ≫ ((D.obj i j h).obj.obj t ◁ (f.app i j h).hom.app t)
  simp only [Category.comp_id, Category.id_comp]

noncomputable instance transposeMonoidal : (transposeDiagram (I:=I) W n).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := asIso (transposeε W n)
    μIso A B := asIso (transposeμ W n A B)
    μIso_hom_natural_left := by
      intro A B f D
      exact transposeμ_natural_left W n f D
    μIso_hom_natural_right := by
      intro A B D f
      exact transposeμ_natural_right W n D f
    associativity := by
      intro A B D
      apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
      change (((transposeμ W n A B).hom.app t ▷ (transposeDiagramObj W D).obj.obj t).hom.app i j h) ≫
          ((transposeμ W n (A ⊗ B) D).hom.app t).hom.app i j h ≫
          ((transposeDiagramHom W (α_ A B D).hom).hom.app t).hom.app i j h =
        (α_ (stringVertex W A t) (stringVertex W B t) (stringVertex W D t)).hom.hom.app i j h ≫
          ((stringVertex W A t ◁ (transposeμ W n B D).hom.app t).hom.app i j h) ≫
          ((transposeμ W n A (B ⊗ D)).hom.app t).hom.app i j h
      erw [posWhiskerRight_app, posWhiskerLeft_app, posAssoc_app]
      change (𝟙 _ ▷ (D.obj i j h).obj.obj t) ≫ 𝟙 _ ≫
          (α_ ((A.obj i j h).obj.obj t) ((B.obj i j h).obj.obj t) ((D.obj i j h).obj.obj t)).hom =
        (α_ ((A.obj i j h).obj.obj t) ((B.obj i j h).obj.obj t) ((D.obj i j h).obj.obj t)).hom ≫
          ((A.obj i j h).obj.obj t ◁ 𝟙 _) ≫ 𝟙 _
      simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
    left_unitality := by
      intro A
      apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
      change (λ_ ((A.obj i j h).obj.obj t)).hom =
        (((transposeε W n).hom.app t ▷ stringVertex W A t).hom.app i j h) ≫
          𝟙 _ ≫ (λ_ ((A.obj i j h).obj.obj t)).hom
      erw [posWhiskerRight_app]
      change (λ_ ((A.obj i j h).obj.obj t)).hom =
        (𝟙 _ ▷ (A.obj i j h).obj.obj t) ≫ 𝟙 _ ≫ (λ_ ((A.obj i j h).obj.obj t)).hom
      simp only [id_whiskerRight, Category.id_comp]
    right_unitality := by
      intro A
      apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
      change (ρ_ ((A.obj i j h).obj.obj t)).hom =
        ((stringVertex W A t ◁ (transposeε W n).hom.app t).hom.app i j h) ≫
          𝟙 _ ≫ (ρ_ ((A.obj i j h).obj.obj t)).hom
      erw [posWhiskerLeft_app]
      change (ρ_ ((A.obj i j h).obj.obj t)).hom =
        ((A.obj i j h).obj.obj t ◁ 𝟙 _) ≫ 𝟙 _ ≫ (ρ_ ((A.obj i j h).obj.obj t)).hom
      simp only [whiskerLeft_id, Category.id_comp] }
noncomputable instance transposeBraided : (transposeDiagram (I:=I) W n).Braided where
  braided A B := by
    change transposeμ W n A B ≫ (transposeDiagram W n).map (β_ A B).hom =
      (β_ ((transposeDiagram W n).obj A) ((transposeDiagram W n).obj B)).hom ≫ transposeμ W n B A
    apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    simp [transposeμ,transposeDiagram,transposeDiagramHom]
    erw [InducedCategory.comp_hom, comp_app, comp_app, posBraiding_app]
    erw [Category.id_comp, Category.comp_id]
    rfl
end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Functor.LaxMonoidal
open IntervalBar IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
instance inclusionEssSurj : (inclusion W).EssSurj where
  mem_essImage X := ⟨⟨X⟩,⟨Iso.refl X⟩⟩
noncomputable abbrev posDiagramInclusion (I : Type) [Preorder I] :=
  InducedMonoidal.inclusion (diagramInclusion W I)
noncomputable instance posDiagramInclusionMonoidal (I : Type) [Preorder I] :
    (posDiagramInclusion W I).Monoidal := InducedMonoidal.inclusionMonoidal (diagramInclusion W I)
noncomputable instance posDiagramInclusionBraided (I : Type) [Preorder I] :
    (posDiagramInclusion W I).Braided := InducedMonoidal.inclusionBraided (diagramInclusion W I)
noncomputable instance posDiagramInclusionEssSurj (n : ℕ) :
    (posDiagramInclusion W (Fin (n+1))).EssSurj where
  mem_essImage X := ⟨(diagramInclusion W (Fin (n+1))).objPreimage X,
    ⟨(diagramInclusion W (Fin (n+1))).objObjPreimageIso X⟩⟩
noncomputable instance posDiagramInclusionEquivalence (n : ℕ) :
    (posDiagramInclusion W (Fin (n+1))).IsEquivalence where
  full := inferInstanceAs (inducedFunctor _).Full
  faithful := inferInstanceAs (inducedFunctor _).Faithful
noncomputable def posDiagramTripleHomologyIso (n j : ℕ) :
    (bar₃ (C:=PosDiagrams W (Fin (n+1)))).homology DiagonalResolution.Z j ≅
      (bar₃ (C:=Diagram C (Fin (n+1)))).homology DiagonalResolution.Z j := by
  have homologyIso := bar₃Map_homology_isIso (posDiagramInclusion W (Fin (n+1))) j
  exact asIso (SSet.homologyMap (bar₃Map (posDiagramInclusion W (Fin (n+1)))) DiagonalResolution.Z j)
end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
open IntervalBar IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I : Type} [Preorder I]
omit [Fact W.StableUnderInverse] in
@[simp] lemma reindex_η {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) :
    Functor.OplaxMonoidal.η (reindex W u)=𝟙 _ := rfl
omit [Fact W.StableUnderInverse] in
@[simp] lemma reindex_μ {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) (A B : Strings W m) :
    Functor.LaxMonoidal.μ (reindex W u) A B=𝟙 _ := rfl
lemma map_strings_reindex_id (n : ℕ) :
    Diagram.map (I:=I) (reindex W (𝟭 (Fin (n+1))))=𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq rfl ?_ ?_
    · apply heq_of_eq; funext i
      apply Iso.ext; apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      simp [mapObj]
      erw [Category.comp_id]
      rfl
    · apply heq_of_eq; funext i j k hij hjk
      apply Iso.ext; apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      simp [mapObj]
      erw [Category.id_comp]
      rfl
  · intro A B f
    apply Hom.ext; intro i j h
    erw [comp_app, comp_app, Diagram.eqToHom_app, Diagram.eqToHom_app]
    simp only [Diagram.map]
    erw [Category.id_comp, Category.comp_id]
    apply WideSubcategory.hom_ext; rfl
lemma map_strings_reindex_comp {n m k : ℕ} (u : Fin (n+1) ⥤ Fin (m+1))
    (v : Fin (m+1) ⥤ Fin (k+1)) :
    Diagram.map (I:=I) (reindex W (u ⋙ v)) =
      Diagram.map (reindex W v) ⋙ Diagram.map (reindex W u) := by
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq rfl ?_ ?_
    · apply heq_of_eq; funext i
      apply Iso.ext; apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      simp [mapObj]
      change (A.unit i).hom.hom.app (v.obj (u.obj t)) ≫ 𝟙 _ =
        (A.unit i).hom.hom.app (v.obj (u.obj t)) ≫ (𝟙 _ ≫ 𝟙 _)
      simp only [Category.comp_id]
    · apply heq_of_eq; funext i j k hij hjk
      apply Iso.ext; apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      simp [mapObj]
      change 𝟙 _ ≫ (A.cut i j k hij hjk).hom.hom.app (v.obj (u.obj t)) =
        𝟙 _ ≫ 𝟙 _ ≫ (A.cut i j k hij hjk).hom.hom.app (v.obj (u.obj t))
      simp only [Category.id_comp]
  · intro A B f
    apply Hom.ext; intro i j h
    erw [comp_app, comp_app, Diagram.eqToHom_app, Diagram.eqToHom_app]
    simp only [Diagram.map]
    erw [Category.id_comp, Category.comp_id]
    apply WideSubcategory.hom_ext; rfl
noncomputable def diagramHorizontal : SimplicialObject Cat.{0,0} where
  obj p := Cat.of (Diagram (Strings W p.unop.len) I)
  map f := (Diagram.map (reindex W f.unop.toOrderHom.toFunctor)).toCatHom
  map_id p := by apply Cat.ext; exact map_strings_reindex_id W _
  map_comp f g := by apply Cat.ext; exact map_strings_reindex_comp (I:=I) W g.unop.toOrderHom.toFunctor f.unop.toOrderHom.toFunctor
@[simp] lemma eqToHom_transposed_app {n : ℕ} {A B : Strings (diagramProperty W I) n}
    (e : A=B) (t : Fin (n+1)) (i j : I) (h : i≤j) :
    ((eqToHom e).hom.app t).hom.app i j h =
      eqToHom (congrArg (fun A : Strings (diagramProperty W I) n => ((diagramInclusion W I).obj (A.obj.obj t)).obj i j h) e) := by
  cases e; rfl
private lemma transposed_comp_app {n : ℕ}
    {A B D : Strings (diagramProperty W I) n} (f : A ⟶ B) (g : B ⟶ D)
    (t : Fin (n+1)) (i j : I) (h : i ≤ j) :
    ((f ≫ g).hom.app t).hom.app i j h =
      (f.hom.app t).hom.app i j h ≫ (g.hom.app t).hom.app i j h := rfl

private lemma eqToHom_vertex_app {A B : PosDiagrams W I} (e : A = B)
    (i j : I) (h : i ≤ j) :
    (eqToHom e).hom.app i j h =
      eqToHom (congrArg (fun A : PosDiagrams W I =>
        ((diagramInclusion W I).obj A).obj i j h) e) := by
  cases e
  rfl

private lemma stringVertex_reindex {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1))
    (A : Diagram (Strings W m) I) (t : Fin (n+1)) :
    stringVertex W ((Diagram.map (reindex W u)).obj A) t = stringVertex W A (u.obj t) := by
  refine ext_heq rfl ?_ ?_
  · apply heq_of_eq; funext i
    apply Iso.ext; apply WideSubcategory.hom_ext
    change (A.unit i).hom.hom.app (u.obj t) ≫ 𝟙 _ = _
    exact Category.comp_id _
  · apply heq_of_eq; funext i j k hij hjk
    apply Iso.ext; apply WideSubcategory.hom_ext
    change 𝟙 _ ≫ (A.cut i j k hij hjk).hom.hom.app (u.obj t) = _
    exact Category.id_comp _

private lemma transpose_reindex {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) :
    Diagram.map (I:=I) (reindex W u) ⋙ transposeDiagram W n =
      transposeDiagram W m ⋙ reindex (diagramProperty W I) u := by
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · apply WideSubcategory.ext
    refine CategoryTheory.Functor.ext (fun t => stringVertex_reindex W u A t) ?_
    intro t s g
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    erw [comp_app, comp_app, eqToHom_vertex_app, eqToHom_vertex_app]
    change (A.obj i j h).obj.map (u.map g) =
      𝟙 _ ≫ (A.obj i j h).obj.map (u.map g) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  · intro A B g
    apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    erw [transposed_comp_app, transposed_comp_app,
      eqToHom_transposed_app, eqToHom_transposed_app]
    change (g.app i j h).hom.app (u.obj t) =
      𝟙 _ ≫ (g.app i j h).hom.app (u.obj t) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]

noncomputable def diagramTranspose : diagramHorizontal (I:=I) W ⟶ horizontal (diagramProperty W I) where
  app p := (transposeDiagram W p.unop.len).toCatHom
  naturality p q f := by
    apply Cat.ext
    exact transpose_reindex W f.unop.toOrderHom.toFunctor

noncomputable def diagramResolutionHomologyIso (p j : ℕ) :
    (SimplicialDiagonal.nerveDiagonal.obj (diagramHorizontal (I:=Fin (p+1)) W)).homology DiagonalResolution.Z j ≅
      (nerve (Diagram C (Fin (p+1)))).homology DiagonalResolution.Z j := by
  have transposeHomologyIso := SimplicialDiagonal.nerveDiagonal_isIso (diagramTranspose (I:=Fin (p+1)) W)
    (fun q => inferInstanceAs (transposeDiagram (I:=Fin (p+1)) W q.unop.len).IsEquivalence) j
  have inclusionHomologyIso := NerveHomotopy.homologyMap_isIso (posDiagramInclusion W (Fin (p+1))) DiagonalResolution.Z j
  exact asIso (SSet.homologyMap (SimplicialDiagonal.nerveDiagonal.map (diagramTranspose (I:=Fin (p+1)) W)) DiagonalResolution.Z j) ≪≫
    homologyIso (diagramProperty W (Fin (p+1))) j ≪≫
    asIso (SSet.homologyMap (nerveMap (posDiagramInclusion W (Fin (p+1)))) DiagonalResolution.Z j)
end

end RestrictedNerve

end OAI
