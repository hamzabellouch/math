import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.MonoidalCongruence
import OAI.GroupTheory.SimpleAmenable.Simplicial.DiagramResolutionNatural

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve

open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I J K:Type} [Preorder I] [Preorder J] [Preorder K]
omit [Fact W.StableUnderInverse] in
@[simp] lemma inclusion_η : Functor.OplaxMonoidal.η (inclusion W) = 𝟙 _ := rfl
omit [Fact W.StableUnderInverse] in
@[simp] lemma inclusion_μ (A B:WideSubcategory W) :
    Functor.LaxMonoidal.μ (inclusion W) A B = 𝟙 _ := rfl
@[simp] lemma widePosReindex_η (u:I→oJ) :
    Functor.OplaxMonoidal.η (widePosReindex W u) = 𝟙 _ := rfl
@[simp] lemma widePosReindex_μ (u:I→oJ) (A B:WideSubcategory (diagramProperty W J)) :
    Functor.LaxMonoidal.μ (widePosReindex W u) A B = 𝟙 _ := rfl
@[simp] lemma posReindex_η (u:I→oJ) :
    Functor.OplaxMonoidal.η (posReindex W u) = 𝟙 _ := rfl
@[simp] lemma posReindex_μ (u:I→oJ) (A B:PosDiagrams W J) :
    Functor.LaxMonoidal.μ (posReindex W u) A B = 𝟙 _ := rfl
@[simp] lemma eqToHom_pos_app {A B:PosDiagrams W I} (e:A=B) (i j:I) (h:i≤j) :
    (eqToHom e).hom.app i j h =
      eqToHom (congrArg (fun A:PosDiagrams W I=>((diagramInclusion W I).obj A).obj i j h) e) := by
  cases e; rfl
noncomputable def nestedPosReindex (u:I→oJ) :
    PosDiagrams (diagramProperty W J) K ⥤ PosDiagrams (diagramProperty W I) K where
  obj A := (Diagram.map (I:=K) (widePosReindex W u)).obj A
  map {A B} f := InducedCategory.homMk {
    app i j h := (posReindex W u).map (f.hom.app i j h)
    unit i := by
      apply InducedCategory.hom_ext; apply Hom.ext; intro x y h
      have he := congrArg (fun z => z.hom.app (u x) (u y) (u.monotone h)) (f.hom.unit i)
      change (f.hom.app i i (le_refl i)).hom.app (u x) (u y) (u.monotone h) ≫
          ((B.unit i).hom.hom.hom.app (u x) (u y) (u.monotone h) ≫ 𝟙 _) =
        (A.unit i).hom.hom.hom.app (u x) (u y) (u.monotone h) ≫ 𝟙 _ at he
      change (f.hom.app i i (le_refl i)).hom.app (u x) (u y) (u.monotone h) ≫
          (((B.unit i).hom.hom.hom.app (u x) (u y) (u.monotone h) ≫ 𝟙 _) ≫ 𝟙 _) =
        ((A.unit i).hom.hom.hom.app (u x) (u y) (u.monotone h) ≫ 𝟙 _) ≫ 𝟙 _
      simpa only [Category.comp_id] using he
    cut i j k hij hjk := by
      apply InducedCategory.hom_ext; apply Hom.ext; intro x y h
      have he := congrArg (fun z => z.hom.app (u x) (u y) (u.monotone h)) (f.hom.cut i j k hij hjk)
      change ((f.hom.app i j hij ⊗ₘ f.hom.app j k hjk).hom.app (u x) (u y) (u.monotone h)) ≫
          (𝟙 _ ≫ (B.cut i j k hij hjk).hom.hom.hom.app (u x) (u y) (u.monotone h)) =
        (𝟙 _ ≫ (A.cut i j k hij hjk).hom.hom.hom.app (u x) (u y) (u.monotone h)) ≫
          (f.hom.app i k (le_trans hij hjk)).hom.app (u x) (u y) (u.monotone h) at he
      erw [posTensor_app] at he
      change (((posReindex W u).map (f.hom.app i j hij) ⊗ₘ
          (posReindex W u).map (f.hom.app j k hjk)).hom.app x y h) ≫
          (𝟙 _ ≫ 𝟙 _ ≫ (B.cut i j k hij hjk).hom.hom.hom.app (u x) (u y) (u.monotone h)) =
        (𝟙 _ ≫ 𝟙 _ ≫ (A.cut i j k hij hjk).hom.hom.hom.app (u x) (u y) (u.monotone h)) ≫
          (f.hom.app i k (le_trans hij hjk)).hom.app (u x) (u y) (u.monotone h)
      erw [posTensor_app]
      simpa only [posReindex, Category.id_comp] using! he }
  map_id A := by
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    exact (posReindex W u).map_id _
  map_comp f g := by
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    exact (posReindex W u).map_comp _ _
lemma nestedPosReindex_property (u:I→oJ) {A B:PosDiagrams (diagramProperty W J) K} (f:A⟶B)
    (hf:diagramProperty (diagramProperty W J) K f) :
    diagramProperty (diagramProperty W I) K ((nestedPosReindex W u).map f) :=
  fun i j h => posReindex_property W u (f.hom.app i j h) (hf i j h)
private lemma nestedPosReindex_inclusion_obj (u:I→oJ) (A:PosDiagrams (diagramProperty W J) K) :
    (nestedPosReindex (K:=K) W u ⋙ posDiagramInclusion (diagramProperty W I) K).obj A =
      (posDiagramInclusion (diagramProperty W J) K ⋙ Diagram.map (posReindex W u)).obj A := by
  refine ext_heq rfl ?_ ?_
  · apply heq_of_eq; funext i; apply Iso.ext
    apply InducedCategory.hom_ext; apply Hom.ext; intro x y h
    simp [nestedPosReindex,diagramInclusion,mapObj]
    simp [posReindex,widePosReindex]
    rfl
  · apply heq_of_eq; funext i j k hij hjk; apply Iso.ext
    apply InducedCategory.hom_ext; apply Hom.ext; intro x y h
    simp [nestedPosReindex,diagramInclusion,mapObj]
    simp [posReindex,widePosReindex]
    rfl

lemma nestedPosReindex_inclusion (u:I→oJ) :
    nestedPosReindex (K:=K) W u ⋙ posDiagramInclusion (diagramProperty W I) K =
      posDiagramInclusion (diagramProperty W J) K ⋙ Diagram.map (posReindex W u) := by
  refine CategoryTheory.Functor.ext (nestedPosReindex_inclusion_obj W u) ?_
  intro A B f
  apply Hom.ext; intro i j h
  apply InducedCategory.hom_ext; apply Hom.ext; intro x y hxy
  simp [nestedPosReindex,posReindex,Diagram.map]
  erw [Diagram.eqToHom_app, Diagram.eqToHom_app]
  erw [comp_app, comp_app, eqToHom_pos_app, eqToHom_pos_app]
  change (f.hom.app i j h).hom.app (u x) (u y) (u.monotone hxy) =
    𝟙 _ ≫ (f.hom.app i j h).hom.app (u x) (u y) (u.monotone hxy) ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

@[simp] lemma transpose_η_app (n:ℕ) (t:Fin (n+1)) (i j:I) (h:i≤j) :
    ((Functor.OplaxMonoidal.η (transposeDiagram (I:=I) W n)).hom.app t).hom.app i j h = 𝟙 _ := by
  have he := congrArg (fun z=> (z.hom.app t).hom.app i j h)
    (Functor.Monoidal.ε_η (transposeDiagram (I:=I) W n))
  change 𝟙 (𝟙_ C) ≫ ((Functor.OplaxMonoidal.η (transposeDiagram (I:=I) W n)).hom.app t).hom.app i j h = 𝟙 (𝟙_ C) at he
  change ((Functor.OplaxMonoidal.η (transposeDiagram (I:=I) W n)).hom.app t).hom.app i j h = 𝟙 (𝟙_ C)
  exact (Category.id_comp _).symm.trans he
@[simp] lemma transpose_obj (n:ℕ) (A:Diagram (Strings W n) I) :
    (transposeDiagram W n).obj A=transposeDiagramObj W A := rfl
@[simp] lemma transpose_map (n:ℕ) {A B:Diagram (Strings W n) I} (f:A⟶B) :
    (transposeDiagram W n).map f=transposeDiagramHom W f := rfl
@[simp] lemma diagramReindex_η (u:I→oJ) :
    Functor.OplaxMonoidal.η (Diagram.reindex (C:=C) u)=𝟙 _ := rfl
@[simp] lemma diagramReindex_μ (u:I→oJ) (A B:Diagram C J) :
    Functor.LaxMonoidal.μ (Diagram.reindex u) A B=𝟙 _ := rfl
private noncomputable abbrev innerReindexLeft (u:I→oJ) (n:ℕ) :=
    Diagram.map (I:=K) (Diagram.reindex (C:=Strings W n) u) ⋙
      Diagram.map (I:=K) (transposeDiagram (I:=I) W n) ⋙
        transposeDiagram (I:=K) (diagramProperty W I) n
private noncomputable abbrev innerReindexRight (u:I→oJ) (n:ℕ) :=
    Diagram.map (I:=K) (transposeDiagram (I:=J) W n) ⋙
      transposeDiagram (I:=K) (diagramProperty W J) n ⋙
        stringsMap (diagramProperty (diagramProperty W J) K) (diagramProperty (diagramProperty W I) K)
          (nestedPosReindex W u) (nestedPosReindex_property W u) n

private lemma doubleTranspose_innerReindex_vertex (u:I→oJ) (n:ℕ)
    (A:Diagram (Diagram (Strings W n) J) K) (t:Fin (n+1)) :
    (((innerReindexLeft (K:=K) W u n).obj A).obj.obj t) =
      (((innerReindexRight (K:=K) W u n).obj A).obj.obj t) := by
  refine ext_heq rfl ?_ ?_
  · apply heq_of_eq; funext i; apply Iso.ext; apply WideSubcategory.hom_ext
    apply InducedCategory.hom_ext; apply Hom.ext; intro x y h
    simp [stringsMap,nestedPosReindex,transposeDiagramObj,stringVertex,mapObj]
    simp [widePosReindex,posReindex,Diagram.reindex]
    erw [comp_app, transpose_η_app]
    change (((A.unit i).hom.app (u x) (u y) (u.monotone h)).hom.app t ≫ 𝟙 _) ≫ 𝟙 _ =
      (((A.unit i).hom.app (u x) (u y) (u.monotone h)).hom.app t ≫
        ((Functor.OplaxMonoidal.η (transposeDiagram (I:=J) W n)).hom.app t).hom.app
          (u x) (u y) (u.monotone h)) ≫ 𝟙 _
    rw [transpose_η_app]
    rfl
  · apply heq_of_eq; funext i j k hij hjk; apply Iso.ext; apply WideSubcategory.hom_ext
    apply InducedCategory.hom_ext; apply Hom.ext; intro x y h
    simp [stringsMap,nestedPosReindex,transposeDiagramObj,stringVertex,mapObj]
    simp [widePosReindex,posReindex,Diagram.reindex]
    change 𝟙 _ ≫ 𝟙 _ ≫ ((A.cut i j k hij hjk).hom.app (u x) (u y) (u.monotone h)).hom.app t =
      𝟙 _ ≫ 𝟙 _ ≫ ((A.cut i j k hij hjk).hom.app (u x) (u y) (u.monotone h)).hom.app t
    simp

private lemma nested_comp_app {A B D:PosDiagrams (diagramProperty W I) K}
    (f:A⟶B) (g:B⟶D) (i j:K) (h:i≤j) (x y:I) (hxy:x≤y) :
    ((f ≫ g).hom.app i j h).hom.app x y hxy =
      (f.hom.app i j h).hom.app x y hxy ≫ (g.hom.app i j h).hom.app x y hxy := rfl

private lemma nested_eqToHom_app {A B:PosDiagrams (diagramProperty W I) K}
    (e:A=B) (i j:K) (h:i≤j) (x y:I) (hxy:x≤y) :
    ((eqToHom e).hom.app i j h).hom.app x y hxy =
      eqToHom (congrArg (fun A:PosDiagrams (diagramProperty W I) K =>
        ((diagramInclusion W I).obj (A.obj i j h).obj).obj x y hxy) e) := by
  cases e
  rfl

private lemma twiceTransposed_comp_app {n:ℕ}
    {A B D:Strings (diagramProperty (diagramProperty W I) K) n}
    (f:A⟶B) (g:B⟶D) (t:Fin (n+1)) (i j:K) (h:i≤j) (x y:I) (hxy:x≤y) :
    (((f ≫ g).hom.app t).hom.app i j h).hom.app x y hxy =
      ((f.hom.app t).hom.app i j h).hom.app x y hxy ≫
        ((g.hom.app t).hom.app i j h).hom.app x y hxy := rfl

private lemma twiceTransposed_eqToHom_app {n:ℕ}
    {A B:Strings (diagramProperty (diagramProperty W I) K) n}
    (e:A=B) (t:Fin (n+1)) (i j:K) (h:i≤j) (x y:I) (hxy:x≤y) :
    (((eqToHom e).hom.app t).hom.app i j h).hom.app x y hxy =
      eqToHom (congrArg (fun A:Strings (diagramProperty (diagramProperty W I) K) n =>
        (((A.obj.obj t).obj i j h).obj.obj x y hxy).obj) e) := by
  cases e
  rfl

private lemma doubleTranspose_innerReindex_obj (u:I→oJ) (n:ℕ)
    (A:Diagram (Diagram (Strings W n) J) K) :
    (innerReindexLeft (K:=K) W u n).obj A = (innerReindexRight (K:=K) W u n).obj A := by
  apply WideSubcategory.ext
  refine CategoryTheory.Functor.ext (doubleTranspose_innerReindex_vertex W u n A) ?_
  intro t s f
  apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
  apply InducedCategory.hom_ext; apply Hom.ext; intro x y hxy
  erw [nested_comp_app, nested_comp_app, nested_eqToHom_app, nested_eqToHom_app]
  change ((A.obj i j h).obj (u x) (u y) (u.monotone hxy)).obj.map f =
    𝟙 _ ≫ ((A.obj i j h).obj (u x) (u y) (u.monotone hxy)).obj.map f ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

private lemma twiceTransposed_transport_ext {n:ℕ}
    {A A' B B':Strings (diagramProperty (diagramProperty W I) K) n}
    (eA:A=A') (eB:B'=B) (f:A⟶B) (g:A'⟶B')
    (hf:∀ (t:Fin (n+1)) (i j:K) (h:i≤j) (x y:I) (hxy:x≤y),
      ((f.hom.app t).hom.app i j h).hom.app x y hxy =
        eqToHom (congrArg (fun A:Strings (diagramProperty (diagramProperty W I) K) n =>
          (((A.obj.obj t).obj i j h).obj.obj x y hxy).obj) eA) ≫
        ((g.hom.app t).hom.app i j h).hom.app x y hxy ≫
        eqToHom (congrArg (fun A:Strings (diagramProperty (diagramProperty W I) K) n =>
          (((A.obj.obj t).obj i j h).obj.obj x y hxy).obj) eB)) :
    f = eqToHom eA ≫ g ≫ eqToHom eB := by
  apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
  apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
  apply InducedCategory.hom_ext; apply Hom.ext; intro x y hxy
  erw [twiceTransposed_comp_app, twiceTransposed_comp_app,
    twiceTransposed_eqToHom_app, twiceTransposed_eqToHom_app]
  exact hf t i j h x y hxy

private lemma doubleTranspose_innerReindex_eq (u:I→oJ) (n:ℕ) :
    innerReindexLeft (K:=K) W u n = innerReindexRight (K:=K) W u n := by
  refine CategoryTheory.Functor.ext (doubleTranspose_innerReindex_obj W u n) ?_
  intro A B f
  apply twiceTransposed_transport_ext
  intro t i j h x y hxy
  change ((f.app i j h).app (u x) (u y) (u.monotone hxy)).hom.app t =
    𝟙 _ ≫ ((f.app i j h).app (u x) (u y) (u.monotone hxy)).hom.app t ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

lemma doubleTranspose_innerReindex (u:I→oJ) (n:ℕ) :
    Diagram.map (I:=K) (Diagram.reindex (C:=Strings W n) u) ⋙
      Diagram.map (I:=K) (transposeDiagram (I:=I) W n) ⋙
        transposeDiagram (I:=K) (diagramProperty W I) n =
    Diagram.map (I:=K) (transposeDiagram (I:=J) W n) ⋙
      transposeDiagram (I:=K) (diagramProperty W J) n ⋙
        stringsMap (diagramProperty (diagramProperty W J) K) (diagramProperty (diagramProperty W I) K)
          (nestedPosReindex W u) (nestedPosReindex_property W u) n := by
  exact doubleTranspose_innerReindex_eq W u n

end RestrictedNerve

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace IntervalBar.Diagram

variable {C D:Type} [Groupoid.{0} C] [Groupoid.{0} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [SymmetricCategory C] [SymmetricCategory D]
variable {I J K:Type} [Preorder I] [Preorder J] [Preorder K]
@[simp] lemma map_ε (F:C⥤D) [F.Braided] :
    Functor.LaxMonoidal.ε (map (I:=I) F)=mapεHom F := rfl
@[simp] lemma map_μ (F:C⥤D) [F.Braided] (A B:Diagram C I) :
    Functor.LaxMonoidal.μ (map F) A B=mapμHom F A B := rfl
@[simp] lemma reindex_ε (u:I→oJ) :
    Functor.LaxMonoidal.ε (reindex (C:=C) u)=𝟙 _ := rfl
@[simp] lemma reindex_μ (u:I→oJ) (A B:Diagram C J) :
    Functor.LaxMonoidal.μ (reindex u) A B=𝟙 _ := rfl
noncomputable instance reindex_map_monoidal (F:C⥤D) [F.Braided] (u:I→oJ) :
    NatTrans.IsMonoidal (eqToHom (reindex_map F u)) where
  unit := by
    apply Hom.ext; intro i j h
    simp only [CategoryTheory.eqToHom_app]
    simp only [Functor.LaxMonoidal.comp_ε,map_ε,reindex_ε]
    simp [mapεHom,map,reindex]
    erw [Diagram.eqToHom_app]
    change Functor.LaxMonoidal.ε F ≫ F.map (𝟙 (𝟙_ C)) ≫ 𝟙 _ = 𝟙 _ ≫ Functor.LaxMonoidal.ε F
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  tensor A B := by
    apply Hom.ext; intro i j h
    simp only [CategoryTheory.eqToHom_app]
    simp only [Functor.LaxMonoidal.comp_μ,map_μ,reindex_μ]
    simp [mapμHom,map,reindex]
    erw [Diagram.eqToHom_app, Diagram.eqToHom_app, Diagram.eqToHom_app]
    change Functor.LaxMonoidal.μ F (A.obj (u i) (u j) (u.monotone h)) (B.obj (u i) (u j) (u.monotone h)) ≫
      F.map (𝟙 _) ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ 𝟙 _ ≫
        Functor.LaxMonoidal.μ F (A.obj (u i) (u j) (u.monotone h)) (B.obj (u i) (u j) (u.monotone h))
    simp only [CategoryTheory.Functor.map_id, id_tensorHom_id, Category.id_comp, Category.comp_id]
lemma map_reindex_map (F:C⥤D) [F.Braided] (u:I→oJ) :
    map (I:=K) (reindex (C:=C) u) ⋙ map (I:=K) (map F) =
      map (I:=K) (map F) ⋙ map (I:=K) (reindex u) := by
  have he := map_congr (I:=K) (reindex_map F u) (reindex_map_monoidal F u)
  simpa only [map_comp] using he
end IntervalBar.Diagram

end OAI
