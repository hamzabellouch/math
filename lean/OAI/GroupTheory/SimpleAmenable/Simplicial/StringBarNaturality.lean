import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.Supplemental

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace SimplicialDiagonal
lemma diagonal_obj_map_apply (X : I ⥤ SSet) {n m : I} (f : n ⟶ m)
    (x : (diagonal.obj X).obj n) :
    (diagonal.obj X).map f x = (X.obj m).map f ((X.map f).app n x) := rfl
lemma diagonal_map_app_apply {X Y : I ⥤ SSet} (f : X ⟶ Y) (n : I)
    (x : (diagonal.obj X).obj n) :
    (diagonal.map f).app n x = (f.app n).app n x := rfl
lemma nerveDiagonal_obj_map_apply (X : I ⥤ Cat.{0,0}) {n m : I} (f : n ⟶ m)
    (x : (nerveDiagonal.obj X).obj n) :
    (nerveDiagonal.obj X).map f x =
      f.unop.toOrderHom.toFunctor ⋙ x ⋙ (X.map f).toFunctor := rfl
lemma nerveDiagonal_map_app_apply {X Y : I ⥤ Cat.{0,0}} (f : X ⟶ Y) (n : I)
    (x : (nerveDiagonal.obj X).obj n) :
    (nerveDiagonal.map f).app n x = x ⋙ (f.app n).toFunctor := rfl
end SimplicialDiagonal
namespace IntervalBar.Diagram
variable {C D : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
  [Groupoid.{0} D] [MonoidalCategory D] [SymmetricCategory D]
lemma bar₃Map_app_apply (F : C ⥤ D) [F.Braided] (n : SimplexCategoryᵒᵖ)
    (x : (bar₃ (C:=C)).obj n) :
    (bar₃Map F).app n x = x ⋙ map₃ F (Fin (n.unop.len+1)) := rfl
end IntervalBar.Diagram
namespace RestrictedNerve

open IntervalBar IntervalBar.Diagram
variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
lemma stringBarRows_map_app_apply {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (k : SimplexCategoryᵒᵖ) (x : ((stringBarRows W).obj n).obj k) :
    ((stringBarRows W).map f).app k x =
      x ⋙ Diagram.map₃ (reindex W (n:=m.unop.len) (m:=n.unop.len) f.unop.toOrderHom.toFunctor) (Fin (k.unop.len+1)) :=
  bar₃Map_app_apply _ _ _
lemma stringBarTotal_map_apply {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : (SimplicialDiagonal.diagonal.obj (stringBarRows W)).obj n) :
    (SimplicialDiagonal.diagonal.obj (stringBarRows W)).map f x =
      f.unop.toOrderHom.toFunctor ⋙ x ⋙
        Diagram.map₃ (reindex W (n:=m.unop.len) (m:=n.unop.len) f.unop.toOrderHom.toFunctor) (Fin (n.unop.len+1)) ⋙
          diagonalReindex f.unop.toOrderHom := by
  rfl

lemma outerResolutionRows_map_app_apply {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (k : SimplexCategoryᵒᵖ) (x : ((outerResolutionRows W).obj n).obj k) :
    ((outerResolutionRows W).map f).app k x =
      x ⋙ Diagram.reindex f.unop.toOrderHom := rfl

lemma middleResolutionRows_map_app_apply (r : ℕ) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (k : SimplexCategoryᵒᵖ) (x : ((middleResolutionRows W r).obj n).obj k) :
    ((middleResolutionRows W r).map f).app k x =
      x ⋙ Diagram.map (Diagram.reindex f.unop.toOrderHom) := rfl

lemma innerResolutionRows_map_app_apply (q r : ℕ) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (k : SimplexCategoryᵒᵖ) (x : ((innerResolutionRows W q r).obj n).obj k) :
    ((innerResolutionRows W q r).map f).app k x =
      x ⋙ Diagram.map (Diagram.map (Diagram.reindex f.unop.toOrderHom)) := rfl
lemma tripleDiagramHorizontal_map_apply (p q r : ℕ) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : (SimplicialDiagonal.nerveDiagonal.obj (tripleDiagramHorizontal W p q r)).obj n) :
    (SimplicialDiagonal.nerveDiagonal.obj (tripleDiagramHorizontal W p q r)).map f x =
      f.unop.toOrderHom.toFunctor ⋙ x ⋙
        Diagram.map
          (C:=Diagram (Diagram (Strings W n.unop.len) (Fin (p+1))) (Fin (q+1)))
          (D:=Diagram (Diagram (Strings W m.unop.len) (Fin (p+1))) (Fin (q+1)))
          (I:=Fin (r+1))
          (Diagram.map (C:=Diagram (Strings W n.unop.len) (Fin (p+1)))
            (D:=Diagram (Strings W m.unop.len) (Fin (p+1))) (I:=Fin (q+1))
          (Diagram.map (C:=Strings W n.unop.len) (D:=Strings W m.unop.len) (I:=Fin (p+1)) (reindex W (n:=m.unop.len) (m:=n.unop.len) f.unop.toOrderHom.toFunctor))) := rfl
lemma innerResolutionTotal_map_apply (q r : ℕ) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : (SimplicialDiagonal.diagonal.obj (innerResolutionRows W q r)).obj n) :
    (SimplicialDiagonal.diagonal.obj (innerResolutionRows W q r)).map f x =
      f.unop.toOrderHom.toFunctor ⋙ x ⋙
        Diagram.map
          (C:=Diagram (Diagram (Strings W n.unop.len) (Fin (n.unop.len+1))) (Fin (q+1)))
          (D:=Diagram (Diagram (Strings W n.unop.len) (Fin (m.unop.len+1))) (Fin (q+1)))
          (I:=Fin (r+1)) (Diagram.map (C:=Diagram (Strings W n.unop.len) (Fin (n.unop.len+1)))
          (D:=Diagram (Strings W n.unop.len) (Fin (m.unop.len+1))) (I:=Fin (q+1))
          (Diagram.reindex (C:=Strings W n.unop.len) f.unop.toOrderHom)) ⋙
          Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1))
            (Diagram.map (C:=Strings W n.unop.len) (D:=Strings W m.unop.len) (I:=Fin (m.unop.len+1)) (reindex W (n:=m.unop.len) (m:=n.unop.len) f.unop.toOrderHom.toFunctor))) := by
  rfl
lemma middleResolutionTotal_map_apply (r : ℕ) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : (SimplicialDiagonal.diagonal.obj (middleResolutionRows W r)).obj n) :
    (SimplicialDiagonal.diagonal.obj (middleResolutionRows W r)).map f x =
      f.unop.toOrderHom.toFunctor ⋙ x ⋙
        Diagram.map (C:=Diagram (Diagram (Strings W n.unop.len) (Fin (n.unop.len+1))) (Fin (n.unop.len+1)))
          (D:=Diagram (Diagram (Strings W n.unop.len) (Fin (n.unop.len+1))) (Fin (m.unop.len+1)))
          (I:=Fin (r+1)) (Diagram.reindex
          (C:=Diagram (Strings W n.unop.len) (Fin (n.unop.len+1))) f.unop.toOrderHom) ⋙
        Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (m.unop.len+1))
          (Diagram.reindex (C:=Strings W n.unop.len) f.unop.toOrderHom)) ⋙
          Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (m.unop.len+1))
            (Diagram.map (C:=Strings W n.unop.len) (D:=Strings W m.unop.len) (I:=Fin (m.unop.len+1)) (reindex W (n:=m.unop.len) (m:=n.unop.len) f.unop.toOrderHom.toFunctor))) := by
  rfl
lemma outerResolutionTotal_map_apply {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : (SimplicialDiagonal.diagonal.obj (outerResolutionRows W)).obj n) :
    (SimplicialDiagonal.diagonal.obj (outerResolutionRows W)).map f x =
      f.unop.toOrderHom.toFunctor ⋙ x ⋙
        Diagram.reindex (C:=Diagram (Diagram (Strings W n.unop.len)
          (Fin (n.unop.len+1))) (Fin (n.unop.len+1))) f.unop.toOrderHom ⋙
        Diagram.map (I:=Fin (m.unop.len+1)) (Diagram.reindex
          (C:=Diagram (Strings W n.unop.len) (Fin (n.unop.len+1))) f.unop.toOrderHom) ⋙
        Diagram.map (I:=Fin (m.unop.len+1)) (Diagram.map (I:=Fin (m.unop.len+1))
          (Diagram.reindex (C:=Strings W n.unop.len) f.unop.toOrderHom)) ⋙
          Diagram.map₃ (reindex W (n:=m.unop.len) (m:=n.unop.len) f.unop.toOrderHom.toFunctor) (Fin (m.unop.len+1)) := by
  rfl

noncomputable def stringBarTotalIso :
    SimplicialDiagonal.diagonal.obj (stringBarRows W) ≅
      SimplicialDiagonal.diagonal.obj (outerResolutionRows W) :=
  NatIso.ofComponents (stringBarTotalComponent W) (by
    intro n m f
    apply ConcreteCategory.hom_ext
    intro x
    change (SimplicialDiagonal.diagonal.obj (stringBarRows W)).map f x =
      (SimplicialDiagonal.diagonal.obj (outerResolutionRows W)).map f x
    erw [stringBarTotal_map_apply, outerResolutionTotal_map_apply]
    have h := map₃_diagonalReindex (reindex W (n:=m.unop.len) (m:=n.unop.len) f.unop.toOrderHom.toFunctor)
      f.unop.toOrderHom
    conv_rhs at h => rw [← reverseDiagonalReindex]
    exact congrArg (fun F => f.unop.toOrderHom.toFunctor ⋙ x ⋙ F) h)
noncomputable def stringBarAugmentation :
    SimplicialDiagonal.diagonal.obj (stringBarRows W) ⟶ bar₃ (C:=C) :=
  (stringBarTotalIso W).hom ≫ totalStringToBar W
noncomputable instance stringBarAugmentation_isIso (j:ℕ) :
    IsIso (SSet.homologyMap (stringBarAugmentation W) DiagonalResolution.Z j) := by
  unfold stringBarAugmentation
  rw [SSet.homologyMap_comp]
  have totalAugmentationIso := totalStringToBar_isIso W j
  infer_instance
end RestrictedNerve

namespace SimpleAmenable.PolygonObject
open _root_.CategoryTheory _root_.OAI.CategoryTheory

noncomputable def stringBarAugmentation (a:ℕ) :
    SimplicialDiagonal.diagonal.obj
      (RestrictedNerve.stringBarRows (positionalProperty a)) ⟶
        IntervalBar.Diagram.bar₃ (C:=PolygonObject a) :=
  RestrictedNerve.stringBarAugmentation (positionalProperty a)
noncomputable instance stringBarAugmentation_isIso (a j:ℕ) :
    IsIso (SSet.homologyMap (stringBarAugmentation a) DiagonalResolution.Z j) :=
  RestrictedNerve.stringBarAugmentation_isIso (positionalProperty a) j
end SimpleAmenable.PolygonObject

end OAI
