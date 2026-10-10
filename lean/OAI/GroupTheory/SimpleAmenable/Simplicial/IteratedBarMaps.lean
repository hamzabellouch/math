import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.IntervalEquivalence

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace IntervalBar.Diagram

variable {C D : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
  [Groupoid.{0} D] [MonoidalCategory D] [SymmetricCategory D]
variable {I J K L : Type} [Preorder I] [Preorder J] [Preorder K] [Preorder L]
lemma simplicialMap_map_reindex (F : C ⥤ D) [F.Braided] (f : I →o J) :
    simplicialMap (map (I:=J) F) ≫ simplicialMap (reindex f) =
      simplicialMap (reindex f) ≫ simplicialMap (map (I:=I) F) := by
  apply NatTrans.ext; funext p; apply Cat.ext
  exact map_map_reindex F f
lemma barMap_map_reindex (F : C ⥤ D) [F.Braided] (f : I →o J) :
    barMap (map (I:=J) F) ≫ barMap (reindex f) =
      barMap (reindex f) ≫ barMap (map (I:=I) F) := by
  have h := congrArg (SimplicialDiagonal.nerveDiagonal.map) (simplicialMap_map_reindex F f)
  erw [Functor.map_comp, Functor.map_comp] at h
  exact h
noncomputable def rows₂Map (F : C ⥤ D) [F.Braided] : rows₂ (C:=C) ⟶ rows₂ (C:=D) where
  app p := barMap (map (I:=Fin (p.unop.len+1)) F)
  naturality _ _ f := (barMap_map_reindex F f.unop.toOrderHom).symm
noncomputable def bar₂Map (F : C ⥤ D) [F.Braided] : bar₂ (C:=C) ⟶ bar₂ (C:=D) :=
  SimplicialDiagonal.diagonal.map (rows₂Map F)
lemma bar₂Map_homology_isIso (F : C ⥤ D) [F.Braided] [F.IsEquivalence] (n : ℕ) :
    IsIso (SSet.homologyMap (bar₂Map F) DiagonalResolution.Z n) := by
  apply SimplicialDiagonal.homologyMap_isIso
  intro p q
  exact barMap_homology_isIso (map (I:=Fin (p.unop.len+1)) F) q
@[simp] lemma map_map_reindex_id :
    map (I:=K) (map (I:=J) (reindex (C:=C) (OrderHom.id (α:=I))))=𝟭 _ := by
  have he (X : Diagram (Diagram C I) J) : mapObj (reindex (OrderHom.id (α:=I))) X=X :=
    congrArg (fun F => F.obj X) map_reindex_id
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq ?_ ?_ ?_
    · funext i j h
      exact congrArg (fun F => F.obj (A.obj i j h)) map_reindex_id
    · apply hfunext; intro i
      apply iso_hext (he _) rfl
      apply hom_hext (he _) rfl
      intro j k h
      apply hom_hext (by simp [mapObj]) (by rfl)
      intro l m hlm
      apply heq_of_eq
      change (((map (reindex (C:=C) (OrderHom.id (α:=I)))).map (A.unit i).hom ≫
        Functor.OplaxMonoidal.η (map (reindex (C:=C) (OrderHom.id (α:=I))))).app j k h).app l m hlm = _
      erw [comp_app, map_η_app (I:=J) (reindex (C:=C) (OrderHom.id (α:=I)))]
      change ((A.unit i).hom.app j k h).app l m hlm ≫ 𝟙 _ = _
      exact Category.comp_id _
    · apply hfunext; intro i
      apply hfunext; intro j
      apply hfunext; intro k
      apply hfunext; intro hij
      apply hfunext; intro hjk
      apply iso_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _) (he _)) (he _)
      apply hom_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _) (he _)) (he _)
      intro l m hlm
      apply hom_hext (by simp [mapObj]) (by simp [mapObj])
      intro n p hnp
      apply heq_of_eq
      change 𝟙 _ ≫ ((A.cut i j k hij hjk).hom.app l m hlm).app n p hnp = _
      exact Category.id_comp _
  · intro A B f
    apply Hom.ext; intro i j h
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    apply Hom.ext; intro k l hkl
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    apply Hom.ext; intro m n hmn
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    simp only [map,reindex]
    erw [Category.id_comp, Category.comp_id]
    rfl
end IntervalBar.Diagram

end OAI
