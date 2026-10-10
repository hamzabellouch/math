import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.RelabelCoefficients
import OAI.GroupTheory.SimpleAmenable.Homology.TranslationCoefficients
import OAI.GroupTheory.SimpleAmenable.Simplicial.TrajectoryReindexLabels

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory
namespace SimpleAmenable.PolygonObject
noncomputable instance stringReindex_braided {a n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) :
    (stringReindex (a:=a) u).Braided where
  braided _ _ := by
    apply WideSubcategory.hom_ext
    ext i
    change 𝟙 _ ≫ (β_ _ _).hom = (β_ _ _).hom ≫ 𝟙 _
    simp
end SimpleAmenable.PolygonObject
namespace SimpleAmenable.PolygonObject.LabelledStage
open IntervalBar.Diagram BarFinitePower FreeChains Labelled

variable {a n m : ℕ} {K : Type} [AddCommGroup K]
noncomputable def reindexCoefficients (u : Fin (m+1) ⥤ Fin (n+1)) :
    Coefficients a n K →ₗ[ℤ] Coefficients a m K :=
  (relabelCoefficients (reindexLabel u) (reindexLabel_reduced u)).comp
    (translateCoefficients (initialDisplacement u))
lemma reindexCoefficients_single (u : Fin (m+1) ⥤ Fin (n+1))
    (l : ReducedLabel n) (s : BooleanStep a K) :
    reindexCoefficients (K:=K) u (Finsupp.single l s) =
      Finsupp.single (labelMap (reindexLabel u) (reindexLabel_reduced u) l)
        (stepTranslate (K:=K) (initialDisplacement u l.val) s) := by
  simp only [reindexCoefficients,LinearMap.comp_apply,translateCoefficients_single,
    relabelCoefficients_single]
namespace Stage
lemma homologyCoefficientIso_reindex (u : Fin (m+1) ⥤ Fin (n+1))
    (j : ℕ) (hj : 0<j) (hj5 : j≤5) :
    SSet.homologyMap (bar₃Map (reindexFunctor (a:=a) u)) Z j ≫
      (homologyCoefficientIso (a:=a) (n:=m) j hj hj5).hom =
    (homologyCoefficientIso (a:=a) (n:=n) j hj hj5).hom ≫
      ModuleCat.ofHom (reindexCoefficients (a:=a) (K:=Stage.K j) u) := by
  change SSet.homologyMap (bar₃Map (translateFunctor (initialDisplacement u) ⋙
      relabel (reindexLabel u) (reindexLabel_reduced u))) Z j ≫ _ = _
  rw [bar₃Map_comp,SSet.homologyMap_comp,Category.assoc,homologyCoefficientIso_relabel,
    ←Category.assoc,homologyCoefficientIso_translate,Category.assoc]
  rfl
end Stage
noncomputable def stringCoefficientIso (a n j : ℕ) (hj : 0<j) (hj5 : j≤5) :
    (bar₃ (C:=StringGroupoid a n)).homology Z j ≅
      ModuleCat.of ℤ (Coefficients a n (Stage.K j)) := by
  haveI := Labelled.tripleBar_homology_isIso (a:=a) (n:=n) j
  exact (asIso (SSet.homologyMap (bar₃Map (toStrings (a:=a) (n:=n))) Z j)).symm ≪≫
    Stage.homologyCoefficientIso j hj hj5
lemma toStrings_stringCoefficientIso (j : ℕ) (hj : 0<j) (hj5 : j≤5) :
    SSet.homologyMap (bar₃Map (toStrings (a:=a) (n:=n))) Z j ≫
      (stringCoefficientIso a n j hj hj5).hom =
    (Stage.homologyCoefficientIso j hj hj5).hom := by
  have tripleBarIso := Labelled.tripleBar_homology_isIso (a:=a) (n:=n) j
  change _ ≫ inv _ ≫ _ = _
  rw [IsIso.hom_inv_id_assoc]
lemma toStrings_reindex_homology (u : Fin (m+1) ⥤ Fin (n+1)) (j : ℕ) :
    SSet.homologyMap (bar₃Map (reindexFunctor (a:=a) u)) Z j ≫
      SSet.homologyMap (bar₃Map toStrings) Z j =
    SSet.homologyMap (bar₃Map toStrings) Z j ≫
      SSet.homologyMap (bar₃Map (stringReindex u)) Z j := by
  rw [←SSet.homologyMap_comp,←bar₃Map_comp,←SSet.homologyMap_comp,←bar₃Map_comp]
  exact bar₃Map_eq_of_monoidalNatTrans (reindexStringIso u).hom j
lemma stringCoefficientIso_reindex (u : Fin (m+1) ⥤ Fin (n+1))
    (j : ℕ) (hj : 0<j) (hj5 : j≤5) :
    SSet.homologyMap (bar₃Map (stringReindex (a:=a) u)) Z j ≫
      (stringCoefficientIso a m j hj hj5).hom =
    (stringCoefficientIso a n j hj hj5).hom ≫
      ModuleCat.ofHom (reindexCoefficients (a:=a) (K:=Stage.K j) u) := by
  have tripleBarIso := Labelled.tripleBar_homology_isIso (a:=a) (n:=n) j
  apply (cancel_epi (SSet.homologyMap (bar₃Map (toStrings (a:=a) (n:=n))) Z j)).mp
  rw [←Category.assoc,toStrings_reindex_homology u j |>.symm,Category.assoc,
    toStrings_stringCoefficientIso,←Category.assoc,toStrings_stringCoefficientIso]
  exact Stage.homologyCoefficientIso_reindex u j hj hj5
end SimpleAmenable.PolygonObject.LabelledStage

end

end OAI
