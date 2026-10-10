import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.PointFiberHomology
import OAI.GroupTheory.SimpleAmenable.Configurations.TranslationFiber
import OAI.GroupTheory.SimpleAmenable.Simplicial.TranslationFiberMonoidal

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Classical
namespace SimpleAmenable.PolygonObject.LabelledStage

variable {a n : ℕ} {K : Type} [AddCommGroup K]
noncomputable def stepTranslate (u : CutRing × CutRing) : BooleanStep a K →ₗ[ℤ] BooleanStep a K where
  toFun f := ⟨fun p => f.val (SimpleAmenable.translate a (-u) p),
    squareArrangement_translate f.property (-u)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
@[simp] lemma stepTranslate_apply (u : CutRing × CutRing) (f : BooleanStep a K) (p : GenericSquare a) :
    (stepTranslate (K:=K) u f).val p = f.val (SimpleAmenable.translate a (-u) p) := rfl
variable (d : (Fin n → CutRing × CutRing) → CutRing × CutRing)
noncomputable def translateCoefficients : Coefficients a n K →ₗ[ℤ] Coefficients a n K :=
  Finsupp.lsum ℤ (fun l : ReducedLabel n => (Finsupp.lsingle l).comp (stepTranslate (d l.val)))
@[simp] lemma translateCoefficients_single (l : ReducedLabel n) (s : BooleanStep a K) :
    translateCoefficients (K:=K) d (Finsupp.single l s)=
      Finsupp.single l (stepTranslate (K:=K) (d l.val) s) := Finsupp.lsum_single _ _ _ _
lemma translateCoefficients_at (f : Coefficients a n K) (l : ReducedLabel n) :
    translateCoefficients (K:=K) d f l=stepTranslate (K:=K) (d l.val) (f l) := by
  induction f using Finsupp.induction with
  | zero => simp
  | single_add k s f hk hs ih =>
    simp only [map_add,Finsupp.add_apply,ih]
    congr 1
    rw [translateCoefficients_single]
    by_cases h:k=l
    · subst l; simp only [Finsupp.single_eq_same]
    · simp only [Finsupp.single_eq_of_ne (Ne.symm h),map_zero]
end SimpleAmenable.PolygonObject.LabelledStage

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Classical
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar.Diagram BarFinitePower FreeChains Labelled

variable {a n : ℕ}
variable (d : (Fin n → CutRing × CutRing) → CutRing × CutRing)
lemma translation_evaluation_homology (j : ℕ)
    (c : GenericSquare a × (Fin n → CutRing × CutRing)) :
    SSet.homologyMap (bar₃Map (translateFunctor d ⋙ PointFiber.evaluation ⋙ project _ c)) Z j =
    SSet.homologyMap (bar₃Map (PointFiber.evaluation ⋙ project _ (SimpleAmenable.translate a (-d c.2) c.1,c.2))) Z j :=
  (bar₃Map_eq_of_monoidalNatTrans (PointFiber.translationEvaluationIso d c).hom j).symm
lemma homologyCoefficientIso_translate_point (j : ℕ) (hj : 0<j) (hj5 : j≤5)
    (c : GenericSquare a × ReducedLabel n) :
    SSet.homologyMap (bar₃Map (translateFunctor d)) Z j ≫
      (homologyCoefficientIso (a:=a) (n:=n) j hj hj5).hom ≫ ModuleCat.ofHom (pointValue c) =
    (homologyCoefficientIso (a:=a) (n:=n) j hj hj5).hom ≫
      ModuleCat.ofHom (pointValue (SimpleAmenable.translate a (-d c.2.val) c.1,c.2)) := by
  rw [homologyCoefficientIso_point,homologyCoefficientIso_point,
    ←SSet.homologyMap_comp,←bar₃Map_comp]
  exact translation_evaluation_homology d j (c.1,c.2.val)
lemma homologyCoefficientIso_translate (j : ℕ) (hj : 0<j) (hj5 : j≤5) :
    SSet.homologyMap (bar₃Map (translateFunctor d)) Z j ≫
      (homologyCoefficientIso (a:=a) (n:=n) j hj hj5).hom =
    (homologyCoefficientIso (a:=a) (n:=n) j hj hj5).hom ≫
      ModuleCat.ofHom (translateCoefficients (a:=a) (K:=K j) d) := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
  apply Finsupp.ext; intro l
  apply Subtype.ext; funext p
  have h := congrArg (fun k : (bar₃ (C:=Labelled a n)).homology Z j ⟶ K j => k x)
    (homologyCoefficientIso_translate_point d j hj hj5 (p,l))
  change _ = (translateCoefficients (a:=a) (K:=K j) d ((homologyCoefficientIso j hj hj5).hom x) l).val p
  rw [translateCoefficients_at,stepTranslate_apply]
  exact h
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end OAI
