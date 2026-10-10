import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.TripleComposition
import OAI.GroupTheory.SimpleAmenable.Configurations.PointFiberEvaluation
import OAI.GroupTheory.SimpleAmenable.Configurations.LabelTranslation

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Classical
namespace SimpleAmenable.PolygonObject.Labelled.PointFiber

variable {a n : ℕ} (d : (Fin n → CutRing × CutRing) → CutRing × CutRing)
variable (c : GenericSquare a × (Fin n → CutRing × CutRing))
noncomputable def backPoint : GenericSquare a × (Fin n → CutRing × CutRing) :=
  (SimpleAmenable.translate a (-d c.2) c.1,c.2)
lemma translated_predicate (U : Labelled a n) (x : U.polygon.Point) :
    (x.val.2=(backPoint d c).1 ∧ U.label x.val.1=(backPoint d c).2) ↔
      (((translateArrow d U).toEquiv x).val.2=c.1 ∧
        (translateObj d U).label ((translateArrow d U).toEquiv x).val.1=c.2) := by
  change (x.val.2=SimpleAmenable.translate a (-d c.2) c.1 ∧ U.label x.val.1=c.2) ↔
    (SimpleAmenable.translate a (d (U.label x.val.1)) x.val.2=c.1 ∧ U.label x.val.1=c.2)
  constructor
  · rintro ⟨hp,hl⟩
    refine ⟨?_,hl⟩
    rw [hl,hp,←SimpleAmenable.translate_add,add_neg_cancel,SimpleAmenable.translate_zero]
  · rintro ⟨hp,hl⟩
    refine ⟨?_,hl⟩
    rw [hl] at hp
    apply (translation a (d c.2)).injective
    change SimpleAmenable.translate a (d c.2) x.val.2 = _
    rw [hp]
    change _ = SimpleAmenable.translate a (d c.2) (SimpleAmenable.translate a (-d c.2) c.1)
    rw [←SimpleAmenable.translate_add,add_neg_cancel,SimpleAmenable.translate_zero]
noncomputable def translateFiber (U : Labelled a n) :
    Fiber U (backPoint d c) ≃ Fiber (translateObj d U) c :=
  (translateArrow d U).toEquiv.subtypeEquiv (translated_predicate d c U)
@[simp] lemma translateFiber_val (U : Labelled a n) (x : Fiber U (backPoint d c)) :
    (translateFiber d c U x).val=(translateArrow d U).toEquiv x.val := rfl
lemma translateFiber_natural {U V : Labelled a n} (f : U ⟶ V)
    (x : Fiber U (backPoint d c)) :
    translateFiber d c V (fiberMap f (backPoint d c) x) =
      fiberMap (translateHom d f) c (translateFiber d c U x) := by
  apply Subtype.ext
  change (translateArrow d V).toEquiv (f.arrow.toEquiv x.val) =
    (inv (translateArrow d U) ≫ f.arrow ≫ translateArrow d V).toEquiv
      ((translateArrow d U).toEquiv x.val)
  simp only [arrow_comp_apply,inv_arrow_apply,Equiv.symm_apply_apply]
noncomputable def translationEvaluationIso :
    evaluation ⋙ BarFinitePower.project _ (backPoint d c) ≅
      translateFunctor d ⋙ evaluation ⋙ BarFinitePower.project _ c :=
  NatIso.ofComponents (fun U => asIso (X := E.obj U (backPoint d c))
    (Y := E.obj (translateObj d U) c)
    ((enumerate U (backPoint d c)).symm.trans ((translateFiber d c U).trans
      (enumerate (translateObj d U) c)))) (by
    intro U V f
    apply Equiv.ext; intro x
    obtain ⟨x,rfl⟩ := (enumerate U (backPoint d c)).surjective x
    change enumerate (translateObj d V) c (translateFiber d c V
      ((enumerate V (backPoint d c)).symm (E.map f (backPoint d c)
        (enumerate U (backPoint d c) x)))) = E.map (translateHom d f) c
      (enumerate (translateObj d U) c (translateFiber d c U
        ((enumerate U (backPoint d c)).symm (enumerate U (backPoint d c) x))))
    rw [E_map_enum,Equiv.symm_apply_apply,Equiv.symm_apply_apply,E_map_enum,translateFiber_natural])
@[simp] lemma translationEvaluationIso_enum (U : Labelled a n) (x : Fiber U (backPoint d c)) :
    (translationEvaluationIso d c).hom.app U (enumerate U (backPoint d c) x) =
      enumerate (translateObj d U) c (translateFiber d c U x) := by
  change enumerate (translateObj d U) c (translateFiber d c U
    ((enumerate U (backPoint d c)).symm (enumerate U (backPoint d c) x))) = _
  rw [Equiv.symm_apply_apply]
end SimpleAmenable.PolygonObject.Labelled.PointFiber

end

end OAI
