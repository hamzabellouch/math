import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.TranslationFiber
import OAI.GroupTheory.SimpleAmenable.Simplicial.PointFiberMonoidal

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Classical
namespace SimpleAmenable.PolygonObject.Labelled.PointFiber

variable {a n : ℕ} (d : (Fin n → CutRing × CutRing) → CutRing × CutRing)
variable (c : GenericSquare a × (Fin n → CutRing × CutRing))
lemma translationFiber_sum_left (U V : Labelled a n) (x : Fiber U (backPoint d c)) :
    fiberMap (translationTensor d U V) c
      (fiberSum (translateObj d U) (translateObj d V) c (.inl (translateFiber d c U x))) =
    translateFiber d c (U⊗V) (fiberSum U V (backPoint d c) (.inl x)) := by
  apply Subtype.ext
  change (inv (sumArrow (translateArrow d U) (translateArrow d V)) ≫ translateArrow d (U⊗V)).toEquiv
    (sumPointEquiv _ _ (.inl ((translateArrow d U).toEquiv x.val))) = _
  rw [←sumArrow_inl,arrow_comp_apply,inv_arrow_apply,Equiv.symm_apply_apply]
  rfl
lemma translationFiber_sum_right (U V : Labelled a n) (x : Fiber V (backPoint d c)) :
    fiberMap (translationTensor d U V) c
      (fiberSum (translateObj d U) (translateObj d V) c (.inr (translateFiber d c V x))) =
    translateFiber d c (U⊗V) (fiberSum U V (backPoint d c) (.inr x)) := by
  apply Subtype.ext
  change (inv (sumArrow (translateArrow d U) (translateArrow d V)) ≫ translateArrow d (U⊗V)).toEquiv
    (sumPointEquiv _ _ (.inr ((translateArrow d V).toEquiv x.val))) = _
  rw [←sumArrow_inr,arrow_comp_apply,inv_arrow_apply,Equiv.symm_apply_apply]
  rfl
lemma translationEvaluation_tensor_left (U V : Labelled a n) (x : Fin (E.obj U (backPoint d c)).size) :
    (translationEvaluationIso d c).hom.app (U⊗V)
      (mu U V (backPoint d c) (FiniteSetGroupoid.sumEquiv _ _ (.inl x))) =
      E.map (translationTensor d U V) c (mu (translateObj d U) (translateObj d V) c
        (FiniteSetGroupoid.sumHom ((translationEvaluationIso d c).hom.app U)
          ((translationEvaluationIso d c).hom.app V) (FiniteSetGroupoid.sumEquiv _ _ (.inl x)))) := by
  obtain ⟨x,rfl⟩ := (enumerate U (backPoint d c)).surjective x
  erw [mu_inl,translationEvaluationIso_enum,FiniteSetGroupoid.sumHom_inl,
    translationEvaluationIso_enum,mu_inl,E_map_enum,translationFiber_sum_left]
  rfl
lemma translationEvaluation_tensor_right (U V : Labelled a n) (x : Fin (E.obj V (backPoint d c)).size) :
    (translationEvaluationIso d c).hom.app (U⊗V)
      (mu U V (backPoint d c) (FiniteSetGroupoid.sumEquiv _ _ (.inr x))) =
      E.map (translationTensor d U V) c (mu (translateObj d U) (translateObj d V) c
        (FiniteSetGroupoid.sumHom ((translationEvaluationIso d c).hom.app U)
          ((translationEvaluationIso d c).hom.app V) (FiniteSetGroupoid.sumEquiv _ _ (.inr x)))) := by
  obtain ⟨x,rfl⟩ := (enumerate V (backPoint d c)).surjective x
  erw [mu_inr,translationEvaluationIso_enum,FiniteSetGroupoid.sumHom_inr,
    translationEvaluationIso_enum,mu_inr,E_map_enum,translationFiber_sum_right]
  rfl
noncomputable instance translationEvaluationIsoMonoidal :
    NatTrans.IsMonoidal (translationEvaluationIso d c).hom where
  unit := by apply Equiv.ext; intro x; exact Fin.elim0 x
  tensor U V := by
    apply Equiv.ext; intro x
    change (translationEvaluationIso d c).hom.app (U⊗V) (mu U V (backPoint d c) x) =
      E.map (translationTensor d U V) c (mu (translateObj d U) (translateObj d V) c
        (FiniteSetGroupoid.sumHom ((translationEvaluationIso d c).hom.app U)
          ((translationEvaluationIso d c).hom.app V) x))
    obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv (E.obj U (backPoint d c))
      (E.obj V (backPoint d c))).surjective x
    cases x with
    | inl x => exact translationEvaluation_tensor_left d c U V x
    | inr x => exact translationEvaluation_tensor_right d c U V x
end SimpleAmenable.PolygonObject.Labelled.PointFiber

end

end OAI
