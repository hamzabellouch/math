import OAI.Algebra.Finitistic.Localization.PresentedActionCompatibility

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.QuadraticEncoding
universe u v w
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

theorem quotientAction_square (r : PresentedAlgebra P) :
    (boundedQuotientEvaluation X).map (quotientAction P r) ≫ (quotientVertexIso X 0).hom =
      (quotientVertexIso X 0).hom ≫ (vectorStalk (k := k)).map
        (liftedEndHom (givenAction X r)) := by
  have h := congrArg (fun f => (quotientVertexIso X 0).hom ≫ f)
    (AlgHom.congr_fun (quotientAction_evaluates X) r)
  change (quotientVertexIso X 0).hom ≫ ((quotientVertexIso X 0).inv ≫
    (boundedQuotientEvaluation X).map (quotientAction P r) ≫ (quotientVertexIso X 0).hom) =
    (quotientVertexIso X 0).hom ≫ (𝟙 _ ≫ (vectorStalk (k := k)).map
      (liftedEndHom (givenAction X r)) ≫ 𝟙 _) at h
  simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id] using h

variable {R : Type w} [Ring R] [Algebra k R]
variable (e : PresentedAlgebra P ≃ₐ[k] R)

def presentationRepresentation [Module R Y] [IsScalarTower k R Y] : Representation P Y :=
  Representation.ofAction (presentedGenerator P) (presentedGenerator_satisfies P)
    ((Algebra.lsmul k k Y).comp e.toAlgHom)

lemma presentationRepresentation_givenAction [Module R Y] [IsScalarTower k R Y] :
    givenAction (presentationRepresentation (Y := Y) e) =
      (Algebra.lsmul k k Y).comp e.toAlgHom := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext h
  exact presentationLift_generator P _ _ h

/-- For a genuinely presented algebra R, every element of theta evaluates to its R-module action. -/
theorem module_quotientAction_square [Module R Y] [IsScalarTower k R Y] (r : R) :
    (boundedQuotientEvaluation (presentationRepresentation (Y := Y) e)).map
      (quotientActionOfPresentation P e r) ≫
        (quotientVertexIso (presentationRepresentation (Y := Y) e) 0).hom =
    (quotientVertexIso (presentationRepresentation (Y := Y) e) 0).hom ≫
      (vectorStalk (k := k)).map (liftedEndHom ((Algebra.lsmul k k Y) r)) := by
  have h := quotientAction_square (presentationRepresentation (Y := Y) e) (e.symm r)
  rw [presentationRepresentation_givenAction] at h
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply,
    quotientActionOfPresentation] using h
end LittleFinitistic.QuadraticEncoding

end

end OAI
