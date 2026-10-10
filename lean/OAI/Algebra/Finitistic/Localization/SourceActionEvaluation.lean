import OAI.Algebra.Finitistic.Localization.SourceEvaluation

namespace OAI
noncomputable section
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SourceActionEvaluation
open QuadraticEncoding SelectionEncoding QuadraticPresentation
universe u v w
variable {k : Type u} [Field k] {R : Type w} [Ring R] [Algebra k R]
variable (E : Encoding k R)
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]

def representation : Representation E.relations Y :=
  LittleFinitistic.QuadraticEncoding.Representation.ofModule (generator E) (generator_relations E)

abbrev evaluation := SourceEvaluation.quotientHomotopy (representation (Y := Y) E)
abbrev vertexIso := SourceEvaluation.quotientVertexIso (representation (Y := Y) E)

def given (_E : Encoding k R) : R →ₐ[k] End ((vectorStalk (k := k)).obj (ModuleCat.of k (ULift.{u} Y))) :=
  (identifiedEndHom (vectorStalk (k := k)) _ (Iso.refl _)).comp
    ((liftedEndHom (k := k) (Y := Y)).comp (Algebra.lsmul k k Y))

def evaluated : R →ₐ[k] End ((vectorStalk (k := k)).obj (ModuleCat.of k (ULift.{u} Y))) :=
  (identifiedEndHom (evaluation (Y := Y) E) _ (vertexIso (Y := Y) E 0)).comp
    (SourceQuotientAction.theta E)

lemma theta_generator (h : Fin E.generators) :
    SourceQuotientAction.theta E (generator E h) =
      SourceQuotientAction.a01 E.relations h.succ ≫ inv (SourceQuotientAction.a01 E.relations 0) := by
  simp only [SourceQuotientAction.theta,QuotientAction.presentedAction,AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom,generator,AlgEquiv.symm_apply_apply,QuotientAction.quotientAction_generator,
    QuotientAction.normalized]

lemma generator_square (h : Fin E.generators) :
    (evaluation (Y := Y) E).map (SourceQuotientAction.theta E (generator E h)) ≫
      (vertexIso (Y := Y) E 0).hom = (vertexIso (Y := Y) E 0).hom ≫
        (vectorStalk (k := k)).map (liftedEndHom ((Algebra.lsmul k k Y) (generator E h))) := by
  rw [theta_generator]
  apply QuotientAction.normalized_evaluation (SourceQuotientAction.a01 E.relations 0)
    (fun h => SourceQuotientAction.a01 E.relations h.succ) (evaluation (Y := Y) E)
    (vertexIso (Y := Y) E 0) (vertexIso (Y := Y) E 1)
    (fun h => (vectorStalk (k := k)).map (liftedEndHom ((Algebra.lsmul k k Y) (generator E h))))
  · simpa only [SourceEvaluation.actionArrow_zero,CategoryTheory.Functor.map_id,Category.comp_id] using
      SourceEvaluation.quotient_arrow01_square (representation (Y := Y) E) 0
  · intro h
    exact SourceEvaluation.quotient_arrow01_square (representation (Y := Y) E) h.succ

lemma evaluated_generator (h : Fin E.generators) :
    evaluated (Y := Y) E (generator E h) = given (Y := Y) E (generator E h) := by
  have hh := congrArg (fun f => (vertexIso (Y := Y) E 0).inv ≫ f) (generator_square (Y := Y) E h)
  change (vertexIso (Y := Y) E 0).inv ≫
    ((evaluation (Y := Y) E).map (SourceQuotientAction.theta E (generator E h)) ≫
      (vertexIso (Y := Y) E 0).hom) = _ at hh
  dsimp [evaluated,given,identifiedEndHom]
  simpa only [Category.assoc,Iso.inv_hom_id_assoc,Category.id_comp,Category.comp_id] using hh

/-- The native theta evaluates to the entire R-action, not just its generators. -/
theorem action_evaluates : evaluated (Y := Y) E = given (Y := Y) E := by
  let q := originalMap k (Fin E.generators) (QuotientAction.polynomial E.relations)
  have h : ((evaluated (Y := Y) E).comp E.equiv.toAlgHom).comp q =
      ((given (Y := Y) E).comp E.equiv.toAlgHom).comp q := by
    apply FreeAlgebra.hom_ext
    funext a
    exact evaluated_generator E a
  apply AlgHom.ext
  intro r
  obtain ⟨f,hf⟩ := (original k (Fin E.generators) (QuotientAction.polynomial E.relations)).mkₐ_surjective
    (α := k) (E.equiv.symm r)
  have hr : E.equiv (q f) = r := by rw [show q f = E.equiv.symm r from hf]; exact E.equiv.apply_symm_apply r
  have hh := AlgHom.congr_fun h f
  simpa only [AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,hr] using hh

theorem action_square (r : R) :
    (evaluation (Y := Y) E).map (SourceQuotientAction.theta E r) ≫ (vertexIso (Y := Y) E 0).hom =
      (vertexIso (Y := Y) E 0).hom ≫
        (vectorStalk (k := k)).map (liftedEndHom ((Algebra.lsmul k k Y) r)) := by
  have h := congrArg (fun f => (vertexIso (Y := Y) E 0).hom ≫ f)
    (AlgHom.congr_fun (action_evaluates (Y := Y) E) r)
  dsimp [evaluated,given,identifiedEndHom] at h
  simpa only [← Category.assoc,Iso.hom_inv_id,Category.id_comp,Category.comp_id] using h


/-- Whole-action compatibility in the bounded finite-dimensional derived target. -/
theorem derived_action_square (r : R) :
    (SourceEvaluation.derived (representation (Y := Y) E) ⋙ derivedTargetInclusion (k := k)).map
      (SourceQuotientAction.theta E r) ≫
        (SourceEvaluation.derivedVertexIso (representation (Y := Y) E) 0).hom =
    (SourceEvaluation.derivedVertexIso (representation (Y := Y) E) 0).hom ≫
      DerivedCategory.Qh.map ((vectorStalk (k := k)).map (liftedEndHom ((Algebra.lsmul k k Y) r))) := by
  have h := congrArg DerivedCategory.Qh.map (action_square (Y := Y) E r)
  simp only [Functor.map_comp] at h
  exact h

end LittleFinitistic.SourceActionEvaluation

end

end OAI
