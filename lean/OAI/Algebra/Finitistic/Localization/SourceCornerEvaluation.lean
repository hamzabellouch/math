import OAI.Algebra.Finitistic.Localization.SourceImageEvaluation

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SourceImageEvaluation
private theorem map_projection_square {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A : D} {B I : C} (e : A ≅ F.obj B)
    (p : B ⟶ I) (b : B ⟶ B) (c : I ⟶ I) (a : A ⟶ A)
    (sq : a ≫ e.hom = e.hom ≫ F.map b) (h : b ≫ p = p ≫ c) :
    a ≫ (e.hom ≫ F.map p) = (e.hom ≫ F.map p) ≫ F.map c := by
  rw [← Category.assoc, sq, Category.assoc, ← F.map_comp, h, F.map_comp, ← Category.assoc]

open QuadraticEncoding
universe u v w
variable {k : Type u} [Field k] {R : Type w} [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R)
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]

def corner (e a : R) (he : e*e=e) : U E e he ⟶ U E e he :=
  ⟨SourceQuotientAction.theta E (e*a*e), by
    change ((SourceQuotientAction.theta E) e * (SourceQuotientAction.theta E) (e*a*e)) *
      (SourceQuotientAction.theta E) e = _
    simp only [← map_mul]
    congr 1
    simp only [← mul_assoc,he]
    rw [mul_assoc (e*a) e e,he]⟩

def imageCorner (e a : R) : imageDerived (k := k) (Y := Y) e ⟶ imageDerived (k := k) (Y := Y) e :=
  (derivedTargetInclusion (k := k)).preimage (DerivedCategory.Qh.map
    ((vectorStalk (k := k)).map (imageCornerEnd (action (k := k) (Y := Y) e).hom (action (k := k) (Y := Y) a).hom)))

lemma corner_projection_square (e a : R) (he : e*e=e) :
    (evaluation (Y := Y) E ⋙ derivedTargetInclusion (k := k)).map (SourceQuotientAction.theta E (e*a*e)) ≫
      projection (Y := Y) E e = projection (Y := Y) E e ≫
        (derivedTargetInclusion (k := k)).map (imageCorner (k := k) (Y := Y) e a) := by
  unfold imageCorner
  erw [Functor.map_preimage]
  have h := image_corner_square (action (k := k) (Y := Y) e).hom (action (k := k) (Y := Y) a).hom (action_idem (k := k) (Y := Y) e he)
  have hc : action (k := k) (Y := Y) (e*a*e) = ModuleCat.ofHom
      ((action (k := k) (Y := Y) e).hom * (action (k := k) (Y := Y) a).hom * (action (k := k) (Y := Y) e).hom) := by
    simp only [action,map_mul]
    rfl
  rw [← hc] at h
  exact map_projection_square ((vectorStalk (k := k)) ⋙ DerivedCategory.Qh)
    (vertexIso (Y := Y) E) (imageProjection (action (k := k) (Y := Y) e).hom)
    (action (k := k) (Y := Y) (e*a*e))
    (imageCornerEnd (action (k := k) (Y := Y) e).hom (action (k := k) (Y := Y) a).hom)
    ((evaluation (Y := Y) E ⋙ derivedTargetInclusion (k := k)).map
      (SourceQuotientAction.theta E (e*a*e)))
    (SourceActionEvaluation.derived_action_square (Y := Y) E (e*a*e)) h

theorem completed_corner_square (e a : R) (he : e*e=e) :
    (completed (Y := Y) E).map (corner E e a he) ≫ (summandImageIso (Y := Y) E e he).hom =
      (summandImageIso (Y := Y) E e he).hom ≫ imageCorner (k := k) (Y := Y) e a := by
  apply completedExtensionImageSquare
  apply (derivedTargetInclusion (k := k)).map_injective
  rw [Functor.map_comp,Functor.map_comp]
  erw [Functor.map_preimage]
  exact corner_projection_square E e a he

omit [FiniteDimensional k Y] in
/-- The central corner is exactly restriction of a, on actual vectors in eY. -/
theorem imageCorner_restriction (e a : R) (he : e*e=e) (hc : e*a=a*e)
    (x : imageSpace (k := k) (Y := Y) e) :
    ((imageCornerEnd (action (k := k) (Y := Y) e).hom (action (k := k) (Y := Y) a).hom) x).val =
      (action (k := k) (Y := Y) a).hom x.val := by
  apply imageCornerEnd_apply _ _ (action_idem (k := k) (Y := Y) e he)
  have h := congrArg (fun r => (action (k := k) (Y := Y) r).hom) hc
  simp only [action,map_mul] at h
  exact h

lemma selecting_action_eq_corner (e : R) (he : e*e=e) (hc : ∀ r : R,e*r=r*e)
    (alpha : R →ₐ[k] R) (r : R) :
    FormalSummandAction.action (SourceQuotientAction.theta E) e he hc alpha r =
      corner E e (alpha r) he := by
  apply Karoubi.Hom.ext
  exact FormalSummandAction.action_f _ _ _ _ _ _
end LittleFinitistic.SourceImageEvaluation

end

end OAI
