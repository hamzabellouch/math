import OAI.Algebra.Finitistic.Localization.NormalizedQuotientAction
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.QuadraticEncoding
universe u v
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- The literal inhomogeneous relation polynomial. -/
def relationPolynomial (j : Fin t) : FreeAlgebra k (Fin d) :=
  (∑ h, ∑ l, P.quadratic j h l • (FreeAlgebra.ι k h * FreeAlgebra.ι k l)) +
  (∑ h, P.linear j h • FreeAlgebra.ι k h) + P.constant j • 1

def presentationRelation (a b : FreeAlgebra k (Fin d)) : Prop :=
  ∃ j, a = relationPolynomial P j ∧ b = 0

/-- The algebra with exactly the displayed finite quadratic presentation. -/
abbrev PresentedAlgebra := RingQuot (presentationRelation P)
def presentedGenerator (h : Fin d) : PresentedAlgebra P :=
  RingQuot.mkAlgHom k (presentationRelation P) (FreeAlgebra.ι k h)

theorem presentedGenerator_satisfies : P.Satisfies (presentedGenerator P) := by
  intro j
  have h := RingQuot.mkAlgHom_rel k (s := presentationRelation P) ⟨j,rfl,rfl⟩
  simpa only [relationPolynomial,map_add,map_sum,map_smul,map_mul,map_one,map_zero,
    presentedGenerator] using h

variable {A : Type v} [Ring A] [Algebra k A]

/-- Descent through the actual presentation, with every relation checked. -/
def presentationLift (x : Fin d → A) (hx : P.Satisfies x) : PresentedAlgebra P →ₐ[k] A :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k x, by
    rintro a b ⟨j,rfl,rfl⟩
    simpa only [relationPolynomial,map_add,map_sum,map_smul,map_mul,map_one,map_zero,
      FreeAlgebra.lift_ι_apply] using hx j⟩

@[simp] theorem presentationLift_generator (x : Fin d → A) (hx : P.Satisfies x) (h : Fin d) :
    presentationLift P x hx (presentedGenerator P h) = x h := by
  simp [presentationLift,presentedGenerator,RingQuot.liftAlgHom_mkAlgHom_apply]

/-- The manuscript's quotient action for its displayed presentation. -/
def quotientAction : PresentedAlgebra P →ₐ[k] End (vertexQ P 0) :=
  presentationLift P (normalizedGenerator P) (normalizedGenerator_satisfies P)

@[simp] theorem quotientAction_generator (h : Fin d) :
    quotientAction P (presentedGenerator P h) = normalizedGenerator P h :=
  presentationLift_generator _ _ _ _

/-- Transport the action along a genuine presentation isomorphism for R. -/
def quotientActionOfPresentation (e : PresentedAlgebra P ≃ₐ[k] A) :
    A →ₐ[k] End (vertexQ P 0) := (quotientAction P).comp e.symm.toAlgHom

@[simp] theorem quotientActionOfPresentation_generator (e : PresentedAlgebra P ≃ₐ[k] A)
    (h : Fin d) : quotientActionOfPresentation P e (e (presentedGenerator P h)) =
      normalizedGenerator P h := by simp [quotientActionOfPresentation]
end LittleFinitistic.QuadraticEncoding

end

end OAI
