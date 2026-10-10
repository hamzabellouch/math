import OAI.NumberTheory.CubicMoment.Decomposition.StoppedOuterEnergy
import OAI.NumberTheory.CubicMoment.Angular.AngularAlgebra
import OAI.NumberTheory.CubicMoment.Estimates.CenteredProductMellin

namespace OAI

/-! The fixed-angular twist of the actual stopped outer coefficient.
Its primary-support energy and divisor bounds are unchanged. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def angularStoppedAlpha (ℓ : ℤ) (E U : Finset Eisenstein) (ψ : ℝ → ℝ)
    (w : ℝ) (remaining : Eisenstein → Prop) (a : Eisenstein) : ℂ :=
  stoppedAlpha E U ψ w remaining a * theta ℓ a

lemma angularStoppedAlpha_norm (ℓ : ℤ) (E U : Finset Eisenstein) (ψ : ℝ → ℝ)
    (w : ℝ) (remaining : Eisenstein → Prop) {a : Eisenstein} (ha : primary a) :
    ‖angularStoppedAlpha ℓ E U ψ w remaining a‖ = ‖stoppedAlpha E U ψ w remaining a‖ := by
  rw [angularStoppedAlpha,norm_mul,norm_theta (primary_ne_zero ha),mul_one]

lemma angularStoppedAlpha_energy (ℓ : ℤ) (E U P : Finset Eisenstein) (ψ : ℝ → ℝ)
    (w : ℝ) (remaining : Eisenstein → Prop) (hP : ∀ a ∈ P, primary a) :
    (∑ a ∈ P, ‖angularStoppedAlpha ℓ E U ψ w remaining a‖^2) =
      ∑ a ∈ P, ‖stoppedAlpha E U ψ w remaining a‖^2 := by
  apply Finset.sum_congr rfl
  intro a ha
  rw [angularStoppedAlpha_norm ℓ E U ψ w remaining (hP a ha)]

lemma centeredProductSmoothed_angular_factors (ℓ : ℤ) (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (V : ℝ → ℂ) (X u : ℝ) :
    centeredProductSmoothed A B (fun a => α a * theta ℓ a)
      (fun b => β b * theta ℓ b) 0 V X u =
      centeredProductSmoothed A B α β ℓ V X u := by
  unfold centeredProductSmoothed
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [theta_zero,theta_mul,mul_one]
  ring

lemma centeredProductPolynomial_angular_factors (ℓ : ℤ) (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ) :
    centeredProductPolynomial A B (fun a => α a * theta ℓ a)
      (fun b => β b * theta ℓ b) 0 u =
      centeredProductPolynomial A B α β ℓ u := by
  unfold centeredProductPolynomial
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [theta_zero,theta_mul,mul_one]
  ring

end CubicFirstMoment

end

end OAI
