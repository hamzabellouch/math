import OAI.NumberTheory.CubicMoment.Angular.AngularTypeILow
import OAI.NumberTheory.CubicMoment.Estimates.RadialTypeILow
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialTypeILow
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTypeILow

namespace OAI

/-! A common low-height Type-I interface for every fixed angular mode.
The radial residue and the nonzero-angular lattice cancellation have
both been proved before this final case split. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicTheta_typeI_low
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    (ℓ : ℤ) 
    {B A : ℝ} (hB : 1 ≤ B) (hA : 0 ≤ A) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X R U : ℝ),
      2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, Y (w r) = X) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → W (w r) x = 0) →
      (∀ r ∈ S, ‖α r‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k) →
      ‖∑ r ∈ S, α r*(metaplecticAngularSmoothSum r ℓ (W (w r)) U 0-
        angularSmoothModel r ℓ (W (w r)) U)‖ ≤ K*X^(5/6-1/100:ℝ) := by
  by_cases hℓ : ℓ = 0
  · subst ℓ
    exact cubicTheta_radial_typeI_low hW hB hA k
  · exact angular_typeI_low_proved hW ℓ hℓ hB hA k

end CubicFirstMoment

end

end OAI
