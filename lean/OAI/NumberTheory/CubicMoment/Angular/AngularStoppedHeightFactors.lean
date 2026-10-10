import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedOuterCoefficient
import OAI.NumberTheory.CubicMoment.Estimates.CenteredProductHeight

namespace OAI

/-! Multiplicative angular phases in the two coefficients give exactly
 the angular phase of the original centered height kernel. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma centeredHeightSum_angular_factors (ℓ : ℤ) (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (W : ℝ → ℂ) (H T X X₀ : ℝ) :
    (∑ a ∈ A, ∑ b ∈ B, (α a*theta ℓ a)*(β b*theta ℓ b)*
      centeredHeightKernel 0 W H T X X₀ (a*b)) =
    ∑ a ∈ A, ∑ b ∈ B, α a*β b*centeredHeightKernel ℓ W H T X X₀ (a*b) := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [centeredHeightKernel,theta_zero,theta_mul]
  ring

end CubicFirstMoment

end

end OAI
