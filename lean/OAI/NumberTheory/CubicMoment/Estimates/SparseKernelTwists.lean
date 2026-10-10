import OAI.NumberTheory.CubicMoment.Estimates.SparseCenteredBilinear

namespace OAI

/-! The sparse centered estimate applies to the original common norm
and angular twists by exact multiplicativity, with no height restriction. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma sparse_common_twist_norm {a : Eisenstein} (ha : primary a) (ℓ : ℤ) (u : ℝ) :
    ‖theta ℓ a*normTwist u a‖ = 1 := by
  rw [norm_mul,norm_theta (primary_ne_zero ha),norm_normTwist,mul_one]

lemma sparse_common_twist_identity (P Q : Finset Eisenstein)
    (hP : ∀ a ∈ P, primary a) (hQ : ∀ b ∈ Q, primary b)
    (α β F V : Eisenstein → ℂ) (ℓ : ℤ) (u : ℝ) :
    (∑ a ∈ P, ∑ b ∈ Q, α a*β b*F (a*b)*theta ℓ (a*b)*normTwist u (a*b)*V (a*b)) =
    ∑ a ∈ P, ∑ b ∈ Q,
      (α a*(theta ℓ a*normTwist u a))*(β b*(theta ℓ b*normTwist u b))*F (a*b)*V (a*b) := by
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [theta_mul,normTwist_mul u (primary_ne_zero (hP a ha)) (primary_ne_zero (hQ b hb))]
  ring

end CubicFirstMoment

end

end OAI
