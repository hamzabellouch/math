import OAI.NumberTheory.CubicMoment.Angular.AngularKummerAlgebra
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedPrimeFactorization
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedPrimeBox

namespace OAI

/-! The fixed complementary primary factor in a free-prime sum is a
constant of norm at most one, even when its cubic symbol vanishes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_fixed_primary_free_prime_sum (ℓ : ℤ) (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (a : Eisenstein → ℂ)
    (r c v : Eisenstein) (hr : primary r) (hc : primary c) (u : ℝ) :
    (∑ p ∈ S, a p*normTwist u (r*(p*c))*angularCubicSymbol ℓ (r*(p*c)) v) =
      (normTwist u r*angularCubicSymbol ℓ r v)*
        ∑ p ∈ S, a p*normTwist u (p*c)*angularCubicSymbol ℓ (p*c) v := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpc : p*c ≠ 0 := mul_ne_zero (hS p hp).2.ne_zero (primary_ne_zero hc)
  rw [normTwist_mul u (primary_ne_zero hr) hpc,
    angularCubicSymbol_mul_lower ℓ (primary_ne_zero hr) hpc]
  ring


lemma angular_fixed_primary_free_prime_norm (ℓ : ℤ) (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (a : Eisenstein → ℂ)
    (r c v : Eisenstein) (hr : primary r) (hc : primary c) (u : ℝ) :
    ‖∑ p ∈ S, a p*normTwist u (r*(p*c))*angularCubicSymbol ℓ (r*(p*c)) v‖ ≤
      ‖∑ p ∈ S, a p*normTwist u (p*c)*angularCubicSymbol ℓ (p*c) v‖ := by
  rw [angular_fixed_primary_free_prime_sum ℓ S hS a r c v hr hc u,norm_mul,
    norm_mul,norm_normTwist,one_mul]
  exact mul_le_of_le_one_left (_root_.norm_nonneg _) (angularCubicSymbol_norm_le_one ℓ hr v)

end CubicFirstMoment

end

end OAI
