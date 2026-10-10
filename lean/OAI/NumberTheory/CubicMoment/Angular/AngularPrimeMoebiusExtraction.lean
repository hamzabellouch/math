import OAI.NumberTheory.CubicMoment.Estimates.PrimeMoebiusExtraction
import OAI.NumberTheory.CubicMoment.Angular.AngularKummerAlgebra
import OAI.NumberTheory.CubicMoment.Angular.AngularLongPrimeSW
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCoefficientBounds

namespace OAI

/-! Removing one prime from the actual unordered cutoff-Mobius product.
The remaining coefficient and character are constant on the free prime;
there is no permutation or divisor multiplicity in this identity. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_cutoffMoebius_free_prime_identity (ℓ : ℤ) (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (ψ : ℝ → ℝ) (w u : ℝ)
    {c : Eisenstein} (hc : primary c) (hs : Squarefree c) (v : Eisenstein) :
    (∑ p ∈ S with ¬p ∣ c,
      cutoffMoebius ψ w (p*c)*normTwist u (p*c)*angularCubicSymbol ℓ (p*c) v) =
    (-cutoffMoebius ψ w c*normTwist u c*angularCubicSymbol ℓ c v)*
      ∑ p ∈ S with ¬p ∣ c, (ψ (norm p/w):ℂ)*normTwist u p*angularCubicSymbol ℓ p v := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpS,hpc⟩ := Finset.mem_filter.mp hp
  have hp' := hS p hpS
  rw [cutoffMoebius_prime_mul ψ w hp' hc hs hpc,
    normTwist_mul u hp'.2.ne_zero (primary_ne_zero hc),
    angularCubicSymbol_mul_lower ℓ hp'.2.ne_zero (primary_ne_zero hc)]
  ring

lemma angular_cutoffMoebius_free_prime_prefactor_bound (ℓ : ℤ) {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w u : ℝ)
    {c : Eisenstein} (hc : primary c) (v : Eisenstein) :
    ‖-cutoffMoebius ψ w c*normTwist u c*angularCubicSymbol ℓ c v‖ ≤ 1 := by
  rw [norm_mul,norm_mul,norm_neg,norm_normTwist,mul_one]
  exact (mul_le_mul (cutoffMoebius_norm_le_one hψ w c) (angularCubicSymbol_norm_le_one ℓ hc v)
    (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

end CubicFirstMoment

end

end OAI
