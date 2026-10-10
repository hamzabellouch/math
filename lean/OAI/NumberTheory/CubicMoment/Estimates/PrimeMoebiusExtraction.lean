import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCoefficientBounds

namespace OAI

/-! Removing one prime from the actual unordered cutoff-Mobius product.
The remaining coefficient and character are constant on the free prime;
there is no permutation or divisor multiplicity in this identity. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cutoffMoebius_prime_mul (ψ : ℝ → ℝ) (w : ℝ)
    {p c : Eisenstein} (hp : primaryPrime p) (hc : primary c)
    (hs : Squarefree c) (hpc : ¬p ∣ c) :
    cutoffMoebius ψ w (p*c) = -(ψ (norm p/w):ℂ)*cutoffMoebius ψ w c := by
  have hpnot : p ∉ primaryPrimeFactors c :=
    fun h => hpc (primaryPrimeFactor_spec hc h).2
  have hf : ∀ q ∈ insert p (primaryPrimeFactors c), primaryPrime q := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact (primaryPrimeFactor_spec hc hq).1
  calc
    _ = cutoffMoebius ψ w (∏ q ∈ insert p (primaryPrimeFactors c), q) := by
      rw [Finset.prod_insert hpnot,primaryPrimeFactors_prod hc hs]
    _ = ∏ q ∈ insert p (primaryPrimeFactors c), -(ψ (norm q/w):ℂ) :=
      cutoffMoebius_prime_product ψ w _ hf
    _ = -(ψ (norm p/w):ℂ)*cutoffMoebius ψ w c := by
      rw [Finset.prod_insert hpnot,←cutoffMoebius_prime_product ψ w (primaryPrimeFactors c)
        (fun q hq => (primaryPrimeFactor_spec hc hq).1),primaryPrimeFactors_prod hc hs]

theorem cutoffMoebius_free_prime_identity (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (ψ : ℝ → ℝ) (w u : ℝ)
    {c : Eisenstein} (hc : primary c) (hs : Squarefree c) (v : Eisenstein) :
    (∑ p ∈ S with ¬p ∣ c,
      cutoffMoebius ψ w (p*c)*normTwist u (p*c)*cubicSymbol (p*c) v) =
    (-cutoffMoebius ψ w c*normTwist u c*cubicSymbol c v)*
      ∑ p ∈ S with ¬p ∣ c, (ψ (norm p/w):ℂ)*normTwist u p*cubicSymbol p v := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpS,hpc⟩ := Finset.mem_filter.mp hp
  have hp' := hS p hpS
  rw [cutoffMoebius_prime_mul ψ w hp' hc hs hpc,
    normTwist_mul u hp'.2.ne_zero (primary_ne_zero hc),
    cubicSymbol_mul_lower hp'.2.ne_zero (primary_ne_zero hc)]
  ring

lemma cutoffMoebius_free_prime_prefactor_bound {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w u : ℝ)
    {c : Eisenstein} (hc : primary c) (v : Eisenstein) :
    ‖-cutoffMoebius ψ w c*normTwist u c*cubicSymbol c v‖ ≤ 1 := by
  rw [norm_mul,norm_mul,norm_neg,norm_normTwist,mul_one]
  exact (mul_le_mul (cutoffMoebius_norm_le_one hψ w c) (norm_cubicSymbol_le_one hc v)
    (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

end CubicFirstMoment

end

end OAI
