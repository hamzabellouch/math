import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourcePrimeSets
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPairwiseActual

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open Preliminaries HigherBiasSource
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem boundedInterval_primes_coprime {Q : ℕ} (E F : Finset (PrimeUpTo Q))
    {a b c d : ℝ} (hsep : b ≤ c) {q r : PrimeUpTo Q}
    (hq : q ∈ boundedInterval E a b) (hr : r ∈ boundedInterval F c d) : q.val.Coprime r.val := by
  have hqlog := boundedInterval_log_bounds E a b q hq
  have hrlog := boundedInterval_log_bounds F c d r hr
  exact prime_coprime_of_log_lt (primeUpTo_prime q) (primeUpTo_prime r)
    ((hqlog.2.trans (Real.exp_le_exp.mpr hsep)).trans_lt hrlog.1)

theorem twoPrime_support_value_of_intervals (p : I → ℕ) (L S : I) (hLS : L ≠ S)
    {Q : ℕ} (E F : Finset (PrimeUpTo Q)) {a b c d : ℝ} (hsep : b ≤ c)
    (q r : PrimeUpTo Q) (hq : q ∈ boundedInterval E a b) (hr : r ∈ boundedInterval F c d)
    (z : ℂ) :
    (if Pairwise (fun i h => (twoPrimeAssignment p L S q.val r.val i).Coprime
      (twoPrimeAssignment p L S q.val r.val h)) then z else 0) =
      longPrimeSupportMask p L S q.val * shortPrimeSupportMask p L S r.val * z := by
  rw [←twoPrimeAssignment_support_indicator_of_coprime p L S hLS q.val r.val
    (boundedInterval_primes_coprime E F hsep hq hr)]
  split_ifs <;> simp

theorem twoPrime_support_value_of_reversed_intervals (p : I → ℕ) (L S : I) (hLS : L ≠ S)
    {Q : ℕ} (E F : Finset (PrimeUpTo Q)) {a b c d : ℝ} (hsep : b ≤ c)
    (q r : PrimeUpTo Q) (hq : q ∈ boundedInterval F c d) (hr : r ∈ boundedInterval E a b)
    (z : ℂ) :
    (if Pairwise (fun i h => (twoPrimeAssignment p L S q.val r.val i).Coprime
      (twoPrimeAssignment p L S q.val r.val h)) then z else 0) =
      longPrimeSupportMask p L S q.val * shortPrimeSupportMask p L S r.val * z := by
  rw [←twoPrimeAssignment_support_indicator_of_coprime p L S hLS q.val r.val
    (boundedInterval_primes_coprime E F hsep hr hq).symm]
  split_ifs <;> simp

theorem supported_prime_unary_norms (p : I → ℕ) (L S : I) (u v : ℕ → ℂ)
    (hu : ∀q,‖u q‖ ≤ 1) (hv : ∀r,‖v r‖ ≤ 1) :
    (∀q,‖longPrimeSupportMask p L S q * u q‖ ≤ 1) ∧
    (∀r,‖shortPrimeSupportMask p L S r * v r‖ ≤ 1) := by
  constructor
  · intro q
    rw [norm_mul]
    exact (mul_le_mul (longPrimeSupportMask_norm_le p L S q) (hu q)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  · intro r
    rw [norm_mul]
    exact (mul_le_mul (shortPrimeSupportMask_norm_le p L S r) (hv r)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
