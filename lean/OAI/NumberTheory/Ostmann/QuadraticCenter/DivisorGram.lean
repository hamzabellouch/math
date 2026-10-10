import OAI.NumberTheory.Ostmann.QuadraticCenter.DivisorGramCube
import OAI.NumberTheory.Ostmann.QuadraticCenter.DivisorGramFactors

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem prime_subset_double_gram_identity {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (lam : ℝ) :
    (∑ s : Finset P, ∑ t : Finset P,
      lam ^ s.card * lam ^ t.card *
        (Nat.gcd (primeSubsetProduct s) (primeSubsetProduct t) : ℝ) /
        (Real.sqrt (primeSubsetProduct s : ℝ) * Real.sqrt (primeSubsetProduct t : ℝ))) =
      ∏ p ∈ P, (1 + lam ^ 2 + 2 * lam / Real.sqrt (p : ℝ)) := by
  classical
  simp_rw [prime_subset_gram_factorization hP]
  have hh := double_powerset_symmetric_gram (Finset.univ : Finset P)
    (fun p : P => lam / Real.sqrt (p.val : ℝ)) (fun _ => lam ^ 2)
  rw [← Finset.prod_coe_sort P (fun p : ℕ => 1 + lam ^ 2 + 2 * lam / Real.sqrt (p : ℝ))]
  simpa only [Finset.powerset_univ, ← mul_div_assoc] using hh

theorem squarefree_divisor_gram_euler_product {L : ℕ} (hL : Squarefree L) (lam : ℝ) :
    (∑ d ∈ L.divisors, ∑ e ∈ L.divisors,
      lam ^ d.primeFactors.card * lam ^ e.primeFactors.card * (Nat.gcd d e : ℝ) /
        (Real.sqrt (d : ℝ) * Real.sqrt (e : ℝ))) =
      ∏ p ∈ L.primeFactors, (1 + lam ^ 2 + 2 * lam / Real.sqrt (p : ℝ)) := by
  have hP : ∀ p ∈ L.primeFactors, Nat.Prime p := fun p hp => (Nat.mem_primeFactors.mp hp).1
  rw [sum_squarefree_divisors_eq_cube hL]
  simp_rw [sum_squarefree_divisors_eq_cube hL, primeSubsetProduct_primeFactors_card hP]
  exact prime_subset_double_gram_identity hP lam

theorem squarefree_divisor_gram_euler_product' {L : ℕ} (hL : Squarefree L) (lam : ℝ) :
    (∑ d ∈ L.divisors, ∑ e ∈ L.divisors,
      lam ^ (d.primeFactors.card + e.primeFactors.card) *
        ((Nat.gcd d e : ℝ) / Real.sqrt ((d : ℝ) * e))) =
      ∏ p ∈ L.primeFactors, (1 + lam ^ 2 + 2 * lam / Real.sqrt (p : ℝ)) := by
  rw [← squarefree_divisor_gram_euler_product hL lam]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  rw [pow_add, Real.sqrt_mul (Nat.cast_nonneg d)]
  ring

end Ostmann.QuadraticCenter

end OAI
