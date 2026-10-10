import OAI.NumberTheory.Ostmann.QuadraticCenter.DivisorGramArithmetic

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

private theorem div_sqrt_pair_mul_self {p : ℝ} (hp : 0 < p) (lam : ℝ) :
    (lam / Real.sqrt p) * (lam / Real.sqrt p) * p = lam ^ 2 := by
  have hs : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  field_simp
  nlinarith [Real.sq_sqrt hp.le]

theorem prime_subset_gram_factorization {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (s t : Finset P) (lam : ℝ) :
    lam ^ s.card * lam ^ t.card *
        (Nat.gcd (primeSubsetProduct s) (primeSubsetProduct t) : ℝ) /
        (Real.sqrt (primeSubsetProduct s : ℝ) * Real.sqrt (primeSubsetProduct t : ℝ)) =
      ∏ p : P, if p ∈ s then (if p ∈ t then lam ^ 2 else lam / Real.sqrt (p.val : ℝ))
        else (if p ∈ t then lam / Real.sqrt (p.val : ℝ) else 1) := by
  classical
  rw [primeSubsetProduct_gcd hP]
  calc
    _ = (lam ^ s.card / Real.sqrt (primeSubsetProduct s : ℝ)) *
        (lam ^ t.card / Real.sqrt (primeSubsetProduct t : ℝ)) *
          (primeSubsetProduct (s ∩ t) : ℝ) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = (∏ p ∈ s, lam / Real.sqrt (p.val : ℝ)) *
        (∏ p ∈ t, lam / Real.sqrt (p.val : ℝ)) * (∏ p ∈ s ∩ t, (p.val : ℝ)) := by
      rw [subset_weight_div_sqrt_product, subset_weight_div_sqrt_product]
      simp only [primeSubsetProduct, Nat.cast_prod]
    _ = (∏ p : P, if p ∈ s then lam / Real.sqrt (p.val : ℝ) else 1) *
        (∏ p : P, if p ∈ t then lam / Real.sqrt (p.val : ℝ) else 1) *
        (∏ p : P, if p ∈ s ∩ t then (p.val : ℝ) else 1) := by
      rw [Finset.prod_ite_mem_eq, Finset.prod_ite_mem_eq, Finset.prod_ite_mem_eq]
    _ = _ := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      have hp0 : (0 : ℝ) < p.val := by exact_mod_cast (hP p.val p.property).pos
      have he := div_sqrt_pair_mul_self hp0 lam
      by_cases hs : p ∈ s <;> by_cases ht : p ∈ t <;> simp [hs, ht, he]

end Ostmann.QuadraticCenter

end OAI
