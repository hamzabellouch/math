import OAI.NumberTheory.Ostmann.Arithmetic.DivisorGrowthLocal

namespace OAI

namespace Ostmann.Arithmetic
open scoped BigOperators

theorem small_prime_cost_le (s : Finset ℕ) (P : ℕ) {C : ℝ} (hC : 1 ≤ C) :
    (∏ p ∈ s, if p < P then C else 1) ≤ C ^ P := by
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const]
  apply pow_le_pow_right₀ hC
  calc
    (s.filter (fun p => p < P)).card ≤ (Finset.range P).card :=
      Finset.card_le_card (fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
    _ = P := Finset.card_range P

theorem prod_prime_factor_rpow (n : ℕ) (hn : n ≠ 0) (ε : ℝ) :
    (∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p) = (n : ℝ) ^ ε := by
  calc
    (∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p) =
        ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε :=
      Finset.prod_congr rfl (fun p _ => Real.rpow_pow_comm (Nat.cast_nonneg p) ε _)
    _ = (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) ^ ε :=
      Real.finsetProd_rpow _ _ (fun _ _ => by positivity) ε
    _ = (n : ℝ) ^ ε := by
      congr 1
      exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm

theorem divisors_card_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨P, C, hC, hlocal⟩ := prime_local_divisor_bounds ε hε
  refine ⟨C ^ P, pow_pos (by linarith) P, fun n hn => ?_⟩
  have hn0 := Nat.ne_of_gt hn
  have hprod : (∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)) ≤
      ∏ p ∈ n.primeFactors,
        (if p < P then C else 1) * ((p : ℝ) ^ ε) ^ n.factorization p := by
    apply Finset.prod_le_prod₀
    · intro p hp
      positivity
    · intro p hp
      exact hlocal p (Nat.prime_of_mem_primeFactors hp) _
  rw [Finset.prod_mul_distrib, prod_prime_factor_rpow n hn0 ε] at hprod
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      rw [Nat.card_divisors hn0]
      push_cast
      rfl
    _ ≤ (∏ p ∈ n.primeFactors, if p < P then C else 1) * (n : ℝ) ^ ε := hprod
    _ ≤ C ^ P * (n : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_right (small_prime_cost_le _ P hC) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem divisors_card_pow_le_rpow (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) ^ k ≤ C * (n : ℝ) ^ ε := by
  by_cases hk : k = 0
  · subst k
    refine ⟨1, by norm_num, fun n hn => ?_⟩
    simp only [pow_zero, one_mul]
    exact Real.one_le_rpow (by exact_mod_cast hn) hε.le
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  obtain ⟨C, hC, hbound⟩ := divisors_card_le_rpow (ε / k) (div_pos hε hkpos)
  refine ⟨C ^ k, pow_pos hC k, fun n hn => ?_⟩
  have h := pow_le_pow_left₀ (Nat.cast_nonneg n.divisors.card) (hbound n hn) k
  have hr : ((n : ℝ) ^ (ε / k)) ^ k = (n : ℝ) ^ ε := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ (ε / k)) k,
      ← Real.rpow_mul (Nat.cast_nonneg n), div_mul_cancel₀ ε hkpos.ne']
  simpa only [mul_pow, hr] using h

theorem two_pow_primeFactors_card_le_divisors_card (n : ℕ) (hn : 0 < n) :
    2 ^ n.primeFactors.card ≤ n.divisors.card := by
  rw [Nat.card_divisors (Nat.ne_of_gt hn), ← Finset.prod_const]
  apply Finset.prod_le_prod
  intro p hp
  have hmem := Nat.mem_primeFactors.mp hp
  have h := hmem.1.factorization_pos_of_dvd hmem.2.2 hmem.2.1
  omega

end Ostmann.Arithmetic

end OAI
