import OAI.NumberTheory.Ostmann.Arithmetic.DivisorGrowth

namespace OAI

namespace Ostmann.Arithmetic
open scoped BigOperators

theorem self_le_totient_mul_two_pow (n : ℕ) :
    n ≤ n.totient * 2 ^ n.primeFactors.card := by
  have hpos : 0 < ∏ p ∈ n.primeFactors, (p - 1) := by
    apply Finset.prod_pos
    intro p hp
    have h := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hprod : (∏ p ∈ n.primeFactors, p) ≤
      ∏ p ∈ n.primeFactors, 2 * (p - 1) := by
    apply Finset.prod_le_prod
    intro p hp
    have h := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  rw [Finset.prod_mul_distrib, Finset.prod_const] at hprod
  have h := Nat.mul_le_mul_left n.totient hprod
  rw [Nat.totient_mul_prod_primeFactors, ← Nat.mul_assoc] at h
  exact Nat.le_of_mul_le_mul_right h hpos

theorem self_le_totient_mul_divisors (n : ℕ) (hn : 0 < n) :
    n ≤ n.totient * n.divisors.card :=
  (self_le_totient_mul_two_pow n).trans
    (Nat.mul_le_mul_left _ (two_pow_primeFactors_card_le_divisors_card n hn))

theorem div_totient_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (n : ℝ) / n.totient ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C, hC, hbound⟩ := divisors_card_le_rpow ε hε
  refine ⟨C, hC, fun n hn => ?_⟩
  have ht : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  calc
    (n : ℝ) / n.totient ≤ n.divisors.card := by
      apply (div_le_iff₀ ht).mpr
      have h := self_le_totient_mul_divisors n hn
      exact_mod_cast (by simpa [Nat.mul_comm] using h)
    _ ≤ _ := hbound n hn

theorem totient_ge_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n →
      c * (n : ℝ) ^ (1 - ε) ≤ n.totient := by
  obtain ⟨C, hC, hbound⟩ := div_totient_le_rpow ε hε
  refine ⟨C⁻¹, inv_pos.mpr hC, fun n hn => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hr : 0 < (n : ℝ) ^ ε := Real.rpow_pos_of_pos hnR ε
  have h := (div_le_iff₀ ht).mp (hbound n hn)
  rw [Real.rpow_sub hnR, Real.rpow_one]
  have heq : C⁻¹ * ((n : ℝ) / (n : ℝ) ^ ε) = (n : ℝ) / (C * (n : ℝ) ^ ε) := by
    field_simp
  rw [heq]
  exact (div_le_iff₀ (mul_pos hC hr)).mpr (by simpa [mul_comm] using h)

end Ostmann.Arithmetic

end OAI
