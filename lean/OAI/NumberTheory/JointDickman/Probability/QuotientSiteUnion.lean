import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeQuotientSite

namespace OAI

/-! # The divisor and quotient together cover the full prime site -/

namespace JointDickman
open Finset

theorem coefficientPrimeSet_union_quotient {B n : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (ha : (∏ p ∈ A, p) ∣ n) :
    A ∪ coefficientPrimeSet B (n / (∏ p ∈ A, p)) = coefficientPrimeSet B n := by
  have he : (∏ p ∈ A, p) * (n / (∏ p ∈ A, p)) = n := Nat.mul_div_cancel' ha
  ext p
  constructor
  · intro hp
    rcases mem_union.mp hp with hp | hp
    · exact (primeProduct_dvd_site_iff hA).mp ha hp
    · obtain ⟨hpP, hpq⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨hpP, by rw [← he]; exact dvd_mul_of_dvd_right hpq _⟩
  · intro hp
    obtain ⟨hpP, hpn⟩ := mem_filter.mp hp
    have hprime := auxiliaryPrimes_prime B p hpP
    rw [← he] at hpn
    rcases hprime.dvd_mul.mp hpn with hpa | hpq
    · have hm : p ∈ coefficientPrimeSet B (∏ p ∈ A, p) := mem_filter.mpr ⟨hpP, hpa⟩
      rw [coefficientPrimeSet_primeProduct hA] at hm
      exact mem_union_left _ hm
    · exact mem_union_right _ (mem_filter.mpr ⟨hpP, hpq⟩)

theorem coefficient_residue_base_product {B : ℕ} {A : Finset ℕ}
    (hB : 1 < B) (hA : A ⊆ auxiliaryPrimes B) (Q : Finset ℕ) :
    coefficientWeight B (∏ p ∈ A, p) * residueBaseWeight B Q =
      (B : ℝ) * (1 / 2 : ℝ)^(A.card + Q.card) := by
  rw [coefficientWeight_primeProduct hA]
  unfold residueBaseWeight
  rw [← Real.sqrt_eq_rpow, pow_add]
  calc
    _ = (Real.log (auxiliaryCutoff B) *
        (Real.sqrt (auxiliaryRatio B) * Real.sqrt (auxiliaryRatio B))) *
        ((1 / 2 : ℝ)^A.card * (1 / 2 : ℝ)^Q.card) := by ring
    _ = _ := by
      rw [Real.mul_self_sqrt (auxiliaryRatio_pos hB).le,
        mul_comm (Real.log _) _, auxiliaryRatio_mul_log hB]

open Classical in
theorem arithmetic_split_weight_le {B L n : ℕ} {τ C : ℝ} {A : Finset ℕ}
    (hB : 1 < B) (hA : A ⊆ auxiliaryPrimes B) (ha : (∏ p ∈ A, p) ∣ n) :
    regularCoefficientWeight B L τ C (∏ p ∈ A, p) *
      regularResidueWeight B L τ C (coefficientPrimeSet B (n / (∏ p ∈ A, p))) ≤
      (B : ℝ) * (1 / 2 : ℝ)^(coefficientPrimeSet B n).card := by
  let Q := coefficientPrimeSet B (n / (∏ p ∈ A, p))
  have hcard : (coefficientPrimeSet B n).card ≤ A.card + Q.card := by
    rw [← coefficientPrimeSet_union_quotient hA ha]
    exact card_union_le _ _
  have hpow : (1 / 2 : ℝ)^(A.card + Q.card) ≤ (1 / 2 : ℝ)^(coefficientPrimeSet B n).card :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard
  have hn : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  rw [regularCoefficientWeight, coefficientPrimeSet_primeProduct hA]
  unfold regularResidueWeight
  split_ifs
  · exact (coefficient_residue_base_product hB hA Q).le.trans (mul_le_mul_of_nonneg_left hpow hn)
  all_goals simp only [mul_zero, zero_mul]
  all_goals positivity

end JointDickman

end OAI
