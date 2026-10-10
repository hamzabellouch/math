import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRamareIdentity

namespace OAI

/-! Positive coefficient weights in the uncorrected Ramaré polynomial.
They have total mass at most one, even at integers divisible by prime
squares.  This is the contraction needed for logarithmic-bin cutoffs. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def mrtRamareWeight (P : Finset ℕ) (n p : ℕ) : ℝ :=
  if p ∣ n then 1 / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℝ) else 0

lemma mrtRamareWeight_nonneg (P : Finset ℕ) (n p : ℕ) :
    0 ≤ mrtRamareWeight P n p := by
  unfold mrtRamareWeight
  split_ifs <;> positivity

lemma mrt_ramare_weight_le_count (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {p n : ℕ} (hp : p ∈ P) (hpn : p ∣ n) :
    mrtRamareWeight P n p ≤ 1 / (finitePrimeDivisorCount P n : ℝ) := by
  have hcount := mrt_prime_divisor_count_mul P hP hp (n / p)
  rw [Nat.mul_div_cancel' hpn] at hcount
  have hc : finitePrimeDivisorCount P n ≤ finitePrimeDivisorCount P (n / p) + 1 := by
    rw [hcount]
    split_ifs <;> omega
  have hpos : (0 : ℝ) < finitePrimeDivisorCount P n := by
    exact_mod_cast finitePrimeDivisorCount_pos_of_mem hp hpn
  rw [mrtRamareWeight, ite_eq_left hpn]
  exact one_div_le_one_div_of_le hpos (by exact_mod_cast hc)

theorem mrt_ramare_weight_sum_le_one (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    (∑ p ∈ P, mrtRamareWeight P n p) ≤ 1 := by
  by_cases hc : finitePrimeDivisorCount P n = 0
  · have hz : ∀ p ∈ P, ¬p ∣ n := by
      intro p hp hpn
      have := finitePrimeDivisorCount_pos_of_mem hp hpn
      omega
    have hs : (∑ p ∈ P, mrtRamareWeight P n p) = 0 := by
      apply sum_eq_zero
      intro p hp
      simp only [mrtRamareWeight, ite_eq_right (hz p hp)]
    rw [hs]
    norm_num
  · calc
      _ ≤ ∑ p ∈ P, if p ∣ n then 1 / (finitePrimeDivisorCount P n : ℝ) else 0 := by
        apply sum_le_sum
        intro p hp
        by_cases hpn : p ∣ n
        · rw [ite_eq_left hpn]
          exact mrt_ramare_weight_le_count P hP hp hpn
        · simp only [mrtRamareWeight, ite_eq_right hpn, le_refl]
      _ = 1 := by
        rw [← sum_filter, sum_const, nsmul_eq_mul, ← finitePrimeDivisorCount_eq_card]
        exact mul_one_div_cancel (by exact_mod_cast hc)

theorem mrt_ramare_weighted_contraction (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (n : ℕ) (z : ℕ → ℂ)
    (hz : ∀ p ∈ P, ‖z p‖ ≤ 1) :
    ‖∑ p ∈ P, (mrtRamareWeight P n p : ℂ) * z p‖ ≤ 1 := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ P, mrtRamareWeight P n p := by
      apply sum_le_sum
      intro p hp
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mrtRamareWeight_nonneg P n p)]
      exact (mul_le_mul_of_nonneg_left (hz p hp) (mrtRamareWeight_nonneg P n p)).trans_eq
        (mul_one _)
    _ ≤ 1 := mrt_ramare_weight_sum_le_one P hP n

end TwoPointCorrelations

end OAI
