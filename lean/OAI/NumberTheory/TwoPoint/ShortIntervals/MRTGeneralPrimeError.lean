import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalCoarse

namespace OAI

/-! The general-multiplicative discrepancy in extracting a prime factor.
It vanishes unless that prime divides the cofactor, and hence has the
same prime-square support as the corrected Ramaré denominator error. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrtTypicalCoefficient_prime_mul_coprime {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (F : ℕ → ℂ) (hF : Multiplicative F)
    {p : ℕ} (hp : p ∈ P j) {m : ℕ} (hm : 0 < m) (hpm : ¬p ∣ m) :
    mrtTypicalCoefficient J P F (p * m) =
      F p * mrtTypicalCoefficient (J.erase j) P F m := by
  unfold mrtTypicalCoefficient
  rw [mrtTypical_prime_mul J P hP hdis hj hp]
  split_ifs
  · exact hF p m (hP j hj p hp).pos hm ((hP j hj p hp).coprime_iff_not_dvd.mpr hpm)
  · simp

noncomputable def mrtPrimeProductError (P : Finset ℕ)
    (active : ℕ → ℕ → Prop) (C A B : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ P, if p ∣ n ∧ active p n then
    (C n - A p * B (n / p)) / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ)
  else 0

theorem mrt_prime_product_error_bound (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (active : ℕ → ℕ → Prop) (C A B : ℕ → ℂ)
    (hC : OneBounded C) (hA : OneBounded A) (hB : OneBounded B)
    (hproduct : ∀ p ∈ P, ∀ m, 0 < m → ¬p ∣ m → C (p * m) = A p * B m)
    {n : ℕ} (hn : 0 < n) :
    ‖mrtPrimeProductError P active C A B n‖ ≤ 2 * mrtPrimeSquareCount P n := by
  unfold mrtPrimeProductError
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ P, if p ^ 2 ∣ n then (2 : ℝ) else 0 := by
      apply sum_le_sum
      intro p hp
      by_cases hgate : p ∣ n ∧ active p n
      · rw [ite_eq_left hgate]
        have hm : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hgate.1) (hP p hp).pos
        by_cases hsquare : p ^ 2 ∣ n
        · rw [ite_eq_left hsquare, norm_div, Complex.norm_natCast]
          have hc : ‖C n - A p * B (n / p)‖ ≤ 2 := by
            apply (norm_sub_le _ _).trans
            rw [norm_mul]
            have hab := mul_le_mul (hA p (hP p hp).pos) (hB (n / p) hm)
              (norm_nonneg _) zero_le_one
            nlinarith [hC n hn]
          calc
            _ ≤ 2 / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℝ) :=
              div_le_div_of_nonneg_right hc (by positivity)
            _ ≤ 2 := div_le_self (by norm_num) (by norm_num)
        · have hnot : ¬p ∣ n / p := by
            intro hd
            apply hsquare
            simpa only [pow_two] using (Nat.dvd_div_iff_mul_dvd hgate.1).mp hd
          have he : C n = A p * B (n / p) := by
            calc
              C n = C (p * (n / p)) := congrArg C (Nat.mul_div_cancel' hgate.1).symm
              _ = _ := hproduct p hp (n / p) hm hnot
          rw [he, sub_self, zero_div, norm_zero, ite_eq_right hsquare]
      · rw [ite_eq_right hgate, norm_zero]
        split_ifs <;> norm_num
    _ = _ := by
      unfold mrtPrimeSquareCount
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      split_ifs <;> norm_num

end TwoPointCorrelations

end OAI
