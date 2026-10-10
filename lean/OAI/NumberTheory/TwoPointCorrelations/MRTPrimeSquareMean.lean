import OAI.NumberTheory.TwoPointCorrelations.MRTDyadicMeanSquare
import OAI.NumberTheory.TwoPointCorrelations.MRTRamareIdentity

namespace OAI

/-! The prime-square error in the corrected Ramaré decomposition has a
small mean square.  The count is evaluated by pairing prime-square
divisibility tests; distinct primes give the product modulus exactly. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def mrtPrimeSquareCount (P : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ P, if p ^ 2 ∣ n then 1 else 0

lemma mrtPrimeSquareCount_nonneg (P : Finset ℕ) (n : ℕ) :
    0 ≤ mrtPrimeSquareCount P n := by
  unfold mrtPrimeSquareCount
  exact sum_nonneg fun _ _ => by split_ifs <;> norm_num

lemma mrt_prime_square_joint_count (N p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    (∑ n ∈ Icc 1 N, (if p ^ 2 ∣ n then (1 : ℝ) else 0) *
      (if q ^ 2 ∣ n then (1 : ℝ) else 0)) ≤
      (N : ℝ) * ((if p = q then 1 / (p : ℝ) ^ 2 else 0) +
        (1 / (p : ℝ) ^ 2) * (1 / (q : ℝ) ^ 2)) := by
  by_cases hpq : p = q
  · subst q
    have he (n : ℕ) : (if p ^ 2 ∣ n then (1 : ℝ) else 0) *
        (if p ^ 2 ∣ n then (1 : ℝ) else 0) =
        (if p ^ 2 ∣ n then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    simp_rw [he]
    rw [mrt_count_multiples (pow_pos hp.pos 2)]
    simp only [ite_true]
    calc
      _ ≤ (N : ℝ) / (p ^ 2 : ℕ) := Nat.cast_div_le
      _ = (N : ℝ) * (1 / (p : ℝ) ^ 2) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
        (Nat.cast_nonneg N)
  · have hc : Nat.Coprime (p ^ 2) (q ^ 2) := ((Nat.coprime_primes hp hq).mpr hpq).pow 2 2
    have hd (n : ℕ) : p ^ 2 * q ^ 2 ∣ n ↔ p ^ 2 ∣ n ∧ q ^ 2 ∣ n := by
      constructor
      · intro h
        exact ⟨dvd_trans (dvd_mul_right _ _) h, dvd_trans (dvd_mul_left _ _) h⟩
      · rintro ⟨h1, h2⟩
        exact hc.mul_dvd_of_dvd_of_dvd h1 h2
    have he (n : ℕ) : (if p ^ 2 ∣ n then (1 : ℝ) else 0) *
        (if q ^ 2 ∣ n then (1 : ℝ) else 0) =
        (if p ^ 2 * q ^ 2 ∣ n then (1 : ℝ) else 0) := by
      simp only [hd]
      split_ifs <;> simp_all
    simp_rw [he]
    rw [mrt_count_multiples (Nat.mul_pos (pow_pos hp.pos 2) (pow_pos hq.pos 2)),
      ite_eq_right hpq, zero_add]
    convert (Nat.cast_div_le (m := N) (n := p ^ 2 * q ^ 2) :
      ((N / (p ^ 2 * q ^ 2) : ℕ) : ℝ) ≤ (N : ℝ) / (p ^ 2 * q ^ 2 : ℕ)) using 1
    push_cast
    ring

/-- No logarithm or cardinality of the prime set occurs in the
divisibility-count second moment. -/
theorem mrt_prime_square_count_second_moment (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (mrtPrimeSquareCount P n) ^ 2) ≤
      (N : ℝ) * ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
        (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
  have he (n : ℕ) : (mrtPrimeSquareCount P n) ^ 2 =
      ∑ p ∈ P, ∑ q ∈ P, (if p ^ 2 ∣ n then (1 : ℝ) else 0) *
        (if q ^ 2 ∣ n then (1 : ℝ) else 0) := by
    unfold mrtPrimeSquareCount
    rw [pow_two, sum_mul]
    apply sum_congr rfl
    intro p _
    rw [mul_sum]
  simp_rw [he]
  rw [sum_comm (s := Icc 1 N) (t := P)]
  calc
    _ = ∑ p ∈ P, ∑ q ∈ P, ∑ n ∈ Icc 1 N,
        (if p ^ 2 ∣ n then (1 : ℝ) else 0) *
        (if q ^ 2 ∣ n then (1 : ℝ) else 0) := by
      apply sum_congr rfl
      intro p _
      exact sum_comm
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, (N : ℝ) *
        ((if p = q then 1 / (p : ℝ) ^ 2 else 0) +
          (1 / (p : ℝ) ^ 2) * (1 / (q : ℝ) ^ 2)) := by
      apply sum_le_sum
      intro p hp
      apply sum_le_sum
      intro q hq
      exact mrt_prime_square_joint_count N p q (hP p hp) (hP q hq)
    _ = _ := by
      simp_rw [← mul_sum]
      congr 1
      simp only [sum_add_distrib]
      congr 1
      · apply sum_congr rfl
        intro p hp
        simp [hp]
      · calc
          _ = ∑ p ∈ P, (1 / (p : ℝ) ^ 2) * (∑ q ∈ P, 1 / (q : ℝ) ^ 2) := by
            apply sum_congr rfl
            intro p _
            exact (mul_sum _ _ _).symm
          _ = _ := by rw [← sum_mul, pow_two]

theorem mrt_prime_square_coefficient_mass (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (hb : ∀ n ∈ Ioc N (2 * N), ‖b n‖ ≤ mrtPrimeSquareCount P n) :
    (∑ n ∈ Ioc N (2 * N), ‖b n / (n : ℂ)‖ ^ 2) ≤
      (2 / (N : ℝ)) * ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
        (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ ∑ n ∈ Ioc N (2 * N), ((mrtPrimeSquareCount P n) / (N : ℝ)) ^ 2 := by
      apply sum_le_sum
      intro n hn
      rw [norm_div, Complex.norm_natCast]
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div₀ (mrtPrimeSquareCount_nonneg P n) (hb n hn) hNr
        (by exact_mod_cast (mem_Ioc.mp hn).1.le)
    _ = (N : ℝ)⁻¹ ^ 2 * ∑ n ∈ Ioc N (2 * N), (mrtPrimeSquareCount P n) ^ 2 := by
      simp_rw [div_eq_mul_inv, mul_pow]
      rw [← sum_mul, mul_comm]
    _ ≤ (N : ℝ)⁻¹ ^ 2 * ∑ n ∈ Icc 1 (2 * N), (mrtPrimeSquareCount P n) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
      · exact fun _ _ _ => sq_nonneg _
    _ ≤ (N : ℝ)⁻¹ ^ 2 * ((2 * N : ℕ) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mrt_prime_square_count_second_moment P hP (2 * N))
        (by positivity)
    _ = _ := by
      push_cast
      field_simp

/-- The mean-square cost of any prime-square-supported Ramaré error. -/
theorem mrt_prime_square_dyadic_mean (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (hb : ∀ n ∈ Ioc N (2 * N), ‖b n‖ ≤ mrtPrimeSquareCount P n)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtDyadicPolynomial b N t‖ ^ 2) ≤
      32 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hm := mrt_dirichlet_mean_square_subset (Ioc N (2 * N)) (N := 2 * N)
    (by intro n hn; exact mem_Ioc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega,
      (mem_Ioc.mp hn).2⟩) (fun n => b n / (n : ℂ)) hT
  apply hm.trans
  calc
    _ ≤ 8 * Real.exp 1 * (T + (2 * N : ℕ)) * ((2 / (N : ℝ)) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mrt_prime_square_coefficient_mass P hP b hN hb)
        (by positivity)
    _ = 16 * Real.exp 1 * (T / (N : ℝ) + 2) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
      push_cast
      field_simp; ring
    _ ≤ _ := by
      have hc : 0 ≤ (∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2 := by positivity
      nlinarith [mul_nonneg (Real.exp_pos 1).le hc,
        mul_nonneg (div_nonneg hT.le hNr.le) (mul_nonneg (Real.exp_pos 1).le hc)]

end TwoPointCorrelations

end OAI
