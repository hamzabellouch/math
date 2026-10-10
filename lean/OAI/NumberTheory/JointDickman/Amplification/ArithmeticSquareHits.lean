import OAI.NumberTheory.JointDickman.Amplification.ArithmeticPeriod
import OAI.NumberTheory.JointDickman.Probability.ResidueQuotientMean

namespace OAI

/-! # The exact rare-square error for the arithmetic amplification -/

namespace JointDickman
open Finset

open Classical in
def AuxiliarySquareHit (B n : ℕ) : Prop :=
  ∃ p ∈ auxiliaryPrimes B, p^2 ∣ n ∨ p^2 ∣ n+1

theorem auxiliarySquare_dvd_period {B p : ℕ} (hp : p ∈ auxiliaryPrimes B) :
    p^2 ∣ auxiliarySquarePeriod B := by
  unfold auxiliarySquarePeriod
  exact pow_dvd_pow_of_dvd (dvd_prod_of_mem id hp) 2

open Classical in
theorem residue_square_divisor_mean {B p : ℕ} (hp : p ∈ auxiliaryPrimes B) (k : ℕ) :
    (∑ a : ZMod (auxiliarySquarePeriod B),
      if p^2 ∣ a.val+k then (1 : ℝ) else 0) / (auxiliarySquarePeriod B : ℝ) =
        1 / (p : ℝ)^2 := by
  let : NeZero (p^2) := ⟨pow_ne_zero _ (auxiliaryPrimes_prime B p hp).ne_zero⟩
  have h := residue_quotient_mean (auxiliarySquare_dvd_period hp)
    (fun r : ZMod (p^2) => if r = -(k : ZMod (p^2)) then (1 : ℝ) else 0)
  have he (n : ℕ) :
      (if (n : ZMod (p^2)) = -(k : ZMod (p^2)) then (1 : ℝ) else 0) =
        if p^2 ∣ n+k then 1 else 0 := by
    congr 1
    rw [← ZMod.natCast_eq_zero_iff]
    simp only [Nat.cast_add, add_eq_zero_iff_eq_neg]
  simp only [he, sum_ite_eq', mem_univ, ite_true, Nat.cast_pow] at h
  exact h

open Classical in
theorem squareHit_indicator_le (B n : ℕ) :
    (if AuxiliarySquareHit B n then (1 : ℝ) else 0) ≤
      ∑ p ∈ auxiliaryPrimes B,
        ((if p^2 ∣ n then (1 : ℝ) else 0) + (if p^2 ∣ n+1 then (1 : ℝ) else 0)) := by
  have hn (p : ℕ) : 0 ≤ (if p^2 ∣ n then (1 : ℝ) else 0) +
      (if p^2 ∣ n+1 then (1 : ℝ) else 0) := by positivity
  by_cases h : AuxiliarySquareHit B n
  · rw [ite_eq_left h]
    obtain ⟨p, hp, hd⟩ := h
    have ht : (1 : ℝ) ≤ (if p^2 ∣ n then (1 : ℝ) else 0) +
        (if p^2 ∣ n+1 then (1 : ℝ) else 0) := by
      rcases hd with hd | hd <;> simp only [hd, ite_true] <;> split_ifs <;> norm_num
    exact ht.trans (single_le_sum (fun p _ => hn p) hp)
  · rw [ite_eq_right h]
    exact sum_nonneg (fun p _ => hn p)

open Classical in
theorem residue_squareHit_mean_bound (B : ℕ) :
    (∑ a : ZMod (auxiliarySquarePeriod B),
      if AuxiliarySquareHit B a.val then (1 : ℝ) else 0) / (auxiliarySquarePeriod B : ℝ) ≤
        2 * ∑ p ∈ auxiliaryPrimes B, 1 / (p : ℝ)^2 := by
  calc
    _ ≤ (∑ a : ZMod (auxiliarySquarePeriod B), ∑ p ∈ auxiliaryPrimes B,
        ((if p^2 ∣ a.val then (1 : ℝ) else 0) +
          (if p^2 ∣ a.val+1 then (1 : ℝ) else 0))) / (auxiliarySquarePeriod B : ℝ) :=
      div_le_div_of_nonneg_right (sum_le_sum (fun a _ => squareHit_indicator_le B a.val))
        (Nat.cast_nonneg _)
    _ = _ := by
      rw [sum_comm, sum_div]
      simp_rw [sum_add_distrib, add_div]
      have h0 (p : ℕ) (hp : p ∈ auxiliaryPrimes B) := residue_square_divisor_mean hp 0
      simp only [add_zero] at h0
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      rw [h0 p hp, residue_square_divisor_mean hp 1]
      ring

end JointDickman

end OAI
