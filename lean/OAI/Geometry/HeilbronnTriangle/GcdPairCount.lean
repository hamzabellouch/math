import Mathlib

namespace OAI


namespace Problem355.GcdPairCount

open Finset

lemma sum_dvd_indicator (M d c : ℕ) :
    (∑ s ∈ Ioc 0 M, if d ∣ s then c else 0) = (M / d) * c := by
  rw [← Finset.sum_filter]
  simp [Nat.Ioc_filter_dvd_card_eq_div]

lemma common_divisor_square_sum (M d : ℕ) :
    (∑ s ∈ Ioc 0 M, ∑ t ∈ Ioc 0 M,
      if d ∣ s ∧ d ∣ t then d ^ 2 else 0) = (d * (M / d)) ^ 2 := by
  simp_rw [ite_and]
  simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp_rw [sum_dvd_indicator]
  ring

theorem sum_gcd_sq_le_cube (M : ℕ) :
    (∑ s ∈ Ioc 0 M, ∑ t ∈ Ioc 0 M, (Nat.gcd s t) ^ 2) ≤ M ^ 3 := by
  have hpoint (s : ℕ) (hs : s ∈ Ioc 0 M) (t : ℕ) (ht : t ∈ Ioc 0 M) :
      (Nat.gcd s t) ^ 2 ≤ ∑ d ∈ Ioc 0 M,
        if d ∣ s ∧ d ∣ t then d ^ 2 else 0 := by
    have hs' := Finset.mem_Ioc.mp hs
    have hg : Nat.gcd s t ∈ Ioc 0 M := by
      exact Finset.mem_Ioc.mpr ⟨Nat.gcd_pos_of_pos_left t hs'.1,
        (Nat.gcd_le_left t hs'.1).trans hs'.2⟩
    have h := Finset.single_le_sum
      (f := fun d => if d ∣ s ∧ d ∣ t then d ^ 2 else 0)
      (fun _ _ => Nat.zero_le _) hg
    simpa [Nat.gcd_dvd_left, Nat.gcd_dvd_right] using h
  calc
    (∑ s ∈ Ioc 0 M, ∑ t ∈ Ioc 0 M, (Nat.gcd s t) ^ 2)
        ≤ ∑ s ∈ Ioc 0 M, ∑ t ∈ Ioc 0 M, ∑ d ∈ Ioc 0 M,
            if d ∣ s ∧ d ∣ t then d ^ 2 else 0 := by
      exact Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun t ht => hpoint s hs t ht
    _ = ∑ s ∈ Ioc 0 M, ∑ d ∈ Ioc 0 M, ∑ t ∈ Ioc 0 M,
          if d ∣ s ∧ d ∣ t then d ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      exact Finset.sum_comm
    _ = ∑ d ∈ Ioc 0 M, ∑ s ∈ Ioc 0 M, ∑ t ∈ Ioc 0 M,
          if d ∣ s ∧ d ∣ t then d ^ 2 else 0 := Finset.sum_comm
    _ = ∑ d ∈ Ioc 0 M, (d * (M / d)) ^ 2 := by
      exact Finset.sum_congr rfl fun d hd => common_divisor_square_sum M d
    _ ≤ ∑ d ∈ Ioc 0 M, M ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      exact Nat.pow_le_pow_left (Nat.mul_div_le M d) 2
    _ = M ^ 3 := by simp [pow_succ, Nat.mul_comm]

end Problem355.GcdPairCount

end OAI
