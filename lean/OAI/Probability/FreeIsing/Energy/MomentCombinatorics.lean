import Mathlib

namespace OAI

open scoped BigOperators

namespace Problem367

theorem sum_sq_le_of_two_positive {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (r : ι → ℕ) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (hri : 0 < r i) (hrj : 0 < r j) :
    (∑ k ∈ s, r k ^ 2) ≤ (∑ k ∈ s, r k - 1) ^ 2 + 1 := by
  have hsum : r i + ∑ k ∈ s.erase i, r k = ∑ k ∈ s, r k :=
    Finset.add_sum_erase s r hi
  have hsumSq : r i ^ 2 + ∑ k ∈ s.erase i, r k ^ 2 = ∑ k ∈ s, r k ^ 2 :=
    Finset.add_sum_erase s (fun k => r k ^ 2) hi
  have hj' : j ∈ s.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩
  have hrest : 1 ≤ ∑ k ∈ s.erase i, r k :=
    le_trans hrj (Finset.single_le_sum (fun k _ => Nat.zero_le (r k)) hj')
  have hsq : (∑ k ∈ s.erase i, r k ^ 2) ≤ (∑ k ∈ s.erase i, r k) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun k _ => Nat.zero_le (r k))
  have htotal : 1 ≤ ∑ k ∈ s, r k := by omega
  have htotalSub := Nat.sub_add_cancel htotal
  have hiSub := Nat.sub_add_cancel hri
  have hrestSub := Nat.sub_add_cancel hrest
  nlinarith [Nat.zero_le ((r i - 1) * ((∑ k ∈ s.erase i, r k) - 1))]

theorem critical_moment_absorption {b theta : ℝ}
    (hb : 0 ≤ b) (htheta : 0 ≤ theta) (hthetaOne : theta < 1)
    (hcritical : b * theta ^ 2 = 1) {p : ℕ} (hp : 3 ≤ p) :
    0 < 1 - theta ∧ 1 - theta ≤ 1 - b * theta ^ p := by
  constructor
  · linarith
  · have hpow : theta ^ p ≤ theta ^ 3 :=
      pow_le_pow_of_le_one htheta hthetaOne.le hp
    have hmul := mul_le_mul_of_nonneg_left hpow hb
    have hcube : b * theta ^ 3 = theta := by nlinarith [hcritical]
    linarith

end Problem367

end OAI
