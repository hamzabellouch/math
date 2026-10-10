import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

namespace MatroidProphet.Pivots

open Finset

noncomputable def binomialSum (n d : ℕ) : ℕ := ∑ k ∈ Iic d, n.choose k

lemma binomialSum_le_weighted (n d : ℕ) (κ : ℝ) (hκ : 1 ≤ κ) :
    (binomialSum n d : ℝ) ≤ κ ^ d * (1 + κ⁻¹) ^ n := by
  have hkpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have htrunc : (binomialSum n d : ℝ) = ∑ k ∈ Iic d ∩ Iic n, (n.choose k : ℝ) := by
    rw [binomialSum, Nat.cast_sum]
    apply (sum_subset inter_subset_left ?_).symm
    intro k hkd hnot
    have hnk : n < k := by simpa only [mem_inter, hkd, true_and, mem_Iic, not_le] using hnot
    simp [Nat.choose_eq_zero_of_lt hnk]
  have hp (k : ℕ) (hkd : k ≤ d) : 1 ≤ κ ^ d * (κ⁻¹) ^ k := by
    rw [inv_pow, ← div_eq_mul_inv]
    exact (one_le_div₀ (pow_pos hkpos k)).2 (pow_le_pow_right₀ hκ hkd)
  calc
    (binomialSum n d : ℝ) = ∑ k ∈ Iic d ∩ Iic n, (n.choose k : ℝ) := htrunc
    _ ≤ ∑ k ∈ Iic d ∩ Iic n, κ ^ d * ((κ⁻¹) ^ k * (n.choose k : ℝ)) := by
      apply sum_le_sum
      intro k hk
      have h := mul_le_mul_of_nonneg_right (hp k (mem_Iic.mp (mem_inter.mp hk).1))
        (Nat.cast_nonneg (n.choose k) : (0 : ℝ) ≤ n.choose k)
      simpa only [one_mul, mul_assoc] using h
    _ ≤ ∑ k ∈ Iic n, κ ^ d * ((κ⁻¹) ^ k * (n.choose k : ℝ)) :=
      sum_le_sum_of_subset_of_nonneg inter_subset_right (by intros; positivity)
    _ = κ ^ d * (1 + κ⁻¹) ^ n := by
      rw [← mul_sum, add_comm 1, add_pow, Nat.range_succ_eq_Iic]
      simp

lemma binomialSum_le_exp (n d : ℕ) (κ : ℝ) (hκ : 1 ≤ κ) :
    (binomialSum n d : ℝ) ≤ Real.exp ((d : ℝ) * Real.log κ + (n : ℝ) / κ) := by
  have hkpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hone : 1 + κ⁻¹ ≤ Real.exp κ⁻¹ := by simpa [add_comm] using Real.add_one_le_exp κ⁻¹
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + κ⁻¹) hone n
  calc
    (binomialSum n d : ℝ) ≤ κ ^ d * (1 + κ⁻¹) ^ n := binomialSum_le_weighted n d κ hκ
    _ ≤ κ ^ d * (Real.exp κ⁻¹) ^ n := mul_le_mul_of_nonneg_left hpow (pow_nonneg hkpos.le d)
    _ = Real.exp ((d : ℝ) * Real.log κ + (n : ℝ) / κ) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hkpos, div_eq_mul_inv, Real.exp_nat_mul]

lemma residual_raw_count_le_exp (n q : ℕ) (κ : ℝ) (hκ : 2 ≤ κ)
    (hq : (q : ℝ) ≤ (n : ℝ) / κ) :
    (((binomialSum n q) ^ 2 * (4 ^ (2 * q) * binomialSum n (2 * q)) ^ 2 : ℕ) : ℝ) ≤
      Real.exp (1000 * Real.log κ / κ * n) := by
  have hkone : 1 ≤ κ := by linarith
  have hkpos : 0 < κ := by linarith
  have hlog : 0 ≤ Real.log κ := Real.log_nonneg hkone
  have hloghalf : (1 : ℝ) / 2 ≤ Real.log κ := by
    have htwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      linarith
    exact htwo.trans (Real.log_le_log (by norm_num) hκ)
  have h4 : (4 : ℝ) ^ (2 * q) ≤ Real.exp (((4 * q : ℕ) : ℝ) * Real.log κ) := by
    rw [Real.exp_nat_mul, Real.exp_log hkpos]
    calc
      (4 : ℝ) ^ (2 * q) = (2 : ℝ) ^ (4 * q) := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
        congr 1
        omega
      _ ≤ κ ^ (4 * q) := pow_le_pow_left₀ (by norm_num) hκ _
  have hs := binomialSum_le_exp n q κ hkone
  have hs2 := binomialSum_le_exp n (2 * q) κ hkone
  have hproduct := mul_le_mul h4 hs2 (by positivity) (Real.exp_nonneg _)
  have hsquare := pow_le_pow_left₀ (by positivity) hs 2
  have hproductsquare := pow_le_pow_left₀ (by positivity) hproduct 2
  have hall := mul_le_mul hsquare hproductsquare (by positivity) (by positivity)
  have hexp : (((binomialSum n q) ^ 2 * (4 ^ (2 * q) * binomialSum n (2 * q)) ^ 2 : ℕ) : ℝ) ≤
      Real.exp (14 * (q : ℝ) * Real.log κ + 4 * ((n : ℝ) / κ)) := by
    push_cast
    convert hall using 1
    rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  apply hexp.trans (Real.exp_le_exp.mpr ?_)
  have hqlog := mul_le_mul_of_nonneg_right hq hlog
  have hn : (0 : ℝ) ≤ (n : ℝ) / κ := div_nonneg (Nat.cast_nonneg n) hkpos.le
  have hnlog : 4 * ((n : ℝ) / κ) ≤ 8 * ((n : ℝ) / κ) * Real.log κ := by
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hloghalf)]
  have hnlognonneg : 0 ≤ ((n : ℝ) / κ) * Real.log κ := mul_nonneg hn hlog
  calc
    14 * (q : ℝ) * Real.log κ + 4 * ((n : ℝ) / κ)
        ≤ 1000 * ((n : ℝ) / κ) * Real.log κ := by nlinarith
    _ = 1000 * Real.log κ / κ * n := by ring

end MatroidProphet.Pivots

end OAI
