import OAI.NumberTheory.JointDickman.Amplification.DyadicTailSum

namespace OAI

/-! # The convergent scale sum in the amplification second moment -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem amplification_scale_sum (S : Finset ℕ) {B L : ℝ}
    (hB : 0 < B) (hL : 0 < L)
    (hcap : ∀ i ∈ S, (2 : ℝ)^i * L ≤ 8 * B) :
    (∑ i ∈ S, (((2 : ℝ)^i * L) / B)^amplificationExponent / ((2 : ℝ)^i * L)) ≤
      ((8 : ℝ)^(amplificationExponent - 1) *
        ((2 : ℝ)^(amplificationExponent - 1) /
          ((2 : ℝ)^(amplificationExponent - 1) - 1))) / B := by
  have ha : 0 < amplificationExponent - 1 := sub_pos.mpr amplificationExponent_gt_one
  have heq (i : ℕ) :
      (((2 : ℝ)^i * L) / B)^amplificationExponent / ((2 : ℝ)^i * L) =
      (8 : ℝ)^(amplificationExponent - 1) / B *
        (((2 : ℝ)^i * L) / (8 * B))^(amplificationExponent - 1) := by
    have hx : 0 < (2 : ℝ)^i * L := by positivity
    have hratio : ((2 : ℝ)^i * L) / B = 8 * (((2 : ℝ)^i * L) / (8 * B)) := by field_simp
    have hpow : (((2 : ℝ)^i * L) / B)^(amplificationExponent - 1) =
        (8 : ℝ)^(amplificationExponent - 1) *
          (((2 : ℝ)^i * L) / (8 * B))^(amplificationExponent - 1) := by
      rw [hratio, Real.mul_rpow (by norm_num) (by positivity)]
    calc
      _ = (((2 : ℝ)^i * L) / B)^(amplificationExponent - 1) / B := by
        rw [Real.rpow_sub (div_pos hx hB), Real.rpow_one]
        field_simp
      _ = _ := by rw [hpow]; ring
  simp_rw [heq]
  rw [← mul_sum]
  have hsum := dyadic_power_sum_bound S (mul_pos (by norm_num : (0 : ℝ) < 8) hB)
    hL.le ha hcap
  have hh := mul_le_mul_of_nonneg_left hsum
    (by positivity : (0 : ℝ) ≤ (8 : ℝ)^(amplificationExponent - 1) / B)
  convert hh using 1; ring

/-- The no-change contribution, including the outside factor B, tends to zero. -/
theorem amplification_no_change_tendsto :
    Tendsto (fun B : ℕ => (B : ℝ) * (auxiliaryRatio B)^(-amplificationExponent))
      atTop (𝓝 0) := by
  have ht := amplification_log_loss.comp tendsto_natCast_atTop_atTop
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 1] with B hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_trans Nat.zero_lt_one hB)
  have hlog : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast hB)
  rw [auxiliaryRatio, Real.rpow_neg (by positivity : (0 : ℝ) ≤ B / (1000 * Real.log B)),
    Real.div_rpow hB0.le (by positivity)]
  dsimp only [Function.comp_def]
  field_simp

/-- Four regular high-prime sets supply the exponent strictly exceeding one. -/
theorem four_tail_coin_bound {B Y C : ℝ} {n : ℕ}
    (hB : 0 < B) (hY : 0 < Y)
    (hn : 4 * ((2 / 5 : ℝ) * Real.log (B / Y) - C) ≤ (n : ℝ)) :
    (1 / 2 : ℝ)^n ≤ (2 : ℝ)^(4 * C) * (Y / B)^amplificationExponent := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (1 / 2 : ℝ)^n = Real.exp (-(n : ℝ) * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num),
      show Real.log (1 / 2 : ℝ) = -Real.log 2 by rw [one_div, Real.log_inv]]
    congr 1
    ring
  rw [hpow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (div_pos hY hB), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlogs : Real.log (Y / B) = -Real.log (B / Y) := by
    rw [Real.log_div hY.ne' hB.ne', Real.log_div hB.ne' hY.ne']
    ring
  rw [hlogs]
  have hh := mul_le_mul_of_nonneg_right hn hlog2.le
  unfold amplificationExponent
  nlinarith only [hh]

end JointDickman

end OAI
