import Mathlib

namespace OAI

namespace Balanced.LineOccupancy

open Filter Topology

theorem tendsto_vacant_fraction :
    Tendsto (fun q : ℕ => (1 - 1 / (q : ℝ)) ^ q) atTop (𝓝 (Real.exp (-1))) := by
  simpa [sub_eq_add_neg, div_eq_mul_inv] using Real.tendsto_one_add_div_pow_exp (-1)

theorem one_quarter_lt_exp_neg_one : (1 / 4 : ℝ) < Real.exp (-1) := by
  rw [Real.exp_neg, ← one_div]
  apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 4) (Real.exp_pos 1)).2
  nlinarith [Real.exp_one_lt_three]

theorem eventually_mean_gap :
    ∀ᶠ q : ℕ in atTop,
      (q : ℝ) * (1 - 1 / (q : ℝ)) ^ q - (q : ℝ) / 5 ≥ (q : ℝ) / 20 := by
  have h := tendsto_vacant_fraction.eventually
    (eventually_gt_nhds one_quarter_lt_exp_neg_one)
  filter_upwards [h] with q hq
  have hm := mul_le_mul_of_nonneg_left hq.le (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  nlinarith

theorem occupancy_exponent (q : ℕ) (hq : 0 < q) :
    -(((q : ℝ) / 20) ^ 2) / (8 * (q : ℝ) * (1 : ℝ) ^ 2) = -(q : ℝ) / 3200 := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  field_simp
  ring

theorem tendsto_line_union_bound :
    Tendsto (fun q : ℕ =>
      (q : ℝ) * ((q : ℝ) + 1) * (2 * Real.exp (-(q : ℝ) / 3200)))
      atTop (𝓝 0) := by
  have h₁ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    1 (1 / 3200) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h₂ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    2 (1 / 3200) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h := (h₂.add h₁).const_mul 2
  convert h using 1
  · funext q
    simp only [Function.comp_apply, Real.rpow_one, Real.rpow_two]
    rw [show -(q : ℝ) / 3200 = -(1 / 3200) * (q : ℝ) by ring]
    ring
  · norm_num

end Balanced.LineOccupancy

end OAI
