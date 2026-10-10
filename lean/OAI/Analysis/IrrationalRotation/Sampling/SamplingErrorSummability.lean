import Mathlib

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.ProductSampling

theorem summable_rpow_of_two_pow_le {m : ℕ → ℝ}
    (hm : ∀ n, (2 : ℝ) ^ n ≤ m n) {r : ℝ} (hr : r < 0) :
    Summable (fun n => m n ^ r) := by
  have hgeom : Summable (fun n : ℕ => ((2 : ℝ) ^ r) ^ n) :=
    summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hr)
  apply hgeom.of_norm_bounded
  intro n
  have hm0 : 0 ≤ m n := le_trans (by positivity : 0 ≤ (2 : ℝ) ^ n) (hm n)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hm0 _)]
  calc
    m n ^ r ≤ ((2 : ℝ) ^ n) ^ r :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (hm n) hr.le
    _ = ((2 : ℝ) ^ r) ^ n := by
      rw [← Real.rpow_natCast_mul (by norm_num), mul_comm,
        Real.rpow_mul_natCast (by norm_num)]

theorem summable_superpower_of_two_pow_le {m : ℕ → ℝ}
    (hm : ∀ n, (2 : ℝ) ^ n ≤ m n) {b : ℝ} (hb : 0 < b) :
    Summable (fun n => m n ^ (-(m n) / b)) := by
  have hrecip : Summable (fun n => m n ^ (-1 : ℝ)) :=
    summable_rpow_of_two_pow_le hm (by norm_num)
  apply hrecip.of_norm_bounded_eventually_nat
  have hlarge : ∀ᶠ n : ℕ in atTop, b ≤ (2 : ℝ) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop b
  filter_upwards [hlarge] with n hn
  have hm1 : 1 ≤ m n := le_trans (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (hm n)
  have hm0 : 0 ≤ m n := le_trans zero_le_one hm1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hm0 _)]
  apply Real.rpow_le_rpow_of_exponent_le hm1
  apply (div_le_iff₀ hb).mpr
  have hbmn : b ≤ m n := hn.trans (hm n)
  linarith

theorem sampling_error_majorant_summable {m : ℕ → ℝ}
    (hm : ∀ n, (2 : ℝ) ^ n ≤ m n) (C : ℝ) :
    Summable (fun n => C * m n ^ (-39 : ℝ) + m n ^ (-(m n) / 25)) := by
  exact ((summable_rpow_of_two_pow_le hm (by norm_num : (-39 : ℝ) < 0)).mul_left C).add
    (summable_superpower_of_two_pow_le hm (by norm_num : (0 : ℝ) < 25))

end Invariant233.ProductSampling

end OAI
