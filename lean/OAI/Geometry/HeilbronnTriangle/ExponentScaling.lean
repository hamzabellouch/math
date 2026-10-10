import Mathlib

namespace OAI


noncomputable section

namespace Problem355

theorem exponent_scaling {n r a k : ℝ}
    (hn : 0 < n) (hr : 64 ≤ r) (hk : 0 < k)
    (hsize : n ≤ r ^ (100000 * k))
    (harea : r ^ 2 / 64 ≤ n ^ 2 * a) :
    n ^ (-2 + 1 / (100000 * k)) ≤ a := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hk0 : 0 < 100000 * k := mul_pos (by norm_num) hk
  have hc : 0 < 1 / (100000 * k) := one_div_pos.mpr hk0
  have hroot : n ^ (1 / (100000 * k)) ≤ r := by
    calc
      n ^ (1 / (100000 * k)) ≤
          (r ^ (100000 * k)) ^ (1 / (100000 * k)) :=
        Real.rpow_le_rpow hn.le hsize hc.le
      _ = r := by
        rw [← Real.rpow_mul hr0.le]
        field_simp
        simp
  have hrscale : r ≤ r ^ 2 / 64 := by nlinarith
  have hscaled : n ^ (1 / (100000 * k)) ≤ n ^ 2 * a :=
    hroot.trans (hrscale.trans harea)
  have hpow : n ^ (-2 + 1 / (100000 * k)) * n ^ (2 : ℝ) =
      n ^ (1 / (100000 * k)) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  rw [← hpow, Real.rpow_two] at hscaled
  nlinarith [sq_pos_of_pos hn]

end Problem355

end

end OAI
