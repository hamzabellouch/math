import Mathlib

namespace OAI


namespace Problem355

theorem eventually_mul_rpow_lt_rpow {n : ℕ → ℕ}
    (hn : Filter.Tendsto n Filter.atTop Filter.atTop)
    {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ j in Filter.atTop,
      C * Real.rpow (n j : ℝ) a < Real.rpow (n j : ℝ) b := by
  simp only [Real.rpow_eq_pow]
  have hnR : Filter.Tendsto (fun j => (n j : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hp := (tendsto_rpow_atTop (sub_pos.mpr hab)).comp hnR
  filter_upwards [hp.eventually (Filter.eventually_gt_atTop C),
    hn.eventually (Filter.eventually_ge_atTop 1)] with j hj hjn
  have hpos : 0 < (n j : ℝ) := by exact_mod_cast (show 0 < n j by omega)
  have hpowpos : 0 < Real.rpow (n j : ℝ) a := Real.rpow_pos_of_pos hpos a
  calc
    C * Real.rpow (n j : ℝ) a <
        Real.rpow (n j : ℝ) (b - a) * Real.rpow (n j : ℝ) a :=
      mul_lt_mul_of_pos_right hj hpowpos
    _ = Real.rpow (n j : ℝ) b := by
      simpa only [Real.rpow_eq_pow, sub_add_cancel] using (Real.rpow_add hpos (b - a) a).symm

end Problem355

end OAI
