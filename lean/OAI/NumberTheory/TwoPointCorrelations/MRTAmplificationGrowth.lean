import OAI.NumberTheory.TwoPointCorrelations.MRTFrequencyExponents

namespace OAI

/-! Explicit factorial and ceiling costs in the multiscale mixed moment.
These estimates keep the numerical scale requirements visible. -/

namespace TwoPointCorrelations

lemma mrt_factorial_square_exp (r : ℕ) :
    (r.factorial : ℝ) ^ 2 ≤
      Real.exp (2 * (r : ℝ) * Real.log (max 1 (r : ℝ))) := by
  by_cases hr : r = 0
  · subst r
    norm_num
  · have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    have hf : (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by exact_mod_cast Nat.factorial_le_pow r
    calc
      _ ≤ ((r : ℝ) ^ r) ^ 2 := pow_le_pow_left₀ (by positivity) hf 2
      _ = _ := by
        rw [max_eq_right hrR, mrt_nat_pow_eq_exp (by positivity : (0 : ℝ) < r),
          ← Real.exp_nat_mul]
        congr 1
        ring

lemma mrt_amplification_log_cost {Y u : ℝ}
    (hY : 1 ≤ Real.log Y) (hu : 1 ≤ Real.log u) (hY0 : 0 < Y) (hu0 : 0 < u) :
    (mrtAmplificationOrder Y u : ℝ) *
        Real.log (max 1 (mrtAmplificationOrder Y u : ℝ)) ≤
      (Real.log u / Real.log Y + 1) * (Real.log (Real.log u) + 1) := by
  have hY1 : 1 < Y := (Real.log_pos_iff hY0.le).mp (by linarith)
  have hu1 : 1 ≤ u := (Real.log_nonneg_iff hu0).mp (by linarith)
  let r : ℕ := mrtAmplificationOrder Y u
  have hr := (mrt_amplification_order_bounds hY1 hu1).2.2.le
  change (r : ℝ) ≤ Real.log u / Real.log Y + 1 at hr
  have hx0 : 0 < Real.log u := by linarith
  have hquot : Real.log u / Real.log Y ≤ Real.log u :=
    div_le_self hx0.le hY
  have hmax : max 1 (r : ℝ) ≤ 2 * Real.log u := by
    apply max_le
    · linarith
    · linarith
  have hlog : Real.log (max 1 (r : ℝ)) ≤ Real.log (Real.log u) + 1 := by
    calc
      _ ≤ Real.log (2 * Real.log u) := Real.log_le_log (by positivity) hmax
      _ = Real.log 2 + Real.log (Real.log u) := Real.log_mul (by norm_num) hx0.ne'
      _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul hr hlog (Real.log_nonneg (le_max_left _ _))
    (by positivity)

end TwoPointCorrelations

end OAI
