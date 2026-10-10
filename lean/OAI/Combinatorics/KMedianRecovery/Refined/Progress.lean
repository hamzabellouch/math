import OAI.Combinatorics.KMedianRecovery.Refined.Bounds

namespace OAI

/-! State-weight coefficients and quantitative progress estimates. -/

namespace MetricKMedianRecovery.RefinedRecovery.Analysis

lemma weight_coefficient_lt {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1/4) :
    1+(2+μ^3)*(3/2 : ℝ)+μ+(11/2 : ℝ)*μ^3 < 6 := by
  have hc : μ^3 ≤ (1/4 : ℝ)^3 := pow_le_pow_left₀ hμ hμ1 3
  norm_num at hc
  nlinarith

noncomputable def progressRate (κ q : ℝ) : ℝ := κ/(2*(6+κ/q))

lemma progressRate_pos {κ q : ℝ} (hκ : 0 < κ) (hq : 0 < q) :
    0 < progressRate κ q := by
  unfold progressRate
  positivity

lemma stopped_weight {P T W κ q : ℝ} (hq : 0 < q)
    (hT : T ≤ κ*P) (hW : W ≤ 6*P+T/q) :
    W ≤ (6+κ/q)*P := by
  have hh := div_le_div_of_nonneg_right hT hq.le
  calc
    W ≤ 6*P+T/q := hW
    _ ≤ 6*P+(κ*P)/q := add_le_add le_rfl hh
    _ = _ := by ring

lemma first_stage_progress {P T W κ q : ℝ} (hP : 0 < P)
    (hκ : 0 < κ) (hq : 0 < q) (hT : κ*P < T)
    (hTW : T ≤ W) (hW : W ≤ 6*P+T/q) :
    progressRate κ q ≤ T/(2*W) := by
  have hT0 : 0 < T := (mul_pos hκ hP).trans hT
  have hW0 : 0 < W := hT0.trans_le hTW
  have hupper : 0 < 6*P+T/q := by positivity
  have hden : 0 < 2*(6+κ/q) := by positivity
  calc
    progressRate κ q ≤ T/(2*(6*P+T/q)) := by
      unfold progressRate
      apply (div_le_div_iff₀ hden (mul_pos (by norm_num) hupper)).mpr
      simp only [div_eq_mul_inv]
      nlinarith
    _ ≤ T/(2*W) := by
      apply div_le_div_of_nonneg_left hT0.le (mul_pos (by norm_num) hW0)
      linarith

lemma bounded_weight_progress {P E W κ q : ℝ} (hP : 0 < P)
    (hκ : 0 < κ) (hq : 0 < q) (hE : κ*P < E)
    (hEW : E ≤ W) (hW : W ≤ (6+κ/q)*P) :
    progressRate κ q ≤ E/(2*W) := by
  have hE0 : 0 < E := (mul_pos hκ hP).trans hE
  have hW0 : 0 < W := hE0.trans_le hEW
  have hupper : 0 < 2*((6+κ/q)*P) := by positivity
  calc
    progressRate κ q = (κ*P)/(2*((6+κ/q)*P)) := by
      unfold progressRate
      field_simp
    _ ≤ E/(2*((6+κ/q)*P)) := div_le_div_of_nonneg_right hE.le hupper.le
    _ ≤ E/(2*W) := by
      apply div_le_div_of_nonneg_left hE0.le (mul_pos (by norm_num) hW0)
      linarith

lemma exponential_log_polynomial {c L₀ N : ℝ} (hc : 0 ≤ c) (hN : 1 ≤ N)
    {m d : ℕ} (hm : (m : ℝ) ≤ L₀*Real.log N) (hd : c*L₀ ≤ d) :
    Real.exp (c*m) ≤ N^d := by
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  calc
    Real.exp (c*m) ≤ Real.exp ((c*L₀)*Real.log N) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hm hc]
    _ ≤ Real.exp ((d : ℝ)*Real.log N) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hd hlog)
    _ = N^d := by
      rw [Real.exp_nat_mul, Real.exp_log (show 0 < N by linarith)]

end MetricKMedianRecovery.RefinedRecovery.Analysis

end OAI
