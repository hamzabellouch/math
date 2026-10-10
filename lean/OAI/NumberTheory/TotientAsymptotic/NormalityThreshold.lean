import OAI.NumberTheory.TotientAsymptotic.NormalitySmallParameter

namespace OAI

/-! Explicit elementary conditions above one fixed endpoint threshold. -/
noncomputable section
namespace TotientAsymptotic

lemma normality_threshold_conditions {N : ℕ} (hN : 3 < N) (hB : 400 ≤ B N) :
    Real.exp 2 ≤ (N:ℝ) ∧ 1 ≤ B N ∧ 1 ≤ Real.log N/(200*B N) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hquad := Real.quadratic_le_exp_of_nonneg (show 0 ≤ B N by linarith)
  rw [show Real.exp (B N)=Real.log N from Real.exp_log hlog] at hquad
  have hlogbig : 200*B N ≤ Real.log N := by
    nlinarith [mul_nonneg (show 0 ≤ B N by linarith) (show 0 ≤ B N-400 by linarith)]
  refine ⟨(Real.le_log_iff_exp_le hN0).mp (by nlinarith),by linarith,?_⟩
  exact (one_le_div (show 0 < 200*B N by positivity)).mpr hlogbig

lemma normality_large_S_threshold {N : ℕ} {S : ℝ} (hB : 400 ≤ B N)
    (hsmall : (B N)^30 ≤ Real.log S) : 4 ≤ B S := by
  have hB0 : 0 < B N := by linarith
  have he : Real.exp 1 ≤ B N := Real.exp_one_lt_three.le.trans (by linarith)
  have hl : 1 ≤ Real.log (B N) := (Real.le_log_iff_exp_le hB0).mpr he
  have hh := Real.log_le_log (pow_pos hB0 30) hsmall
  rw [Real.log_pow] at hh
  change 30*Real.log (B N) ≤ B S at hh
  linarith

end TotientAsymptotic

end

end OAI
