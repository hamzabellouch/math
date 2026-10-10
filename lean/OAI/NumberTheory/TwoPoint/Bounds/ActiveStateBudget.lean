import OAI.NumberTheory.TwoPoint.Bounds.ActiveStateExpansion

namespace OAI

/-! The complete low-degree state family fits the scalar-comparison budget. -/

namespace TwoPointCorrelations

lemma active_state_family_cost (L : ℝ) (n M R : ℕ)
    (hL : 4800 ≤ L) (hn : (n : ℝ) ≤ Real.exp L)
    (hM : (M : ℝ) ≤ 400 * Real.log L) (hR : (R : ℝ) ≤ 4 * L) :
    (((M + 1) * (n + 1) ^ M : ℕ) : ℝ) ^ R ≤ Real.exp (L ^ 4) := by
  have hLp : 0 ≤ L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hexp : (2 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hn' : (n : ℝ) + 1 ≤ Real.exp (2 * L) := by
    have he : Real.exp (2 * L) = Real.exp L * Real.exp L := by
      rw [show 2 * L = L + L by ring, Real.exp_add]
    rw [he]
    nlinarith
  have hM' : (M : ℝ) + 1 ≤ Real.exp (400 * Real.log L) := by
    linarith [Real.add_one_le_exp (400 * Real.log L)]
  have hbase : (((M + 1) * (n + 1) ^ M : ℕ) : ℝ) ≤
      Real.exp (1200 * L * Real.log L) := by
    push_cast
    calc
      _ ≤ Real.exp (400 * Real.log L) * (Real.exp (2 * L)) ^ M :=
        mul_le_mul hM' (pow_le_pow_left₀ (by positivity) hn' M) (by positivity) (by positivity)
      _ = Real.exp (400 * Real.log L + M * (2 * L)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_right hM (show 0 ≤ 2 * L by positivity)
        have hl := mul_le_mul_of_nonneg_right (show 1 ≤ L by linarith) hlog
        nlinarith
  have hlogL : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  calc
    _ ≤ (Real.exp (1200 * L * Real.log L)) ^ R :=
      pow_le_pow_left₀ (by positivity) hbase R
    _ = Real.exp (R * (1200 * L * Real.log L)) := by rw [Real.exp_nat_mul]
    _ ≤ Real.exp (4800 * L ^ 3) := by
      apply Real.exp_le_exp.mpr
      have hr := mul_le_mul_of_nonneg_right hR
        (show 0 ≤ 1200 * L * Real.log L by positivity)
      have hl := mul_le_mul_of_nonneg_left hlogL (show 0 ≤ 4800 * L ^ 2 by positivity)
      nlinarith
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (show 0 ≤ L - 4800 by linarith) (pow_nonneg hLp 3)]

end TwoPointCorrelations

end OAI
