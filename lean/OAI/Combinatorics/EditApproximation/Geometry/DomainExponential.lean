import OAI.Combinatorics.EditApproximation.Geometry.DomainCounts

namespace OAI

/-! The exponential form of the actual domain bound used in amplification. -/

namespace EditApproximation

theorem computed_labeledStateCount_exp (N nx ny : ℕ) (hN : 0 < N)
    (hnx : nx ≤ N) (hny : ny ≤ N) (hell : 200 ≤ inputSmallLog N) :
    (labeledStateCount (integerParameters N).M nx ny : ℝ) ≤
      Real.exp (10 * inputHeight N) := by
  have hcount : (labeledStateCount (integerParameters N).M nx ny : ℝ) ≤
      (2 : ℝ) ^ (5 * inputHeight N) := by
    exact_mod_cast computed_labeledStateCount_le N nx ny hN hnx hny hell
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  have hpower := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo (5 * inputHeight N)
  rw [← Real.exp_nat_mul, mul_one] at hpower
  apply hcount.trans (hpower.trans (Real.exp_le_exp.mpr ?_))
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith [show (0 : ℝ) ≤ inputHeight N from Nat.cast_nonneg _]

end EditApproximation

end OAI
