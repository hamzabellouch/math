import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! The effective numerical tail in source `eq:residual-tail`, including its
strict final inequality and its validity already at the threshold group size. -/

namespace MatroidProphet.SourceProof

lemma residual_exponent_coefficient :
    1000 * Real.log densityThreshold / densityThreshold - residualDelta * Real.log 2 ≤
      -((2 : ℝ)^27)⁻¹ * Real.log 2 := by
  have hl : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  unfold densityThreshold residualDelta
  rw [Real.log_pow]
  norm_num
  nlinarith

/-- Exact effective exponential bound at the smallest analyzed group size. -/
theorem residual_tail_exact (N : ℝ) (hN : densityThreshold ≤ N) :
    Real.exp ((1000 * Real.log densityThreshold / densityThreshold -
      residualDelta * Real.log 2) * N) ≤
        Real.exp (-((2 : ℝ)^73) * Real.log 2) ∧
      Real.exp (-((2 : ℝ)^73) * Real.log 2) < residualDelta := by
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hN0 : 0 ≤ N := constants_positive.2.1.le.trans hN
  have hc : -((2 : ℝ)^27)⁻¹ * Real.log 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num) hl.le
  constructor
  · apply Real.exp_le_exp.mpr
    calc
      _ ≤ (-((2 : ℝ)^27)⁻¹ * Real.log 2) * N :=
        mul_le_mul_of_nonneg_right residual_exponent_coefficient hN0
      _ ≤ (-((2 : ℝ)^27)⁻¹ * Real.log 2) * densityThreshold :=
        mul_le_mul_of_nonpos_left hN hc
      _ = -((2 : ℝ)^73) * Real.log 2 := by
        norm_num [densityThreshold]
        ring
  · have hpow : (26 : ℝ) < (2 : ℝ)^73 := by norm_num
    have he : Real.exp (-((2 : ℝ)^73) * Real.log 2) <
        Real.exp (-(26 * Real.log 2)) := by
      apply Real.exp_lt_exp.mpr
      nlinarith
    have hid : Real.exp (-(26 * Real.log (2 : ℝ))) = residualDelta := by
      rw [Real.exp_neg]
      have h := Real.exp_nat_mul (Real.log (2 : ℝ)) 26
      norm_num at h
      rw [h, Real.exp_log (by norm_num)]
      rfl
    rwa [hid] at he

end MatroidProphet.SourceProof

end OAI
