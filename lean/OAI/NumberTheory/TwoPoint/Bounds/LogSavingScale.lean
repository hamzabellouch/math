import OAI.NumberTheory.TwoPoint.Bounds.QuantitativeParameterChoice

namespace OAI

/-! Convert the fixed prime-count saving into the final logarithmic
power, retaining a single exponent for all affine coefficients. -/

namespace TwoPointCorrelations

lemma primeSupplyCount_log_saving (X W : ℝ) (A : ℕ) (hX : Real.exp 1 ≤ X)
    (hW : 0 < W) (hA : 0 < A) :
    Real.exp (-(primeSupplyCount W ((Real.log X) ^ (1 / (A : ℝ))) : ℝ)) ≤
      Real.exp 1 / (Real.log X) ^ (1 / (1200 * W * A) : ℝ) := by
  have hlog : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hX
  have hlogp : 0 < Real.log X := by linarith
  have hL : 1 ≤ (Real.log X) ^ (1 / (A : ℝ)) :=
    Real.one_le_rpow hlog (by positivity)
  have hp := primeSupplyCount_saving ((Real.log X) ^ (1 / (A : ℝ))) W hL hW
  apply hp.trans_eq
  rw [← Real.rpow_mul hlogp.le]
  have he : (1 / (A : ℝ)) * (-(1 / (1200 * W))) = -(1 / (1200 * W * A)) := by ring
  rw [he, Real.rpow_neg hlogp.le]
  rfl

lemma log_saving_exponent_pos (W : ℝ) (A : ℕ) (hW : 0 < W) (hA : 0 < A) :
    0 < (1 / (1200 * W * A) : ℝ) := by positivity

end TwoPointCorrelations

end OAI
