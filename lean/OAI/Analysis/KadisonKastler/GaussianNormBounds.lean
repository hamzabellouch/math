import OAI.Analysis.KadisonKastler.GaussianStateDerivative

namespace OAI

/-! # Uniform norm bounds on Gaussian analytic orbits -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem gaussianStateAverage_norm_of_im_le
    (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (R : ℝ) (hR : 0 ≤ R)
    (z : ℂ) (hz : |z.im| ≤ R) :
    ‖gaussianStateAverage U hU a r hr z‖ ≤
      Real.exp (r * R ^ 2) * Real.sqrt (Real.pi / r) * ‖a‖ := by
  apply (gaussianStateAverage_norm U hU a r hr z).trans
  have hs : z.im ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).2 hz
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs hr.le)) (Real.sqrt_nonneg _))
    (norm_nonneg a)

theorem gaussianStateAverage_norm_of_norm_le
    (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (R : ℝ) (hR : 0 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖gaussianStateAverage U hU a r hr z‖ ≤
      Real.exp (r * R ^ 2) * Real.sqrt (Real.pi / r) * ‖a‖ :=
  gaussianStateAverage_norm_of_im_le U hU a r hr R hR z
    ((Complex.abs_im_le_norm z).trans hz)

end

end KadisonKastler

end OAI
