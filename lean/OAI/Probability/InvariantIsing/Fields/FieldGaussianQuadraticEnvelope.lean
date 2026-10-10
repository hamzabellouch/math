import OAI.Probability.InvariantIsing.Fields.FieldGaussianIntegrability

namespace OAI

/-! A Gaussian exponential envelope for the quadratic affine-noise terms
appearing in second covariance derivatives. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma field_one_add_abs_sq_le_exp (u : ℝ) :
    (1 + |u|) ^ 2 ≤ Real.exp (2 * |u|) := by
  have h : 1 + |u| ≤ Real.exp |u| := by linarith [Real.add_one_le_exp |u|]
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |u|) h 2
  calc
    (1 + |u|) ^ 2 ≤ (Real.exp |u|) ^ 2 := hs
    _ = Real.exp (2 * |u|) := by rw [two_mul, Real.exp_add]; ring

lemma field_gaussian_quadratic_envelope_integrable (C L : ℝ) :
    Integrable (fun u : ℝ => Real.exp (C + L * |u|) * (1 + |u|) ^ 2)
      (gaussianReal 0 1) := by
  have hi := ((gaussianReal_exponentialNormMoments 0 1) (L + 2)).const_mul (Real.exp C)
  apply hi.mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro u
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  change Real.exp (C + L * |u|) * (1 + |u|) ^ 2 ≤
    Real.exp C * Real.exp ((L + 2) * |u|)
  calc
    _ ≤ Real.exp (C + L * |u|) * Real.exp (2 * |u|) :=
      mul_le_mul_of_nonneg_left (field_one_add_abs_sq_le_exp u) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end InvariantIsing

end

end OAI
