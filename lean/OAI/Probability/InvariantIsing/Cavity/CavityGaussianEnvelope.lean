import OAI.Probability.InvariantIsing.Cavity.CavityGaussianRadialMoments
import Mathlib.Probability.Distributions.Gaussian.Fernique

namespace OAI

/-! Uniform polynomial-exponential moments for the finite Gaussian marks
after the quadratic tilt. Only the norm of the covariance factor matters. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace InvariantIsing

lemma cavity_standardGaussian_exp_norm_integrable (d : ℕ) (c : ℝ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => Real.exp (c * ‖z‖)) (stdGaussian _) := by
  obtain ⟨a, ha, hi⟩ := IsGaussian.exists_integrable_exp_sq (stdGaussian (EuclideanSpace ℝ (Fin d)))
  let b := c^2 / (4 * a)
  have hb : 4 * a * b = c^2 := mul_div_cancel₀ _ (by positivity)
  apply (hi.const_mul (Real.exp b)).mono' (by fun_prop)
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hs := sq_nonneg (2 * a * ‖z‖ - c)
    nlinarith

lemma cavity_polynomial_exp_bound (p : ℕ) (c r : ℝ) (hr : 0 ≤ r) :
    r^p * Real.exp (c * r) ≤ Real.exp ((p + c) * r) := by
  have he : r ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  have hp := pow_le_pow_left₀ hr he p
  have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos (c * r)).le
  rw [← Real.exp_nat_mul, ← Real.exp_add] at hm
  simpa only [add_mul] using hm

theorem cavity_gaussian_linear_polynomial_exp_bound {d q : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin q))
    {M c : ℝ} (_hM : 0 ≤ M) (hL : ‖L‖ ≤ M) (hc : 0 ≤ c) (p : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => ‖L z‖^p * Real.exp (c * ‖L z‖))
      (stdGaussian _) ∧
    (∫ z : EuclideanSpace ℝ (Fin d), ‖L z‖^p * Real.exp (c * ‖L z‖) ∂stdGaussian _) ≤
      ∫ z : EuclideanSpace ℝ (Fin d), Real.exp (((p : ℝ) + c) * M * ‖z‖) ∂stdGaussian _ := by
  have hi := cavity_standardGaussian_exp_norm_integrable d (((p : ℝ) + c) * M)
  have hb z : ‖L z‖^p * Real.exp (c * ‖L z‖) ≤ Real.exp (((p : ℝ) + c) * M * ‖z‖) := by
    have hn : ‖L z‖ ≤ M * ‖z‖ := (L.le_opNorm z).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg z))
    apply (cavity_polynomial_exp_bound p c ‖L z‖ (norm_nonneg _)).trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hn (add_nonneg (Nat.cast_nonneg p) hc)]
  have hif : Integrable (fun z : EuclideanSpace ℝ (Fin d) => ‖L z‖^p * Real.exp (c * ‖L z‖))
      (stdGaussian _) := by
    apply hi.mono' (by fun_prop)
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hb z
  exact ⟨hif, integral_mono hif hi hb⟩

end InvariantIsing

end

end OAI
