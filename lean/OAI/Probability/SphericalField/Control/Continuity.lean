import Mathlib
import OAI.Probability.SphericalField.Control.Truncation

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma controlValue_trial_sub_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m n : Trial) (L : ℝ≥0) (hf : LipschitzWith L f) :
    controlValue P f m - controlValue P f n ≤
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw := by
  suffices controlValue P f m ≤ controlValue P f n +
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw by linarith
  apply controlValue_le_of_bounded_controls P f m L hf
  intro v hv _ hbound
  have hpay : controlPayoff P f n v ≤ controlValue P f n :=
    le_csSup (controlPayoffs_bddAbove P f n) ⟨v, hv,
      (controlCost_le_bound P n L hbound).trans_lt (by finiteness), rfl⟩
  have hd := (abs_le.mp (controlPayoff_trial_diff_bound P f m n L hf hv hbound)).2
  linarith

lemma controlValue_trial_abs_sub_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m n : Trial) (L : ℝ≥0) (hf : LipschitzWith L f) :
    |controlValue P f m - controlValue P f n| ≤
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw := by
  have hmn := controlValue_trial_sub_le P f m n L hf
  have hnm := controlValue_trial_sub_le P f n m L hf
  simp_rw [abs_sub_comm (n _) (m _)] at hnm
  exact abs_le.mpr ⟨by linarith, hmn⟩

lemma usual_measurable_aemeasurable (P : Measure BrownianPath) (t : Time)
    {Y : BrownianPath → ℝ} (hY : @Measurable _ _ (usualBrownianSigma P t) (borel ℝ) Y) :
    AEMeasurable Y P := by
  have h : NullMeasurable Y P := hY.mono (usualBrownianSigma_le_completion P t) le_rfl
  exact h.aemeasurable

lemma brownian_increment_indep_adapted (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (t : Time) (r : ℝ≥0) (htr : (t : ℝ) < r)
    {Y : BrownianPath → ℝ} (hY : @Measurable _ _ (usualBrownianSigma P t) (borel ℝ) Y) :
    IndepFun Y (fun ω => brownianEval r ω - brownianEval ⟨t.val, (show 0 ≤ (t : ℝ) from t.property.1)⟩ ω) P :=
  indep_of_indep_of_le_left (brownian_increment_indep_usual P hB t r htr) hY.comap_le

lemma second_order_taylor_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (C : ℝ) (hC : ∀ x, |iteratedDeriv 3 f x| ≤ C) (x y : ℝ) :
    |f y - f x - deriv f x * (y-x) - iteratedDeriv 2 f x * (y-x)^2/2| ≤
      C * |y-x|^3 / 6 := by
  by_cases hxy : x = y
  · subst y; simp
  have hs := uniqueDiffOn_uIcc hxy
  have hd₁ : iteratedDerivWithin 1 f (uIcc x y) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs ((hf.of_le (by norm_num)).contDiffAt)
      left_mem_uIcc, iteratedDeriv_one]
  have hd₂ : iteratedDerivWithin 2 f (uIcc x y) x = iteratedDeriv 2 f x :=
    iteratedDerivWithin_eq_iteratedDeriv hs ((hf.of_le (by norm_num)).contDiffAt)
      left_mem_uIcc
  have hp : taylorWithinEval f 2 (uIcc x y) x y =
      f x + deriv f x * (y-x) + iteratedDeriv 2 f x * (y-x)^2/2 := by
    rw [show (2 : ℕ) = 1+1 from rfl, taylorWithinEval_succ,
      taylorWithinEval_succ, taylor_within_zero_eval, hd₁, hd₂]
    norm_num
    ring
  obtain ⟨z, -, hz⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hxy hf.contDiffOn
  rw [hp] at hz
  have he : f y - f x - deriv f x * (y-x) - iteratedDeriv 2 f x * (y-x)^2/2 =
      iteratedDeriv 3 f z * (y-x)^3/6 := by
    norm_num at hz
    linarith only [hz]
  rw [he, abs_div, abs_mul, abs_pow]
  norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hC z) (by positivity)) (by norm_num)

lemma first_order_taylor_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (C : ℝ) (hC : ∀ x, |iteratedDeriv 2 f x| ≤ C) (x y : ℝ) :
    |f y - f x - deriv f x * (y-x)| ≤ C * (y-x)^2 / 2 := by
  by_cases hxy : x = y
  · subst y; simp
  have hs := uniqueDiffOn_uIcc hxy
  have hd : iteratedDerivWithin 1 f (uIcc x y) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs ((hf.of_le (by norm_num)).contDiffAt)
      left_mem_uIcc, iteratedDeriv_one]
  have hp : taylorWithinEval f 1 (uIcc x y) x y = f x + deriv f x * (y-x) := by
    rw [show (1 : ℕ) = 0+1 from rfl, taylorWithinEval_succ, taylor_within_zero_eval, hd]
    norm_num
    ring
  obtain ⟨z, -, hz⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hxy hf.contDiffOn
  rw [hp] at hz
  have he : f y - f x - deriv f x * (y-x) = iteratedDeriv 2 f z * (y-x)^2/2 := by
    norm_num at hz
    linarith only [hz]
  rw [he, abs_div, abs_mul, abs_of_nonneg (sq_nonneg (y-x))]
  norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hC z) (sq_nonneg _)) (by norm_num)

lemma smooth_deriv_lipschitz {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (C : ℝ≥0) (hC : ∀ x, |iteratedDeriv 2 f x| ≤ C) : LipschitzWith C (deriv f) := by
  apply lipschitzWith_of_nnnorm_deriv_le hf.differentiable_deriv_two
  intro x
  apply NNReal.coe_le_coe.mp
  simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero, coe_nnnorm, Real.norm_eq_abs] using hC x

lemma drift_shift_taylor_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (C : ℝ≥0) (hC : ∀ x, |iteratedDeriv 2 f x| ≤ C) (x z a : ℝ) :
    |f (x+z+a) - f (x+z) - deriv f x * a| ≤ (C : ℝ) * (|z| * |a| + a^2/2) := by
  have ht := first_order_taylor_bound hf C hC (x+z) (x+z+a)
  simp only [add_sub_cancel_left] at ht
  have hd := (smooth_deriv_lipschitz hf C hC).dist_le_mul (x+z) x
  simp only [Real.dist_eq, add_sub_cancel_left] at hd
  calc
    _ = |(f (x+z+a) - f (x+z) - deriv f (x+z) * a) + (deriv f (x+z) - deriv f x) * a| := by congr 1; ring
    _ ≤ |f (x+z+a) - f (x+z) - deriv f (x+z) * a| + |(deriv f (x+z) - deriv f x) * a| := abs_add_le _ _
    _ ≤ (C : ℝ) * a^2/2 + (C : ℝ) * |z| * |a| := by
      rw [abs_mul]
      exact add_le_add ht (mul_le_mul_of_nonneg_right hd (abs_nonneg _))
    _ = _ := by ring

end SphericalPerceptron
end
end

end OAI
