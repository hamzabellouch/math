import OAI.Probability.InvariantIsing.Fields.FieldGaussianIntegrability
import OAI.Probability.InvariantIsing.Fields.FieldParameterGrowth

namespace OAI

/-! A uniform second-moment envelope for scalar Gaussian tilts whose
centered potential is Lipschitz. This supplies the finite-dimensional
Hessian differentiation without assuming higher spatial derivatives. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def fieldGaussianMomentCap (C : ℝ) : ℝ :=
  (∫ u : ℝ, 4 * Real.exp ((C + 2) * |u|) ∂gaussianReal 0 1) /
    (∫ u : ℝ, Real.exp (-C * |u|) ∂gaussianReal 0 1)

private lemma quadratic_exp_envelope (C u : ℝ) :
    Real.exp (C * |u|) * (1 + |u|) ^ 2 ≤ 4 * Real.exp ((C + 2) * |u|) := by
  have h1 : 1 ≤ Real.exp |u| := Real.one_le_exp (abs_nonneg u)
  have h2 : |u| ≤ Real.exp |u| := by linarith [Real.add_one_le_exp |u|]
  have h3 : (1 + |u|) ^ 2 ≤ (2 * Real.exp |u|) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  calc
    _ ≤ Real.exp (C * |u|) * (2 * Real.exp |u|) ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = 4 * Real.exp ((C + 2) * |u|) := by
      rw [show (C + 2) * |u| = C * |u| + (|u| + |u|) by ring,
        Real.exp_add, Real.exp_add]
      ring

theorem field_centered_tilt_second_moment {U : ℝ → ℝ}
    (hU : Measurable U) {C : ℝ}
    (hUb : ∀ u, |U u| ≤ C * |u|) :
    Integrable (fun u : ℝ => (1 + |u|) ^ 2) ((gaussianReal 0 1).tilted U) ∧
      (∫ u : ℝ, (1 + |u|) ^ 2 ∂(gaussianReal 0 1).tilted U) ≤ fieldGaussianMomentCap C := by
  let μ := gaussianReal 0 1
  have hexp : Integrable (fun u : ℝ => Real.exp (C * |u|)) μ := by
    simpa only [Real.norm_eq_abs] using (gaussianReal_exponentialNormMoments 0 1 C)
  have hlo : Integrable (fun u : ℝ => Real.exp (-C * |u|)) μ := by
    simpa only [Real.norm_eq_abs] using (gaussianReal_exponentialNormMoments 0 1 (-C))
  have hhi : Integrable (fun u : ℝ => 4 * Real.exp ((C + 2) * |u|)) μ := by
    simpa only [Real.norm_eq_abs] using
      ((gaussianReal_exponentialNormMoments 0 1 (C + 2)).const_mul 4)
  have hUi : Integrable (fun u => Real.exp (U u)) μ :=
    hexp.mono' hU.exp.aestronglyMeasurable (Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hUb u)))
  have hprod : Integrable (fun u => Real.exp (U u) * (1 + |u|) ^ 2) μ :=
    hhi.mono' (hU.exp.mul (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact (mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr ((le_abs_self _).trans (hUb u))) (sq_nonneg _)).trans
            (quadratic_exp_envelope C u))
  have hdenpos : 0 < ∫ u : ℝ, Real.exp (-C * |u|) ∂μ :=
    integral_pos_iff_support_of_nonneg (fun u => (Real.exp_pos _).le) hlo |>.mpr
      (by simp [Function.support, Real.exp_ne_zero, μ])
  have hden : (∫ u : ℝ, Real.exp (-C * |u|) ∂μ) ≤ ∫ u, Real.exp (U u) ∂μ :=
    integral_mono hlo hUi (fun u => Real.exp_le_exp.mpr (by
      have h := (abs_le.mp (hUb u)).1
      linarith))
  have hnum : (∫ u, Real.exp (U u) * (1 + |u|) ^ 2 ∂μ) ≤
      ∫ u : ℝ, 4 * Real.exp ((C + 2) * |u|) ∂μ :=
    integral_mono hprod hhi (fun u =>
      (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr ((le_abs_self _).trans (hUb u))) (sq_nonneg _)).trans
          (quadratic_exp_envelope C u))
  constructor
  · rw [integrable_tilted_iff hUi]
    simpa only [smul_eq_mul] using hprod
  · rw [integral_tilted_eq_div]
    exact div_le_div₀ (integral_nonneg (fun u => by positivity)) hnum hdenpos hden

end InvariantIsing

end

end OAI
