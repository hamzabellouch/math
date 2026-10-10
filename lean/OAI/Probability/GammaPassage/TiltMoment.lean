import OAI.Probability.GammaPassage.TiltDensity
import OAI.Probability.GammaPassage.MGF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

namespace GammaFPP

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

private noncomputable def squareTheta (rate delta : ℝ) : ℝ :=
  -(2 * rate * ((1 - delta)⁻¹ - 1))

private lemma shrink_likelihood_sq (shape rate delta x : ℝ) :
    gammaShrinkLikelihood shape rate delta x ^ 2 =
      ((1 - delta) ^ (-shape)) ^ 2 * exp (squareTheta rate delta * x) := by
  unfold gammaShrinkLikelihood gammaScaleLikelihood squareTheta
  rw [mul_pow, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  congr 1
  congr 1
  ring

private lemma square_shifted_rate (rate : ℝ) {delta : ℝ} (hdelta : delta < 1) :
    rate - squareTheta rate delta = rate * (1 + delta) / (1 - delta) := by
  unfold squareTheta
  field_simp [(sub_pos.mpr hdelta).ne']; ring

private lemma squareTheta_lt_rate {rate delta : ℝ}
    (hrate : 0 < rate) (hlo : -1 < delta) (hhi : delta < 1) :
    squareTheta rate delta < rate := by
  apply sub_pos.mp
  rw [square_shifted_rate rate hhi]
  exact div_pos (mul_pos hrate (by linarith)) (sub_pos.mpr hhi)

private lemma square_moment_coefficient {shape rate delta : ℝ}
    (hrate : 0 < rate) (hlo : -1 < delta) (hhi : delta < 1) :
    ((1 - delta) ^ (-shape)) ^ 2 *
        (rate / (rate - squareTheta rate delta)) ^ shape =
      (1 - delta ^ 2) ^ (-shape) := by
  have ha : 0 < 1 - delta := sub_pos.mpr hhi
  have hb : 0 < 1 + delta := by linarith
  have hd : 0 < 1 - delta ^ 2 := by
    have he : 1 - delta ^ 2 = (1 - delta) * (1 + delta) := by ring
    rw [he]
    exact mul_pos ha hb
  have hratio : rate / (rate - squareTheta rate delta) = (1 - delta) / (1 + delta) := by
    rw [square_shifted_rate rate hhi]
    field_simp [hrate.ne', ha.ne', hb.ne']
  have hbase : ((1 - delta)⁻¹) ^ 2 * ((1 - delta) / (1 + delta)) =
      (1 - delta ^ 2)⁻¹ := by
    field_simp [ha.ne', hb.ne', hd.ne']; ring
  rw [hratio]
  calc
    ((1 - delta) ^ (-shape)) ^ 2 * ((1 - delta) / (1 + delta)) ^ shape =
        (((1 - delta)⁻¹) ^ 2) ^ shape * ((1 - delta) / (1 + delta)) ^ shape := by
      rw [Real.rpow_neg_eq_inv_rpow,
        Real.rpow_pow_comm (inv_nonneg.mpr ha.le) shape 2]
    _ = (((1 - delta)⁻¹) ^ 2 * ((1 - delta) / (1 + delta))) ^ shape :=
      (Real.mul_rpow (sq_nonneg _) (div_nonneg ha.le hb.le)).symm
    _ = ((1 - delta ^ 2)⁻¹) ^ shape := by rw [hbase]
    _ = (1 - delta ^ 2) ^ (-shape) :=
      (Real.rpow_neg_eq_inv_rpow (1 - delta ^ 2) shape).symm

/-- The square of the shrinking likelihood is integrable under the Gamma law. -/
theorem gamma_shrink_likelihood_sq_integrable {shape rate delta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (hlo : -1 < delta) (hhi : delta < 1) :
    Integrable (fun x : ℝ => gammaShrinkLikelihood shape rate delta x ^ 2)
      (gammaMeasure shape rate) := by
  have he : (fun x : ℝ => gammaShrinkLikelihood shape rate delta x ^ 2) =
      (fun x : ℝ => ((1 - delta) ^ (-shape)) ^ 2 * exp (squareTheta rate delta * x)) :=
    funext (shrink_likelihood_sq shape rate delta)
  rw [he]
  exact (gamma_integrable_exp hshape hrate (squareTheta_lt_rate hrate hlo hhi)).const_mul _

/-- The second moment of the likelihood for one coordinate. -/
theorem gamma_shrink_likelihood_second_moment {shape rate delta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (hlo : -1 < delta) (hhi : delta < 1) :
    (∫ x : ℝ, gammaShrinkLikelihood shape rate delta x ^ 2 ∂gammaMeasure shape rate) =
      (1 - delta ^ 2) ^ (-shape) := by
  calc
    (∫ x : ℝ, gammaShrinkLikelihood shape rate delta x ^ 2 ∂gammaMeasure shape rate) =
        ∫ x : ℝ, ((1 - delta) ^ (-shape)) ^ 2 * exp (squareTheta rate delta * x)
          ∂gammaMeasure shape rate :=
      integral_congr_ae (Filter.Eventually.of_forall (shrink_likelihood_sq shape rate delta))
    _ = ((1 - delta) ^ (-shape)) ^ 2 *
        (∫ x : ℝ, exp (squareTheta rate delta * x) ∂gammaMeasure shape rate) :=
      integral_const_mul _ _
    _ = ((1 - delta) ^ (-shape)) ^ 2 *
        (rate / (rate - squareTheta rate delta)) ^ shape := by
      rw [gamma_integral_exp hshape hrate (squareTheta_lt_rate hrate hlo hhi)]
    _ = (1 - delta ^ 2) ^ (-shape) := square_moment_coefficient hrate hlo hhi

/-- The nonnegative second moment used in finite-product likelihood arguments. -/
theorem gamma_shrink_likelihood_second_lintegral {shape rate delta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (hlo : -1 < delta) (hhi : delta < 1) :
    (∫⁻ x : ℝ, (ENNReal.ofReal (gammaShrinkLikelihood shape rate delta x)) ^ 2
        ∂gammaMeasure shape rate) = ENNReal.ofReal ((1 - delta ^ 2) ^ (-shape)) := by
  calc
    (∫⁻ x : ℝ, (ENNReal.ofReal (gammaShrinkLikelihood shape rate delta x)) ^ 2
        ∂gammaMeasure shape rate) =
        ∫⁻ x : ℝ, ENNReal.ofReal (gammaShrinkLikelihood shape rate delta x ^ 2)
          ∂gammaMeasure shape rate := by
      apply lintegral_congr
      intro x
      exact (ENNReal.ofReal_pow
        (gammaScaleLikelihood_pos shape rate (sub_pos.mpr hhi) x).le 2).symm
    _ = ENNReal.ofReal (∫ x : ℝ, gammaShrinkLikelihood shape rate delta x ^ 2
        ∂gammaMeasure shape rate) :=
      (ofReal_integral_eq_lintegral_ofReal
        (gamma_shrink_likelihood_sq_integrable hshape hrate hlo hhi)
        (Filter.Eventually.of_forall fun x => sq_nonneg (gammaShrinkLikelihood shape rate delta x))).symm
    _ = ENNReal.ofReal ((1 - delta ^ 2) ^ (-shape)) := by
      rw [gamma_shrink_likelihood_second_moment hshape hrate hlo hhi]

end GammaFPP

end OAI
