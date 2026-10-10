import OAI.Probability.FreeIsing.Conditioning.ShiftedLoss
import OAI.Probability.FreeIsing.Energy.LinearTiltVariance
import OAI.Probability.FreeIsing.Estimates.MessageFunction

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma variance_cavityMessage_linearSignalTilt
    {theta eta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta < 1) (hη : |eta| ≤ 1)
    {Y : Ω → ℝ} (hY : Measurable Y) (T : Ω ≃ᵐ Ω)
    (hT : MeasurePreserving T μ μ) (hYodd : ∀ᵐ w ∂μ, Y (T w) = -Y w) :
    (1 - theta ^ 2) * theta ^ 2 * (∫ w, Real.tanh (Y w) ^ 2 ∂μ) ≤
      variance (fun w => cavityMessage theta (Y w))
        (linearSignalTilt μ (fun w => Real.tanh (Y w)) (eta * theta)) := by
  have hθsq : theta ^ 2 ≤ 1 := by nlinarith
  have hq : Measurable (fun w => Real.tanh (Y w)) :=
    lipschitzWith_tanh_response.continuous.measurable.comp hY
  have hqb : ∀ᵐ w ∂μ, |Real.tanh (Y w)| ≤ 1 :=
    Filter.Eventually.of_forall fun w => (Real.abs_tanh_lt_one _).le
  have ha : |eta * theta| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hθ0]
    calc
      |eta| * theta ≤ 1 * theta := mul_le_mul_of_nonneg_right hη hθ0
      _ ≤ 1 := by simpa using hθ1.le
  have hgMeas : Measurable (fun w => cavityMessage theta (Y w)) :=
    (lipschitzWith_cavityMessage hθ0 hθ1.le).continuous.measurable.comp hY
  have hg : MemLp (fun w => cavityMessage theta (Y w)) 2 μ :=
    MemLp.of_bound hgMeas.aestronglyMeasurable (Real.artanh theta)
      (Filter.Eventually.of_forall fun w => by
        simpa only [Real.norm_eq_abs] using cavityMessage_abs_le_artanh hθ0 hθ1 (Y w))
  apply variance_linearSignalTilt_ge_signal_moment hq hqb ha hg T hT
  · filter_upwards [hYodd] with w hw
    rw [hw, Real.tanh_neg]
  · filter_upwards [hYodd] with w hw
    rw [hw, cavityMessage_neg hθsq]
  · have hηsq := (sq_le_one_iff_abs_le_one eta).mpr hη
    nlinarith [mul_le_mul_of_nonneg_right hηsq (sq_nonneg theta)]
  · exact hθsq
  · filter_upwards [] with w
    have h := cavityMessage_abs_ge_tanh hθsq (Y w)
    have hs := (sq_le_sq₀ (mul_nonneg (abs_nonneg theta) (abs_nonneg _))
      (abs_nonneg _)).mpr h
    simpa only [mul_pow, sq_abs] using hs

def sideSignalLossCoefficient (theta : ℝ) : ℝ :=
  shiftedLossCoefficient theta (Real.artanh theta) * (1 - theta ^ 2) * theta ^ 2

lemma sideSignalLossCoefficient_pos {theta : ℝ} (hθ0 : 0 < theta) (hθ1 : theta < 1) :
    0 < sideSignalLossCoefficient theta := by
  have hθsq : theta ^ 2 < 1 := by nlinarith
  exact mul_pos (mul_pos (shiftedLossCoefficient_pos hθsq) (sub_pos.mpr hθsq))
    (sq_pos_of_pos hθ0)

lemma integral_tilted_cavity_attenuation_le
    {theta eta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta < 1) (hη : |eta| ≤ 1)
    {Y : Ω → ℝ} (hY : Measurable Y) (T : Ω ≃ᵐ Ω)
    (hT : MeasurePreserving T μ μ) (hYodd : ∀ᵐ w ∂μ, Y (T w) = -Y w) (z : ℝ) :
    (∫ w, responseAttenuation theta (z + cavityMessage theta (Y w)) ^ 2
      ∂linearSignalTilt μ (fun w => Real.tanh (Y w)) (eta * theta)) ≤
        1 - sideSignalLossCoefficient theta * (∫ w, Real.tanh (Y w) ^ 2 ∂μ) := by
  have hθsq : theta ^ 2 < 1 := by nlinarith
  have hq : Measurable (fun w => Real.tanh (Y w)) :=
    lipschitzWith_tanh_response.continuous.measurable.comp hY
  have hqb : ∀ᵐ w ∂μ, |Real.tanh (Y w)| ≤ 1 :=
    Filter.Eventually.of_forall fun w => (Real.abs_tanh_lt_one _).le
  have ha : |eta * theta| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hθ0]
    calc
      |eta| * theta ≤ 1 * theta := mul_le_mul_of_nonneg_right hη hθ0
      _ ≤ 1 := by simpa using hθ1.le
  have hqodd : ∀ᵐ w ∂μ, Real.tanh (Y (T w)) = -Real.tanh (Y w) := by
    filter_upwards [hYodd] with w hw
    rw [hw, Real.tanh_neg]
  let := linearSignalTilt_probability hq hqb ha
    (integral_eq_zero_of_ae_sign_reversal T hT hqodd)
  have hgMeas : Measurable (fun w => cavityMessage theta (Y w)) :=
    (lipschitzWith_cavityMessage hθ0 hθ1.le).continuous.measurable.comp hY
  have hloss := integral_shifted_attenuation_loss_explicit
    (μ := linearSignalTilt μ (fun w => Real.tanh (Y w)) (eta * theta)) hθsq.le hgMeas
    (Filter.Eventually.of_forall fun w => cavityMessage_abs_le_artanh hθ0 hθ1 (Y w)) z
  have hvariance := variance_cavityMessage_linearSignalTilt hθ0 hθ1 hη hY T hT hYodd
  have hmul := mul_le_mul_of_nonneg_left hvariance
    (shiftedLossCoefficient_pos (beta := Real.artanh theta) hθsq).le
  unfold sideSignalLossCoefficient
  nlinarith [hloss]

end Problem367

end

end OAI
