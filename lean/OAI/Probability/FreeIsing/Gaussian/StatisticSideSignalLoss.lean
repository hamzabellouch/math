import OAI.Probability.FreeIsing.Gaussian.SideSignalLoss

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

def statisticMessage (theta q : ℝ) : ℝ := Real.artanh (theta * q)

theorem measurable_statisticMessage (theta : ℝ) : Measurable (statisticMessage theta) := by
  unfold statisticMessage Real.artanh
  fun_prop

theorem statisticMessage_argument_mem {theta q : ℝ}
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1) (hq : |q| ≤ 1) :
    theta * q ∈ Set.Ioo (-1 : ℝ) 1 := by
  apply abs_lt.mp
  rw [abs_mul, abs_of_nonneg hθ0]
  exact (mul_le_mul_of_nonneg_left hq hθ0).trans_lt (by simpa using hθ1)

theorem statisticMessage_abs_le {theta q : ℝ}
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1) (hq : |q| ≤ 1) :
    |statisticMessage theta q| ≤ Real.artanh theta := by
  have hm := statisticMessage_argument_mem hθ0 hθ1 hq
  have hupper : Real.artanh (theta * q) ≤ Real.artanh theta := by
    apply Real.artanh_le_artanh hm.1 hθ1
    simpa using mul_le_mul_of_nonneg_left (abs_le.mp hq).2 hθ0
  have hneg : Real.artanh (-(theta * q)) ≤ Real.artanh theta := by
    apply Real.artanh_le_artanh (by linarith [hm.2]) hθ1
    nlinarith [(abs_le.mp hq).1]
  rw [artanh_neg_of_mem hm] at hneg
  exact abs_le.mpr ⟨by simpa only [statisticMessage, neg_neg] using (neg_le_neg hneg), hupper⟩

theorem statisticMessage_abs_ge {theta q : ℝ}
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1) (hq : |q| ≤ 1) :
    theta * |q| ≤ |statisticMessage theta q| := by
  have h := abs_tanh_le_abs_response (Real.artanh (theta * q))
  rw [Real.tanh_artanh (statisticMessage_argument_mem hθ0 hθ1 hq),
    abs_mul, abs_of_nonneg hθ0] at h
  exact h

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem variance_statisticMessage_linearSignalTilt
    {theta eta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta < 1) (hη : |eta| ≤ 1)
    {q : Ω → ℝ} (hq : Measurable q) (hqb : ∀ᵐ w ∂μ, |q w| ≤ 1)
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hqodd : ∀ᵐ w ∂μ, q (T w) = -q w) :
    (1 - theta ^ 2) * theta ^ 2 * (∫ w, q w ^ 2 ∂μ) ≤
      variance (fun w => statisticMessage theta (q w))
        (linearSignalTilt μ q (eta * theta)) := by
  have hθsq : theta ^ 2 ≤ 1 := by nlinarith
  have ha : |eta * theta| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hθ0]
    exact (mul_le_mul_of_nonneg_right hη hθ0).trans (by simpa using hθ1.le)
  have hg : MemLp (fun w => statisticMessage theta (q w)) 2 μ :=
    MemLp.of_bound ((measurable_statisticMessage theta).comp hq).aestronglyMeasurable
      (Real.artanh theta) (by
        filter_upwards [hqb] with w hw
        simpa only [Real.norm_eq_abs] using statisticMessage_abs_le hθ0 hθ1 hw)
  apply variance_linearSignalTilt_ge_signal_moment hq hqb ha hg T hT hqodd
  · filter_upwards [hqodd, hqb] with w hw hb
    simp only [statisticMessage, hw, mul_neg]
    exact artanh_neg_of_mem (statisticMessage_argument_mem hθ0 hθ1 hb)
  · have hηsq := (sq_le_one_iff_abs_le_one eta).mpr hη
    nlinarith [mul_le_mul_of_nonneg_right hηsq (sq_nonneg theta)]
  · exact hθsq
  · filter_upwards [hqb] with w hw
    have hs := (sq_le_sq₀ (mul_nonneg hθ0 (abs_nonneg _)) (abs_nonneg _)).mpr
      (statisticMessage_abs_ge hθ0 hθ1 hw)
    simpa only [mul_pow, sq_abs] using hs

theorem integral_tilted_statistic_attenuation_le
    {theta eta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta < 1) (hη : |eta| ≤ 1)
    {q : Ω → ℝ} (hq : Measurable q) (hqb : ∀ᵐ w ∂μ, |q w| ≤ 1)
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hqodd : ∀ᵐ w ∂μ, q (T w) = -q w) (z : ℝ) :
    (∫ w, responseAttenuation theta (z + statisticMessage theta (q w)) ^ 2
      ∂linearSignalTilt μ q (eta * theta)) ≤
        1 - sideSignalLossCoefficient theta * (∫ w, q w ^ 2 ∂μ) := by
  have hθsq : theta ^ 2 < 1 := by nlinarith
  have ha : |eta * theta| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hθ0]
    exact (mul_le_mul_of_nonneg_right hη hθ0).trans (by simpa using hθ1.le)
  let := linearSignalTilt_probability hq hqb ha
    (integral_eq_zero_of_ae_sign_reversal T hT hqodd)
  have hb : ∀ᵐ w ∂linearSignalTilt μ q (eta * theta),
      |statisticMessage theta (q w)| ≤ Real.artanh theta := by
    apply (withDensity_absolutelyContinuous _ _).ae_le
    exact hqb.mono (fun w hw => statisticMessage_abs_le hθ0 hθ1 hw)
  have hloss := integral_shifted_attenuation_loss_explicit
    (μ := linearSignalTilt μ q (eta * theta)) hθsq.le
    ((measurable_statisticMessage theta).comp hq) hb z
  have hvariance := variance_statisticMessage_linearSignalTilt hθ0 hθ1 hη hq hqb T hT hqodd
  have hmul := mul_le_mul_of_nonneg_left hvariance
    (shiftedLossCoefficient_pos (beta := Real.artanh theta) hθsq).le
  simp only [Function.comp_def] at hloss
  unfold sideSignalLossCoefficient
  nlinarith [hloss]

end Probability

end Problem367

end

end OAI
