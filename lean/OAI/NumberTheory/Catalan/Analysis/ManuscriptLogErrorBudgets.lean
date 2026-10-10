import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants

namespace OAI


noncomputable section
namespace InternalCatalan

theorem manuscript_log_error_constants :
    2 * 101 * barrierLogHError + 9 * barrierAtanJ0 <
        (7 / 10000000000000000 : ℝ) ∧
      (569 / 2 : ℝ) * (1 / 1000000000000000) < 285 / 1000000000000000 ∧
      (35 : ℝ) * (1 / 1000000000000000) < 1 / 100000000 ∧
      (14 : ℝ) * (1 / 1000000000000000) < 1 / 100000000 := by
  norm_num [barrierLogHError, barrierAtanJ0]

theorem manuscript_weighted_complex_log_error
    (c z : ℂ) (m k : ℤ) (y r s : ℝ)
    (hm : |(m : ℝ)| ≤ 100)
    (hnorm : z.re ^ 2 + z.im ^ 2 = (2 : ℝ) ^ m * y)
    (hy : y ∈ Set.Icc (1 : ℝ) 2)
    (hrot : barrierOctantRotate k z = ⟨r, s⟩)
    (hr : 0 < r) (hs : |s| ≤ r / 2) (hk : |k| ≤ 4)
    (hpos : k = 4 → s ≤ 0) (hneg : k = -4 → 0 < s) :
    |(c * Complex.log z).re - barrierWeightedComplexLogApprox c m k y (s / r)| ≤
      ‖c‖ * (1 / 1000000000000000 : ℝ) := by
  have hh := barrierComplexLog_weighted_error c z m k y r s hnorm hy hrot hr hs hk hpos hneg
  have he : 0 ≤ barrierLogHError := by unfold barrierLogHError; positivity
  have hj : 0 ≤ barrierAtanJ0 := by unfold barrierAtanJ0; positivity
  have hreal : 0 ≤ (|(m : ℝ)| + 1) * barrierLogHError / 2 := by positivity
  have hang : 0 ≤ 9 * barrierAtanJ0 := by positivity
  have hscale : (|(m : ℝ)| + 1) * barrierLogHError / 2 ≤
      101 * barrierLogHError / 2 := by
    have h := mul_le_mul_of_nonneg_right (show |(m : ℝ)| + 1 ≤ 101 by linarith) he
    linarith
  have hc : 101 * barrierLogHError / 2 + 9 * barrierAtanJ0 ≤
      (1 / 1000000000000000 : ℝ) := by
    have h := manuscript_log_error_constants.1
    linarith
  calc
    _ ≤ |c.re| * ((|(m : ℝ)| + 1) * barrierLogHError / 2) +
        |c.im| * (9 * barrierAtanJ0) := hh
    _ ≤ ‖c‖ * ((|(m : ℝ)| + 1) * barrierLogHError / 2) +
        ‖c‖ * (9 * barrierAtanJ0) :=
      add_le_add (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm c) hreal)
        (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm c) hang)
    _ = ‖c‖ * ((|(m : ℝ)| + 1) * barrierLogHError / 2 + 9 * barrierAtanJ0) := by ring
    _ ≤ ‖c‖ * (101 * barrierLogHError / 2 + 9 * barrierAtanJ0) :=
      mul_le_mul_of_nonneg_left (add_le_add hscale le_rfl) (norm_nonneg c)
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (norm_nonneg c)

end InternalCatalan

end

end OAI
