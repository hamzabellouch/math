import OAI.NumberTheory.TwoPoint.Halasz.HalaszTriangleWeight

namespace OAI

/-! Identification of the compact triangular Fourier transform with the
oscillatory integrals estimated above. -/
namespace TwoPointCorrelations

open MeasureTheory
open scoped FourierTransform

lemma halasz_triangle_integral_function (N u v : ℝ) (hN : 0 < N) :
    (∫ x, halaszTriangleFunction N u v x) = halaszTriangleIntegral N u v := by
  have hz (x : ℝ) (hx : x ∉ Set.Ioc (N/2) (5*N/2)) :
      halaszTriangleFunction N u v x = 0 := by
    rw [Set.mem_Ioc, not_and_or] at hx
    rcases hx with hx | hx
    · simp only [not_lt] at hx
      simp only [halaszTriangleFunction, halasz_triangle_weight_left_zero N x hN hx,
        Complex.ofReal_zero, zero_mul]
    · apply halasz_triangle_function_zero N u v x hN
      intro hx'
      exact hx hx'.2
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    ← intervalIntegral.integral_of_le (by linarith : N/2 ≤ 5*N/2)]
  have hc := halasz_triangle_function_continuous N u v hN
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (N/2) (3*N/2)) (hc.intervalIntegrable (3*N/2) (5*N/2))]
  unfold halaszTriangleIntegral
  congr 1
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith : N/2 ≤ 3*N/2)] at hx
    unfold halaszTriangleFunction
    rw [halasz_triangle_weight_left N x hN hx]
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith : 3*N/2 ≤ 5*N/2)] at hx
    unfold halaszTriangleFunction
    rw [halasz_triangle_weight_right N x hN hx]

lemma halasz_log_phase_fourier (u ξ x : ℝ) :
    Complex.exp (((-2*Real.pi*x*ξ:ℝ):ℂ)*Complex.I)*halaszLogPhase u 0 x =
      halaszLogPhase u (2*Real.pi*ξ) x := by
  unfold halaszLogPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem halasz_triangle_fourier (N u ξ : ℝ) (hN : 0 < N) :
    𝓕 (halaszTriangleFunction N u 0) ξ =
      halaszTriangleIntegral N u (2*Real.pi*ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he (x : ℝ) :
      Complex.exp (((-2*Real.pi*x*ξ:ℝ):ℂ)*Complex.I) • halaszTriangleFunction N u 0 x =
        halaszTriangleFunction N u (2*Real.pi*ξ) x := by
    rw [smul_eq_mul]
    unfold halaszTriangleFunction
    rw [← mul_assoc, mul_comm _ (halaszTriangleWeight N x:ℂ), mul_assoc,
      halasz_log_phase_fourier]
  simp_rw [he]
  exact halasz_triangle_integral_function N u (2*Real.pi*ξ) hN

end TwoPointCorrelations

end OAI
