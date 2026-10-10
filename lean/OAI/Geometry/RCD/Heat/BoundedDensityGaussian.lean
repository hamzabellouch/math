import OAI.Geometry.RCD.Heat.SupportedGaussianVolume

namespace OAI

/-! # Gaussian source bounds for the bounded curvature density -/

open Set Metric MeasureTheory Filter

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsLocallyFiniteMeasure μ]

/-- Bounded densities supported on the working ball consume only its
Gaussian volume moment. This will be applied to the curvature density. -/
theorem integral_bounded_density_gaussian_le (n : ℕ) (x : X)
    {s R α D V B : ℝ} (hs : 0 < s) (hα : 0 ≤ α) (hD : 0 < D)
    (hV : 0 ≤ V) (hB : 0 ≤ B) (N : ℕ) (hroot : (2 : ℝ) ^ N * s = R)
    {k g : X → ℝ} (hg : ∀ᵐ z ∂μ, |g z| ≤ B)
    (hzero : ∀ᵐ z ∂μ, z ∉ ball x R → g z = 0)
    (hkernel : ∀ z ∈ ball x R, |k z| ≤ α / s ^ n * Real.exp (-(dist x z) ^ 2 / (D * s ^ 2)))
    (hvolume : ∀ j ≤ N, μ.real (ball x (2 ^ j * s)) ≤ V * (2 ^ j * s) ^ n) :
    |∫ z, k z * g z ∂μ| ≤ α * B * V * gaussianVolumeMomentConstant n D⁻¹ := by
  let F := (ball x R).indicator (fun z => (α * B) / s ^ n *
    Real.exp (-(dist x z) ^ 2 / (D * s ^ 2)))
  have hcoef : 0 ≤ (α * B) / s ^ n := div_nonneg (mul_nonneg hα hB) (pow_pos hs n).le
  have hexp (z : X) : Real.exp (-(dist x z) ^ 2 / (D * s ^ 2)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  have hbase : IntegrableOn (fun z => (α * B) / s ^ n *
      Real.exp (-(dist x z) ^ 2 / (D * s ^ 2))) (ball x R) μ := by
    apply IntegrableOn.of_bound isBounded_ball.measure_lt_top
      (by fun_prop) ((α * B) / s ^ n)
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hcoef (Real.exp_pos _).le)]
      exact mul_le_of_le_one_right hcoef (hexp z)
  have hF : Integrable F μ := (integrable_indicator_iff measurableSet_ball).mpr hbase
  have hdom : ∀ᵐ z ∂μ, ‖k z * g z‖ ≤ F z := by
    filter_upwards [hg, hzero] with z hz hz0
    by_cases hin : z ∈ ball x R
    · rw [show F z = (α * B) / s ^ n * Real.exp (-(dist x z) ^ 2 / (D * s ^ 2)) from
        indicator_of_mem hin _, Real.norm_eq_abs, abs_mul]
      have h := mul_le_mul (hkernel z hin) hz (abs_nonneg _) (by positivity :
        0 ≤ α / s ^ n * Real.exp (-(dist x z) ^ 2 / (D * s ^ 2)))
      convert h using 1
      ring
    · simp only [F, indicator_of_notMem hin, hz0 hin, mul_zero, norm_zero, le_refl]
  have hpoint (z : X) : F z ≤ (α * B) / s ^ n * Real.exp (-(dist x z) ^ 2 / (D * s ^ 2)) := by
    by_cases hz : z ∈ ball x R
    · rw [show F z = _ from indicator_of_mem hz _]
    · simp only [F, indicator_of_notMem hz]
      positivity
  have hbound := supported_gaussian_integral_le μ n x hs (mul_nonneg hα hB) hD hV N hroot hF
    hpoint (fun z hz => indicator_of_notMem hz _) hvolume
  have hi : |∫ z, k z * g z ∂μ| ≤ ∫ z, F z ∂μ := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le hF hdom
  exact hi.trans hbound

end RegularPointCoordinates

end

end OAI
