import OAI.Geometry.RCD.Heat.ShortAverageGaussian

namespace OAI

/-! # Averaging a Gaussian above the averaging-ball scale -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk in
/-- When the heat length exceeds the averaging radius, a Gaussian at any
averaging point gives a Gaussian at the fixed reference center. -/
theorem kernelAverage_gaussian_above_scale {r t A B D : ℝ}
    (hr : 0 < r) (ht : 0 < t) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 < D)
    (hrtime : r ^ 2 ≤ t) (x q z : X)
    (hfinite : μ (ball q r) ≠ ∞) (hvol : 0 < μ.real (ball q r))
    (hcenter : dist x q ≤ A * r)
    (hbound : ∀ y ∈ ball q r,
      ker t y z ≤ B * Real.exp (-(dist y z) ^ 2 / (D * t))) :
    kernelAverage μ ker t (ball q r) z ≤
      (B * Real.exp ((A + 1) ^ 2 / D)) *
        Real.exp (-(dist x z) ^ 2 / (2 * D * t)) := by
  apply kernelAverage_le_uniform μ hQ hk ht (ball q r) measurableSet_ball hfinite hvol z
  intro y hy
  have hyq : dist q y < r := by simpa only [mem_ball, dist_comm] using hy
  have htri := dist_triangle x q z
  have htri' := dist_triangle q y z
  have hdist : dist x z ≤ (A + 1) * r + dist y z := by linarith
  have hsquare := (sq_le_sq₀ dist_nonneg (by positivity : 0 ≤ (A + 1) * r + dist y z)).mpr hdist
  have hmul := mul_le_mul_of_nonneg_left hrtime (sq_nonneg (A + 1))
  have hs : (dist x z) ^ 2 ≤ 2 * (dist y z) ^ 2 + 2 * (A + 1) ^ 2 * t := by
    nlinarith [sq_nonneg ((A + 1) * r - dist y z)]
  have hf := div_le_div_of_nonneg_right hs (by positivity : 0 ≤ 2 * D * t)
  have he : (2 * (dist y z) ^ 2 + 2 * (A + 1) ^ 2 * t) / (2 * D * t) =
      (dist y z) ^ 2 / (D * t) + (A + 1) ^ 2 / D := by field_simp
  rw [he] at hf
  have hexp : Real.exp (-(dist y z) ^ 2 / (D * t)) ≤
      Real.exp ((A + 1) ^ 2 / D) * Real.exp (-(dist x z) ^ 2 / (2 * D * t)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [neg_div]
    linarith only [hf]
  exact (hbound y hy).trans ((mul_le_mul_of_nonneg_left hexp hB).trans_eq (by ring))

end RegularPointCoordinates

end

end OAI
