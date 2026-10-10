import OAI.Geometry.RCD.Metric.ComparisonModel

namespace OAI

/-! # Global volume ratios for the Gaussian tail estimate -/

open Set Metric MeasureTheory

noncomputable section

namespace RegularPointCoordinates

/-- The hyperbolic comparison factor has at most exponential growth. -/
theorem comparisonModelVolume_le_exp (m : ℕ) {a R : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R) :
    comparisonModelVolume m a R ≤ Real.exp ((m : ℝ) * a * R) * R ^ (m + 1) := by
  have hc : Real.cosh (a * R) ≤ Real.exp (a * R) := by
    rw [Real.cosh_eq]
    have hh := Real.exp_le_exp.mpr (show -(a * R) ≤ a * R by nlinarith)
    linarith
  have hp := pow_le_pow_left₀ (Real.cosh_pos _).le hc m
  have he : Real.exp (a * R) ^ m = Real.exp ((m : ℝ) * a * R) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  exact (comparisonModelVolume_bounds m ha hR).2.trans
    (mul_le_mul_of_nonneg_right (hp.trans_eq he) (pow_nonneg hR _))

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- Bishop--Gromov compares arbitrary radii with a polynomial and the
explicit hyperbolic exponential factor. -/
theorem volume_ratio_le_exp (μ : Measure X) (m : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison μ (comparisonModelVolume m a))
    (p : X) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    μ.real (ball p R) ≤ Real.exp ((m : ℝ) * a * R) * (R / r) ^ (m + 1) *
      μ.real (ball p r) := by
  have hR : 0 ≤ R := hr.le.trans hrR
  have hm := (comparisonModelVolume_bounds m ha hr.le).1
  have hM := comparisonModelVolume_le_exp m ha hR
  have hcross : μ.real (ball p R) * r ^ (m + 1) ≤
      μ.real (ball p r) * (Real.exp ((m : ℝ) * a * R) * R ^ (m + 1)) :=
    (mul_le_mul_of_nonneg_left hm measureReal_nonneg).trans
      ((hBG p r R hr hrR).trans (mul_le_mul_of_nonneg_left hM measureReal_nonneg))
  apply (mul_le_mul_iff_left₀ (pow_pos hr (m + 1))).mp
  calc
    _ ≤ _ := hcross
    _ = _ := by rw [div_pow]; field_simp

/-- A ball about the pole sits in a larger ball about any distant point.
The inverse small-ball volume in the Gaussian upper bound therefore has
an explicit estimate in terms of the pole's ball volume. -/
theorem inverse_volume_at_distant_center_le (μ : Measure X) (m : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison μ (comparisonModelVolume m a))
    (hfinite : ∀ x s, μ (ball x s) ≠ ⊤)
    (p y : X) {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hpy : dist p y ≤ R)
    (hp : 0 < μ.real (ball p r)) :
    0 < μ.real (ball y r) ∧
      (μ.real (ball y r))⁻¹ ≤
        (Real.exp ((m : ℝ) * a * (r + R)) * ((r + R) / r) ^ (m + 1)) /
          μ.real (ball p r) := by
  have hsub : ball p r ⊆ ball y (r + R) := ball_subset_ball' (by linarith)
  have hlarge : μ.real (ball p r) ≤ μ.real (ball y (r + R)) :=
    measureReal_mono hsub (hfinite y _)
  have hv := hlarge.trans (volume_ratio_le_exp μ m ha hBG y hr (by linarith : r ≤ r + R))
  let F := Real.exp ((m : ℝ) * a * (r + R)) * ((r + R) / r) ^ (m + 1)
  have hF : 0 < F := by dsimp [F]; positivity
  have hy : 0 < μ.real (ball y r) := by
    by_contra hn
    have hz : μ.real (ball y r) = 0 := le_antisymm (le_of_not_gt hn) measureReal_nonneg
    rw [hz, mul_zero] at hv
    exact (not_le_of_gt hp) hv
  refine ⟨hy, ?_⟩
  apply (le_div_iff₀ hp).mpr
  have hh := (div_le_iff₀ hy).mpr hv
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh

end RegularPointCoordinates

end

end OAI
