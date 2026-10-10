import OAI.Geometry.RCD.Metric.GlobalVolumeGrowth
import OAI.Geometry.RCD.Heat.HeatMassTail

namespace OAI

/-! # Global Gaussian shell bounds from Bishop--Gromov -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section

namespace RegularPointCoordinates

/-- The polynomial cost of moving the volume center and then integrating
one shell has a fixed geometric rate. -/
theorem dyadic_volume_polynomial_bound (n j : ℕ) {r : ℝ} (hr : 0 < r) :
    ((r + 2 ^ j * r) / r) ^ n * ((2 ^ j * r) / r) ^ n ≤
      (2 : ℝ) ^ n * ((2 : ℝ) ^ (2 * n)) ^ j := by
  have hrne := ne_of_gt hr
  have he : (r + (2 : ℝ) ^ j * r) / r = 1 + 2 ^ j := by field_simp
  rw [he, mul_div_cancel_right₀ _ hrne]
  have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  calc
    _ ≤ ((2 : ℝ) * 2 ^ j) ^ n * (2 ^ j) ^ n := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by positivity) _)
      exact pow_le_pow_left₀ (by positivity) (by linarith) n
    _ = (2 : ℝ) ^ n * ((2 ^ j) ^ n * (2 ^ j) ^ n) := by rw [mul_pow]; ring
    _ = (2 : ℝ) ^ n * ((2 : ℝ) ^ (2 * n)) ^ j := by
      rw [← pow_add, ← pow_mul, ← pow_mul]
      congr 2
      ring

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (ker : ℝ → X → X → ℝ)

/-- The pole volume normalizes a kernel bound on any dyadic shell, even
outside an almost Euclidean region. -/
def globalGaussianShellBound (m : ℕ) (a C B D r : ℝ) (p : X) (j : ℕ) : ℝ :=
  (C / μ.real (ball p r)) * Real.exp (B * r ^ 2) *
    (Real.exp ((m : ℝ) * a * (r + 2 ^ j * r)) *
      ((r + 2 ^ j * r) / r) ^ (m + 1)) * gaussianShellFactor D⁻¹ j

omit [BorelSpace X] in
theorem global_gaussian_shell_bound (m : ℕ) {a C B D r : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hD : 0 < D) (hr : 0 < r)
    (hBG : BallVolumeComparison μ (comparisonModelVolume m a))
    (hfinite : ∀ x s, μ (ball x s) ≠ ∞) (p : X) (hp : 0 < μ.real (ball p r))
    (hupper : ∀ y, ker (r ^ 2) p y ≤ (C / μ.real (ball y r)) *
      Real.exp (-(dist p y) ^ 2 / (D * r ^ 2) + B * r ^ 2))
    (j : ℕ) {y : X} (hy : y ∈ dyadicShell p r j) :
    ker (r ^ 2) p y ≤ globalGaussianShellBound μ m a C B D r p j := by
  have hyball := dyadicShell_subset_ball p r j hy
  have hinv := inverse_volume_at_distant_center_le μ m ha hBG hfinite p y hr
    (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) j) hr).le
    (by simpa only [dist_comm] using (mem_ball.mp hyball).le) hp
  have hk := gaussian_shell_upper μ ker 0 hr hC hinv.1 hD p j hy (hupper y)
    (by simp only [pow_zero, mul_one, le_refl])
  simp only [pow_zero, mul_one] at hk
  have hratio := mul_le_mul_of_nonneg_left hinv.2 hC
  have hh := mul_le_mul_of_nonneg_right hratio
    (mul_nonneg (Real.exp_pos (B * r ^ 2)).le (gaussianShellFactor_nonneg D⁻¹ j))
  apply hk.trans
  simpa only [globalGaussianShellBound, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh

omit [BorelSpace X] in
/-- Integrating the shell bound cancels the pole volume. The remaining
majorant is uniform for all reference radii at most one. -/
theorem global_gaussian_shell_volume_bound (m : ℕ) {a C B D r : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hB : 0 ≤ B) (hr : 0 < r) (hr1 : r ≤ 1)
    (hBG : BallVolumeComparison μ (comparisonModelVolume m a))
    (p : X) (hp : 0 < μ.real (ball p r)) (j : ℕ) :
    globalGaussianShellBound μ m a C B D r p j * μ.real (ball p (2 ^ j * r)) ≤
      (C * Real.exp (B + (m : ℝ) * a) * (2 : ℝ) ^ (m + 1)) *
        (((2 : ℝ) ^ (2 * (m + 1))) ^ j *
          Real.exp ((2 * (m : ℝ) * a) * 2 ^ j) * gaussianShellFactor D⁻¹ j) := by
  have hpj : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hrad : r ≤ 2 ^ j * r := by nlinarith
  have hv := volume_ratio_le_exp μ m ha hBG p hr hrad
  have hn : 0 ≤ globalGaussianShellBound μ m a C B D r p j := by
    unfold globalGaussianShellBound
    exact mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg hC hp.le) (Real.exp_pos _).le)
      (mul_nonneg (Real.exp_pos _).le (pow_nonneg (by positivity) _)))
      (gaussianShellFactor_nonneg _ _)
  have hmul := mul_le_mul_of_nonneg_left hv hn
  have hcancel : globalGaussianShellBound μ m a C B D r p j *
      (Real.exp ((m : ℝ) * a * (2 ^ j * r)) * ((2 ^ j * r) / r) ^ (m + 1) *
        μ.real (ball p r)) =
      C * Real.exp (B * r ^ 2 + (m : ℝ) * a * (r + 2 * (2 ^ j * r))) *
        (((r + 2 ^ j * r) / r) ^ (m + 1) * ((2 ^ j * r) / r) ^ (m + 1)) *
          gaussianShellFactor D⁻¹ j := by
    have he : Real.exp (B * r ^ 2 + (m : ℝ) * a * (r + 2 * (2 ^ j * r))) =
        Real.exp (B * r ^ 2) * Real.exp ((m : ℝ) * a * (r + 2 ^ j * r)) *
          Real.exp ((m : ℝ) * a * (2 ^ j * r)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [he]
    unfold globalGaussianShellBound
    field_simp [ne_of_gt hp, ne_of_gt hr]
  rw [hcancel] at hmul
  have hexponent : B * r ^ 2 + (m : ℝ) * a * (r + 2 * (2 ^ j * r)) ≤
      B + (m : ℝ) * a + (2 * (m : ℝ) * a) * 2 ^ j := by
    have hrsq : r ^ 2 ≤ 1 := by nlinarith
    have hb := mul_le_mul_of_nonneg_left hrsq hB
    have ha' : 0 ≤ (m : ℝ) * a := mul_nonneg (Nat.cast_nonneg m) ha
    have hlin := mul_le_mul_of_nonneg_left
      (show r + 2 * ((2 : ℝ) ^ j * r) ≤ 1 + 2 * 2 ^ j by nlinarith) ha'
    nlinarith
  have hpoly := dyadic_volume_polynomial_bound (m + 1) j hr
  have hmain := mul_le_mul (Real.exp_le_exp.mpr hexponent) hpoly
    (by positivity) (Real.exp_pos _).le
  have hfinal := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmain hC) (gaussianShellFactor_nonneg D⁻¹ j)
  apply hmul.trans
  simpa only [Real.exp_add, mul_assoc, mul_left_comm, mul_comm] using hfinal

end RegularPointCoordinates

end

end OAI
