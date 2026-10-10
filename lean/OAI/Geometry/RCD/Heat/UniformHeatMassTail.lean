import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.GlobalGaussianShell

namespace OAI

/-! # Uniform heat mass tails on spaces with Bishop--Gromov comparison -/

open Set Metric MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace RegularPointCoordinates

def gaussianMassEnvelope (m : ℕ) (a : ℝ) (j : ℕ) : ℝ :=
  (((2 : ℝ) ^ (2 * (m + 1))) ^ j * Real.exp ((2 * (m : ℝ) * a) * 2 ^ j)) *
    gaussianShellFactor (4 + (1 / 2 : ℝ))⁻¹ j

theorem gaussianMassEnvelope_nonneg (m : ℕ) (a : ℝ) (j : ℕ) :
    0 ≤ gaussianMassEnvelope m a j := by
  unfold gaussianMassEnvelope
  exact mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
    (gaussianShellFactor_nonneg _ _)

theorem summable_gaussianMassEnvelope (m : ℕ) (a : ℝ) : Summable (gaussianMassEnvelope m a) :=
  summable_shell_with_linear_growth (by positivity) (by norm_num) _

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) [μ.Regular]
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk in
/-- The tail bound is uniform in the pole and in all reference radii at
most one. No global Euclidean volume hypothesis is used. -/
theorem exists_uniform_heat_mass_tail (m : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison μ (comparisonModelVolume m a))
    (hfinite : ∀ x r, μ (ball x r) ≠ ∞)
    (hpos : ∀ x r, 0 < r → 0 < μ.real (ball x r))
    (hg : HasCoordinateHeatBounds μ ker) :
    ∃ C : ℝ, 0 < C ∧ ∀ p r, 0 < r → r ≤ 1 → ∀ N : ℕ,
      (∫ y in (ball p (2 ^ N * r))ᶜ, ker (r ^ 2) p y ∂μ) ≤
        C * ∑' j, gaussianMassEnvelope m a (j + (N + 1)) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hgauss⟩ := hg (1 / 2) (by norm_num) (by norm_num)
  let C := C₁ * Real.exp (C₂ + (m : ℝ) * a) * (2 : ℝ) ^ (m + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hs := summable_gaussianMassEnvelope m a
  refine ⟨C, hC, fun p r hr hr1 N => ?_⟩
  let W := globalGaussianShellBound μ m a C₁ C₂ (4 + 1 / 2) r p
  have hW (j : ℕ) : 0 ≤ W j := by
    dsimp [W, globalGaussianShellBound]
    exact mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg hC₁.le (hpos p r hr).le)
      (Real.exp_pos _).le) (mul_nonneg (Real.exp_pos _).le (by positivity)))
      (gaussianShellFactor_nonneg _ _)
  have hupper (y : X) : ker (r ^ 2) p y ≤ (C₁ / μ.real (ball y r)) *
      Real.exp (-(dist p y) ^ 2 / ((4 + 1 / 2) * r ^ 2) + C₂ * r ^ 2) := by
    simpa only [Real.sqrt_sq hr.le] using (hgauss (r ^ 2) (sq_pos_of_pos hr) p y).2
  have hbound (j : ℕ) : ∀ᵐ y ∂μ.restrict (dyadicShell p r j), ker (r ^ 2) p y ≤ W j := by
    filter_upwards [ae_restrict_mem (measurableSet_dyadicShell p r j)] with y hy
    exact global_gaussian_shell_bound μ ker m ha hC₁.le (by norm_num) hr hBG hfinite p
      (hpos p r hr) hupper j hy
  have hmajor (j : ℕ) : W j * μ.real (ball p (2 ^ j * r)) ≤ C * gaussianMassEnvelope m a j :=
    global_gaussian_shell_volume_bound μ m ha hC₁.le hC₂ hr hr1 hBG p (hpos p r hr) j
  have hsum : Summable (fun j => W j * μ.real (ball p (2 ^ j * r))) :=
    (hs.mul_left C).of_nonneg_of_le
      (fun j => mul_nonneg (hW j) measureReal_nonneg) hmajor
  have ht := integral_outside_dyadic_ball_le_tail μ p hr
    (hk.integrable _ (sq_pos_of_pos hr) p) (hfinite p) hW hbound hsum N
  have hm := ((summable_nat_add_iff (N + 1)).mpr hsum).tsum_le_tsum
    (fun j => hmajor (j + (N + 1)))
    (((summable_nat_add_iff (N + 1)).mpr hs).mul_left C)
  rw [tsum_mul_left] at hm
  exact ht.trans hm

end RegularPointCoordinates

end

end OAI
