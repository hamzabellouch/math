import OAI.Geometry.RCD.Harmonic.ActualRadialHarmonic
import OAI.Geometry.RCD.Sobolev.PoissonDefectBudget

namespace OAI

/-! # Uniform natural units for the actual radial correction error -/

noncomputable section
namespace RegularPointCoordinates

def radialCorrectionConstant (K : ℝ) (n : ℕ) (epsilon A B J Cχ : ℝ) : ℝ :=
  1 + 2 * (1 + epsilon) ^ 2 * B + annularPoincareConstant K n *
    (((n + 2 : ℕ) : ℝ) * (1 + epsilon + A)) ^ 2 *
      (4096 * Cχ * (J + B / 2) + A ^ 2)

theorem radialCorrectionConstant_pos {K epsilon A B J Cχ : ℝ} {n : ℕ}
    (hB : 0 ≤ B) (hJ : 0 ≤ J) (hCχ : 0 ≤ Cχ) :
    0 < radialCorrectionConstant K n epsilon A B J Cχ := by
  have hp := annularPoincareConstant_pos K n
  dsimp only [radialCorrectionConstant]
  positivity

/-- The scale-dependent span bound and the radius-squared Poincare
constant give one uniform coefficient for the complete Poisson defect. -/
theorem radial_correction_error_units {K epsilon A B J Cχ s κ σ V L : ℝ} {n : ℕ}
    (hs1 : s ≤ 1) (hκ : 0 ≤ κ) (hσ : 0 ≤ σ) (hV : 0 ≤ V)
    (hB : 0 ≤ B) (hJ : 0 ≤ J) (hA : 0 ≤ A) (hε : 0 ≤ epsilon) (hCχ : 0 ≤ Cχ)
    (hL : L = ((n + 2 : ℕ) : ℝ) * max (1 + epsilon) (A * s)) :
    2 * (1 + epsilon) ^ 2 * (σ * (B * s ^ 2)) +
      8 * (annularPoincareConstant K n * (s / 64) ^ 2) * L ^ 2 *
        (4096 * Cχ * (J + B / 2) * σ + κ * A ^ 2 * s ^ 2 * V) ≤
      radialCorrectionConstant K n epsilon A B J Cχ * s ^ 2 * (σ + κ * s ^ 2 * V) := by
  let N := ((n + 2 : ℕ) : ℝ) * (1 + epsilon + A)
  let H := 4096 * Cχ * (J + B / 2) + A ^ 2
  have hc := (annularPoincareConstant_pos K n).le
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hLN : L ≤ N := by
    rw [hL]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply max_le
    · linarith
    · have hh := mul_le_mul_of_nonneg_left hs1 hA
      linarith
  have hLs : L ^ 2 ≤ N ^ 2 := (sq_le_sq₀ hL0 hN).mpr hLN
  have hsize : 0 ≤ σ + κ * s ^ 2 * V := by positivity
  have hmass : 4096 * Cχ * (J + B / 2) * σ + κ * A ^ 2 * s ^ 2 * V ≤
      H * (σ + κ * s ^ 2 * V) := by
    dsimp only [H]
    nlinarith [mul_nonneg (sq_nonneg A) hσ,
      mul_nonneg (by positivity : 0 ≤ 4096 * Cχ * (J + B / 2))
        (by positivity : 0 ≤ κ * s ^ 2 * V)]
  have hscale : 8 * (annularPoincareConstant K n * (s / 64) ^ 2) ≤
      annularPoincareConstant K n * s ^ 2 := by
    nlinarith [mul_nonneg hc (sq_nonneg s)]
  have hsecond : 8 * (annularPoincareConstant K n * (s / 64) ^ 2) * L ^ 2 *
      (4096 * Cχ * (J + B / 2) * σ + κ * A ^ 2 * s ^ 2 * V) ≤
      annularPoincareConstant K n * s ^ 2 * N ^ 2 * (H * (σ + κ * s ^ 2 * V)) := by
    gcongr
  have hfirst : 2 * (1 + epsilon) ^ 2 * (σ * (B * s ^ 2)) ≤
      (2 * (1 + epsilon) ^ 2 * B) * s ^ 2 * (σ + κ * s ^ 2 * V) := by
    have hh := mul_le_mul_of_nonneg_left
      (show σ ≤ σ + κ * s ^ 2 * V from le_add_of_nonneg_right (by positivity))
      (show 0 ≤ (2 * (1 + epsilon) ^ 2 * B) * s ^ 2 by positivity)
    convert hh using 1
    ring
  calc
    _ ≤ (2 * (1 + epsilon) ^ 2 * B) * s ^ 2 * (σ + κ * s ^ 2 * V) +
        annularPoincareConstant K n * s ^ 2 * N ^ 2 * (H * (σ + κ * s ^ 2 * V)) :=
      add_le_add hfirst hsecond
    _ ≤ _ := by
      dsimp only [radialCorrectionConstant, N, H]
      nlinarith [mul_nonneg (sq_nonneg s) hsize]

end RegularPointCoordinates

end

end OAI
