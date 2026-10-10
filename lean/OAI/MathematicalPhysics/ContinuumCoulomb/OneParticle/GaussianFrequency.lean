import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PiProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalSquareRoot
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ResolventNumericalBounds

namespace OAI

/-! Certified approximation of the manuscript's actual transverse frequency
`sqrt (4*pi*rho)`. The integer density is fixed once for the construction;
it is not assumed that the resulting frequency is rational. -/

noncomputable section
namespace ContinuumCoulomb.GaussianFrequency
open scoped BigOperators

def frequency (rho : ℕ) : ℝ := Real.sqrt (4 * Real.pi * (rho : ℝ))

def count (rho P : ℕ) : ℕ := 512 * (rho + 1) * (P + 1) ^ 2

def precision (P : ℕ) : ℕ := 8 * (P + 1)

def radicand (rho P : ℕ) : ℚ := 4 * (rho : ℚ) * PiProgram.approximate (count rho P)

def approximate (rho P : ℕ) : ℚ := RationalSquareRoot.value (precision P, radicand rho P)

theorem count_positive (rho P : ℕ) : 0 < count rho P := by unfold count; positivity

theorem pi_approximate_nonnegative (N : ℕ) : 0 ≤ PiProgram.approximate N := by
  unfold PiProgram.approximate RationalQuadratureProgram.value
  apply mul_nonneg (by norm_num)
  apply mul_nonneg (by dsimp [PiProgram.input]; positivity)
  apply Finset.sum_nonneg
  intro i _
  dsimp [RationalQuadratureProgram.sample, PiProgram.evaluate]
  positivity

theorem radicand_nonnegative (rho P : ℕ) : 0 ≤ radicand rho P := by
  unfold radicand
  exact mul_nonneg (by positivity) (pi_approximate_nonnegative _)

theorem radicand_error (rho P : ℕ) :
    |(radicand rho P : ℝ) - 4 * Real.pi * (rho : ℝ)| ≤
      ((4 * ((P : ℝ) + 1))⁻¹) ^ 2 := by
  let S := (P : ℝ) + 1
  have hS : 0 < S := by dsimp [S]; positivity
  have hrho : (0 : ℝ) ≤ rho := Nat.cast_nonneg _
  have hp := PiProgram.error (count rho P) (count_positive rho P)
  have he : (radicand rho P : ℝ) - 4 * Real.pi * (rho : ℝ) =
      4 * (rho : ℝ) * ((PiProgram.approximate (count rho P) : ℝ) - Real.pi) := by
    simp only [radicand, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast]
    ring
  rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * (rho : ℝ))]
  apply (mul_le_mul_of_nonneg_left hp (by positivity)).trans
  have hc : (count rho P : ℝ) = 512 * ((rho : ℝ) + 1) * S ^ 2 := by
    dsimp [count, S]
    push_cast
    rfl
  rw [hc]
  calc
    4 * (rho : ℝ) * (8 / (512 * ((rho : ℝ) + 1) * S ^ 2)) ≤
        4 * ((rho : ℝ) + 1) * (8 / (512 * ((rho : ℝ) + 1) * S ^ 2)) := by
      gcongr
      linarith
    _ = ((4 * S)⁻¹) ^ 2 := by
      field_simp [hS.ne', show (rho : ℝ) + 1 ≠ 0 by positivity]
      ring

theorem root_precision_bound (P : ℕ) :
    (2 : ℝ)⁻¹ ^ precision P ≤ (4 * ((P : ℝ) + 1))⁻¹ := by
  have hn : 4 * (P + 1) ≤ 2 ^ precision P := by
    have hh := ResolventSchedule.succ_le_two_pow (precision P)
    unfold precision at *
    omega
  have hr : 4 * ((P : ℝ) + 1) ≤ (2 : ℝ) ^ precision P := by exact_mod_cast hn
  rw [inv_pow]
  exact inv_anti₀ (by positivity) hr

theorem approximation_error (rho P : ℕ) :
    |(approximate rho P : ℝ) - frequency rho| ≤ ((P : ℝ) + 1)⁻¹ := by
  let S := (P : ℝ) + 1
  have hS : 0 < S := by dsimp [S]; positivity
  have hsqrt := RationalSquareRoot.sqrt_perturbation
    (show 0 ≤ (radicand rho P : ℝ) by exact_mod_cast radicand_nonnegative rho P)
    (show 0 ≤ 4 * Real.pi * (rho : ℝ) by positivity)
  have hquad := Real.sqrt_le_sqrt (radicand_error rho P)
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : 0 < (4 * ((P : ℝ) + 1))⁻¹)] at hquad
  have hnum := RationalSquareRoot.value_error (precision P) (radicand_nonnegative rho P)
  have h := (abs_sub_le (approximate rho P : ℝ) (Real.sqrt (radicand rho P : ℝ))
    (frequency rho)).trans (add_le_add (hnum.trans (root_precision_bound P)) (hsqrt.trans hquad))
  apply h.trans
  change (4 * S)⁻¹ + (4 * S)⁻¹ ≤ S⁻¹
  rw [mul_inv]
  norm_num
  nlinarith [inv_pos.mpr hS]

end ContinuumCoulomb.GaussianFrequency

end

end OAI
