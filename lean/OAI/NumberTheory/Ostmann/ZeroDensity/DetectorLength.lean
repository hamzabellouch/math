import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Ostmann.ZeroDensity.FiniteDetector

namespace OAI

noncomputable section
namespace Ostmann.ZeroDensity

def detectorLength (Q H X : ℕ) : ℕ := (16 * Q * H * X) ^ 2

theorem detectorLength_ge {Q H X : ℕ} (hQ : 1 ≤ Q) (hH : 1 ≤ H) (hX : 1 ≤ X) :
    X ≤ detectorLength Q H X := by
  have hbase : 1 ≤ 16 * Q * H := by
    have : 0 < 16 * Q * H := by positivity
    omega
  have hXB : X ≤ 16 * Q * H * X := by
    simpa using Nat.mul_le_mul_right X hbase
  unfold detectorLength
  nlinarith

theorem detectorLength_rpow_le {Q H X : ℕ} (hQ : 1 ≤ Q) (hH : 1 ≤ H) (hX : 1 ≤ X)
    {β : ℝ} (hβ : 1 / 2 ≤ β) :
    (detectorLength Q H X : ℝ) ^ (-β) ≤
      (16 * (Q : ℝ) * (H : ℝ) * (X : ℝ))⁻¹ := by
  have hN : (1 : ℝ) ≤ detectorLength Q H X := by
    exact_mod_cast hX.trans (detectorLength_ge hQ hH hX)
  calc
    (detectorLength Q H X : ℝ) ^ (-β) ≤
        (detectorLength Q H X : ℝ) ^ (-((1 : ℝ) / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    _ = (Real.sqrt (detectorLength Q H X : ℝ))⁻¹ := by
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ detectorLength Q H X),
        Real.sqrt_eq_rpow]
    _ = (16 * (Q : ℝ) * (H : ℝ) * (X : ℝ))⁻¹ := by
      simp [detectorLength, Real.sqrt_sq_eq_abs, abs_of_nonneg]

theorem detector_support_length_le {Q H : ℕ} (hQ : 1 ≤ Q) :
    (Q ^ 2 * H) * detectorLength Q H (Q ^ 2 * H) ≤ 256 * (Q ^ 2 * H) ^ 5 := by
  have hp : Q ^ 8 ≤ Q ^ 10 := Nat.pow_le_pow_right (by omega) (by decide)
  calc
    (Q ^ 2 * H) * detectorLength Q H (Q ^ 2 * H) = 256 * Q ^ 8 * H ^ 5 := by
      unfold detectorLength
      ring
    _ ≤ 256 * Q ^ 10 * H ^ 5 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hp)
    _ = 256 * (Q ^ 2 * H) ^ 5 := by ring

end Ostmann.ZeroDensity

end

end OAI
