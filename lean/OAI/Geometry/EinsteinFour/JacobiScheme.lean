import OAI.Geometry.EinsteinFour.JacobiApproximation
import Mathlib.Analysis.Normed.Operator.Mul

namespace OAI

/-! The concrete noncommuting kick-drift scheme and its Jacobi recurrence. -/

namespace PositiveEinsteinFour.Jacobi

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R]

def jacobiScheme (A : ℕ → R) (h : ℝ) : ℕ → R × R
  | 0 => (0, 1)
  | n + 1 =>
      let z := jacobiScheme A h n
      let w := z.2 - h • (A n * z.1)
      (z.1 + h • w, w)

def discretePosition (A : ℕ → R) (h : ℝ) (n : ℕ) : R := (jacobiScheme A h n).1

def discreteVelocity (A : ℕ → R) (h : ℝ) (n : ℕ) : R := (jacobiScheme A h n).2

@[simp] theorem discretePosition_zero (A : ℕ → R) (h : ℝ) :
    discretePosition A h 0 = 0 := rfl

@[simp] theorem discreteVelocity_zero (A : ℕ → R) (h : ℝ) :
    discreteVelocity A h 0 = 1 := rfl

theorem discreteVelocity_succ (A : ℕ → R) (h : ℝ) (n : ℕ) :
    discreteVelocity A h (n + 1) = discreteVelocity A h n -
      h • (A n * discretePosition A h n) := rfl

theorem discretePosition_succ (A : ℕ → R) (h : ℝ) (n : ℕ) :
    discretePosition A h (n + 1) = discretePosition A h n +
      h • discreteVelocity A h (n + 1) := rfl

@[simp] theorem discretePosition_one (A : ℕ → R) (h : ℝ) :
    discretePosition A h 1 = h • (1 : R) := by
  simp [discretePosition, jacobiScheme]

/-- Matrix multiplication stays in its original order in the second-order
recurrence. The curvature is sampled at the interior node. -/
theorem discretePosition_recurrence (A : ℕ → R) (h : ℝ) (n : ℕ) :
    discretePosition A h (n + 2) =
      ((2 : ℝ) • (1 : R) - h ^ 2 • A (n + 1)) * discretePosition A h (n + 1) -
        discretePosition A h n := by
  rw [discretePosition_succ A h (n + 1), discreteVelocity_succ A h (n + 1)]
  have hp := discretePosition_succ A h n
  simp only [sub_mul, smul_mul_assoc, one_mul, smul_sub, smul_smul, pow_two]
  rw [show (2 : ℝ) • discretePosition A h (n + 1) =
    discretePosition A h (n + 1) + discretePosition A h (n + 1) by module]
  rw [hp]
  abel

def normalizedDiscrete (A : ℕ → R) (h : ℝ) (n : ℕ) : R :=
  h⁻¹ • discretePosition A h n

@[simp] theorem normalizedDiscrete_zero (A : ℕ → R) (h : ℝ) :
    normalizedDiscrete A h 0 = 0 := by simp [normalizedDiscrete]

@[simp] theorem normalizedDiscrete_one (A : ℕ → R) {h : ℝ} (hh : h ≠ 0) :
    normalizedDiscrete A h 1 = 1 := by
  simp [normalizedDiscrete, smul_smul, hh]

theorem normalizedDiscrete_recurrence (A : ℕ → R) (h : ℝ) (n : ℕ) :
    normalizedDiscrete A h (n + 2) =
      ((2 : ℝ) • (1 : R) - h ^ 2 • A (n + 1)) * normalizedDiscrete A h (n + 1) -
        normalizedDiscrete A h n := by
  simp only [normalizedDiscrete, discretePosition_recurrence, smul_sub, mul_smul_comm]

end

end PositiveEinsteinFour.Jacobi

end OAI
