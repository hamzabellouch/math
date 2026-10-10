import OAI.Geometry.EinsteinFour.JacobiKernelTrace
import Mathlib.LinearAlgebra.Matrix.SchurComplement

namespace OAI

/-! Moving the square-root factors in the finite Jacobi perturbation.
Only cyclicity of trace is used; curvature matrices are never commuted. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem product_power_succ (A B : Matrix ι ι ℝ) (k : ℕ) :
    (A * B) ^ (k + 1) = A * (B * A) ^ k * B := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ (A * B), ih, pow_succ (B * A)]
      simp only [Matrix.mul_assoc]

theorem trace_product_powers (A B : Matrix ι ι ℝ) (k : ℕ) :
    ((A * B) ^ k).trace = ((B * A) ^ k).trace := by
  cases k with
  | zero => simp
  | succ k =>
      rw [product_power_succ, Matrix.trace_mul_cycle, ← pow_succ']

theorem trace_sandwich_powers (S D : Matrix ι ι ℝ) (k : ℕ) :
    ((S * D * S) ^ k).trace = ((S * S * D) ^ k).trace := by
  rw [trace_product_powers (S * D) S, ← Matrix.mul_assoc]

theorem det_one_sub_sandwich (S D : Matrix ι ι ℝ) :
    (1 - S * D * S).det = (1 - S * S * D).det := by
  rw [Matrix.det_one_sub_mul_comm (S * D) S, ← Matrix.mul_assoc]

end
end PositiveEinsteinFour.Jacobi

end OAI
