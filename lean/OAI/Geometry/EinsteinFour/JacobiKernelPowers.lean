import OAI.Geometry.EinsteinFour.JacobiTraceProducts
import OAI.Geometry.EinsteinFour.JacobiCompression

namespace OAI

/-! Positive scalar path weights bound the noncommuting curvature kernel. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
open scoped Matrix.Norms.Frobenius
noncomputable section

def curvatureKernel {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (R : Fin N → NormalMatrix) : Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ :=
  scalarLift G * Matrix.blockDiagonal R

theorem blockAt_curvatureKernel {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (R : Fin N → NormalMatrix) (i j : Fin N) :
    blockAt (curvatureKernel G R) i j = G i j • R j := by
  rw [curvatureKernel, blockAt_mul_diagonal, blockAt_scalarLift,
    smul_mul_assoc, Matrix.one_mul]

theorem blockAt_one {N : ℕ} (i j : Fin N) :
    blockAt (1 : Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ) i j =
      if i = j then 1 else 0 := by
  rw [← scalarLift_one N, blockAt_scalarLift]
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

theorem scalar_pow_entry_nonneg {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (hG : ∀ i j, 0 ≤ G i j) (k : ℕ) (i j : Fin N) : 0 ≤ (G ^ k) i j := by
  induction k generalizing i j with
  | zero => simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
      rw [pow_succ', Matrix.mul_apply]
      exact Finset.sum_nonneg (fun l _ => mul_nonneg (hG i l) (ih l j))

/-- The initial matrix is kept outside the scalar path bound. In particular,
the zero-step bound does not lose the norm of the identity matrix. -/
theorem curvatureKernel_power_bound {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (hG : ∀ i j, 0 ≤ G i j) (R : Fin N → NormalMatrix)
    (hR : ∀ i, ‖R i‖ ≤ 3) (k : ℕ) (A : NormalMatrix) (i j : Fin N) :
    ‖A * blockAt (curvatureKernel G R ^ k) i j‖ ≤
      (3 ^ k * (G ^ k) i j) * ‖A‖ := by
  induction k generalizing A i j with
  | zero =>
      rw [pow_zero, blockAt_one, pow_zero]
      by_cases hij : i = j <;> simp [hij]
  | succ k ih =>
      rw [pow_succ', blockAt_mul, Matrix.mul_sum]
      calc
        _ ≤ ∑ l, ‖A * (blockAt (curvatureKernel G R) i l *
              blockAt (curvatureKernel G R ^ k) l j)‖ := norm_sum_le _ _
        _ = ∑ l, G i l * ‖(A * R l) *
              blockAt (curvatureKernel G R ^ k) l j‖ := by
          apply Finset.sum_congr rfl
          intro l _
          rw [blockAt_curvatureKernel, smul_mul_assoc, mul_smul_comm,
            ← Matrix.mul_assoc, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hG i l)]
        _ ≤ ∑ l, G i l * ((3 ^ k * (G ^ k) l j) * (‖A‖ * 3)) := by
          apply Finset.sum_le_sum
          intro l _
          apply mul_le_mul_of_nonneg_left _ (hG i l)
          exact (ih (A * R l) l j).trans (mul_le_mul_of_nonneg_left
            ((Matrix.frobenius_norm_mul A (R l)).trans
              (mul_le_mul_of_nonneg_left (hR l) (norm_nonneg A)))
            (mul_nonneg (by positivity) (scalar_pow_entry_nonneg G hG k l j)))
        _ = (3 ^ (k + 1) * (G ^ (k + 1)) i j) * ‖A‖ := by
          rw [show G ^ (k + 1) = G * G ^ k from pow_succ' G k,
            Matrix.mul_apply, pow_succ]
          simp only [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro l _
          ring

end
end PositiveEinsteinFour.Jacobi

end OAI
