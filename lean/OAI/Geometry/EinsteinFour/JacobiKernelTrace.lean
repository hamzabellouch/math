import OAI.Geometry.EinsteinFour.JacobiKernelPowers

namespace OAI

/-! Exact endpoint expansion of the curvature-kernel trace. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem trace_curvatureKernel_power {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (R : Fin N → NormalMatrix) (k : ℕ) :
    (curvatureKernel G R ^ (k + 2)).trace =
      ∑ i, ∑ j, ∑ l, G i j * G l i *
        (R j * blockAt (curvatureKernel G R ^ k) j l * R i).trace := by
  have hp : curvatureKernel G R ^ (k + 2) =
      (curvatureKernel G R * curvatureKernel G R ^ k) * curvatureKernel G R := by
    rw [show k + 2 = (k + 1) + 1 from rfl, pow_succ, pow_succ']
  rw [hp, trace_eq_sum_block_traces]
  simp only [blockAt_mul, blockAt_curvatureKernel, Matrix.sum_mul, Matrix.trace_sum,
    smul_mul_assoc, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem scalar_power_trace_endpoints {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (k : ℕ) :
    (G ^ (k + 2)).trace = ∑ i, ∑ j, ∑ l, G i j * G l i * (G ^ k) j l := by
  have hp : G ^ (k + 2) = (G * G ^ k) * G := by
    rw [show k + 2 = (k + 1) + 1 from rfl, pow_succ, pow_succ']
  rw [hp]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

end
end PositiveEinsteinFour.Jacobi

end OAI
