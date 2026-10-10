import OAI.Geometry.EinsteinFour.JacobiCyclicPowers
import OAI.Geometry.EinsteinFour.JacobiKernelAverage

namespace OAI

/-! Symmetric realization of the positive Green-kernel perturbation. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

def symmetricCurvatureKernel {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ)
    (R : Fin N → NormalMatrix) : Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ :=
  scalarLift S * Matrix.blockDiagonal R * scalarLift S

theorem symmetricCurvatureKernel_trace_pow {N : ℕ}
    (S G : Matrix (Fin N) (Fin N) ℝ) (hS : S * S = G)
    (R : Fin N → NormalMatrix) (k : ℕ) :
    (symmetricCurvatureKernel S R ^ k).trace = (curvatureKernel G R ^ k).trace := by
  rw [symmetricCurvatureKernel, trace_sandwich_powers, ← scalarLift_mul, hS]
  rfl

theorem symmetricCurvatureKernel_trace {N : ℕ}
    (S G : Matrix (Fin N) (Fin N) ℝ) (hS : S * S = G)
    (R : Fin N → NormalMatrix) (hR : ∀ i, (R i).trace = 3) :
    (symmetricCurvatureKernel S R).trace = 3 * G.trace := by
  have h := symmetricCurvatureKernel_trace_pow S G hS R 1
  simp only [pow_one] at h
  rw [h]
  change (scalarLift G * Matrix.blockDiagonal R).trace = _
  rw [trace_scalarLift_mul_diagonal]
  simp_rw [hR]
  simp only [Matrix.trace, Matrix.diag_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem symmetricCurvatureKernel_det {N : ℕ}
    (S G : Matrix (Fin N) (Fin N) ℝ) (hS : S * S = G)
    (R : Fin N → NormalMatrix) :
    (1 - symmetricCurvatureKernel S R).det = (1 - curvatureKernel G R).det := by
  rw [symmetricCurvatureKernel, det_one_sub_sandwich, ← scalarLift_mul, hS]
  rfl

theorem blockDiagonal_posSemidef {N : ℕ} (R : Fin N → NormalMatrix)
    (hR : ∀ i, (R i).PosSemidef) : (Matrix.blockDiagonal R).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change (Matrix.blockDiagonal R).conjTranspose = Matrix.blockDiagonal R
    rw [Matrix.blockDiagonal_conjTranspose]
    congr 1
    funext i
    exact (hR i).isHermitian.eq
  · intro x
    rw [blockDiagonal_quadratic]
    exact Finset.sum_nonneg (fun i _ => (hR i).dotProduct_mulVec_nonneg _)

theorem scalarLift_conjTranspose {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ)
    (hS : Sᵀ = S) : (scalarLift S)ᴴ = scalarLift S := by
  ext ⟨a,i⟩ ⟨b,j⟩
  change (1 : NormalMatrix) b a * S j i = (1 : NormalMatrix) a b * S i j
  have hs : S j i = S i j := congrFun (congrFun hS i) j
  rw [hs]
  simp only [Matrix.one_apply, eq_comm]

theorem symmetricCurvatureKernel_posSemidef {N : ℕ}
    (S : Matrix (Fin N) (Fin N) ℝ) (hS : Sᵀ = S)
    (R : Fin N → NormalMatrix) (hR : ∀ i, (R i).PosSemidef) :
    (symmetricCurvatureKernel S R).PosSemidef := by
  have h := (blockDiagonal_posSemidef R hR).conjTranspose_mul_mul_same (scalarLift S)
  simpa only [scalarLift_conjTranspose S hS, symmetricCurvatureKernel] using h

end
end PositiveEinsteinFour.Jacobi

end OAI
