import OAI.Geometry.EinsteinFour.PositiveDeterminantOrder
import OAI.Geometry.EinsteinFour.JacobiCurvatureCap

namespace OAI

/-! The pointwise lower comparison with the scalar curvature cap three. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem symmetricCurvatureKernel_cap_posSemidef {N : ℕ}
    (S G : Matrix (Fin N) (Fin N) ℝ) (hS : S * S = G) (hSt : Sᵀ = S)
    (R : Fin N → NormalMatrix) (hR : ∀ i, (R i).PosSemidef ∧ (R i).trace = 3) :
    ((3 : ℝ) • scalarLift G - symmetricCurvatureKernel S R).PosSemidef := by
  have hc := blockDiagonal_posSemidef (fun i => (3 : ℝ) • (1 : NormalMatrix) - R i)
    (fun i => three_sub_posSemidef (hR i).1 (hR i).2)
  have he : Matrix.blockDiagonal (fun i => (3 : ℝ) • (1 : NormalMatrix) - R i) =
      (3 : ℝ) • 1 - Matrix.blockDiagonal R := by
    ext ⟨a,i⟩ ⟨b,j⟩
    by_cases hij : i = j
    · subst j
      simp [Matrix.blockDiagonal_apply, Matrix.one_apply]
    · simp [Matrix.blockDiagonal_apply, hij]
  rw [he] at hc
  have hp := hc.conjTranspose_mul_mul_same (scalarLift S)
  simpa only [scalarLift_conjTranspose S hSt, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← scalarLift_mul, hS,
    symmetricCurvatureKernel] using hp

theorem curvatureKernel_determinant_lower_cap {N : ℕ}
    (S G : Matrix (Fin N) (Fin N) ℝ) (hS : S * S = G) (hSt : Sᵀ = S)
    (R : Fin N → NormalMatrix) (hR : ∀ i, (R i).PosSemidef ∧ (R i).trace = 3)
    (hscalar : (1 - (3 : ℝ) • G).PosDef) :
    (1 - (3 : ℝ) • G).det ^ 3 ≤ (1 - curvatureKernel G R).det := by
  have hp : ((1 - symmetricCurvatureKernel S R) - scalarLift (1 - (3 : ℝ) • G)).PosSemidef := by
    rw [scalarLift_sub_three]
    convert symmetricCurvatureKernel_cap_posSemidef S G hS hSt R hR using 1
    abel
  have h := det_le_det_of_posDef_sub_posSemidef (scalarLift_posDef hscalar) hp
  rwa [det_scalarLift, symmetricCurvatureKernel_det S G hS R] at h

end
end PositiveEinsteinFour.Jacobi

end OAI
