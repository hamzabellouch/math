import OAI.Geometry.EinsteinFour.FlatCurvatureDirichlet
import OAI.Geometry.EinsteinFour.FlatDirichletDeterminant
import OAI.Geometry.EinsteinFour.DirichletLeadingPositive

namespace OAI

/-! Exact determinant normalization by the flat discrete Green matrix. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem flatGreen_curvature_factorization {N : ℕ} (t : ℝ) (R : Fin N → NormalMatrix) :
    1 - curvatureKernel (scaledFlatGreen t N) R =
      scalarLift (flatGreen N) * curvatureDirichlet t (fun i => R i - 1) := by
  have hflat : flatGreen N * scalarDirichlet N 2 = 1 := by
    rw [flatGreen_eq_inverse]
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (flatDirichlet_posDef N).isUnit)
  rw [flat_curvatureDirichlet_eq, Matrix.mul_sub, ← scalarLift_mul, hflat,
    scalarLift_one, curvatureKernel, scaledFlatGreen, scalarLift_smul,
    Matrix.smul_mul, Matrix.mul_smul]

theorem flatGreen_curvature_det {N : ℕ} (t : ℝ) (R : Fin N → NormalMatrix) :
    ((N : ℝ) + 1) ^ 3 * (1 - curvatureKernel (scaledFlatGreen t N) R).det =
      (curvatureDirichlet t (fun i => R i - 1)).det := by
  rw [flatGreen_curvature_factorization, Matrix.det_mul, det_scalarLift,
    flatGreen_eq_inverse, Matrix.det_nonsing_inv, flatDirichlet_det, Ring.inverse_eq_inv]
  field_simp

theorem flatGreen_endpoint_det {N : ℕ} {t : ℝ} (ht : t ≠ 0)
    (R : ℕ → NormalMatrix) (hsym : ∀ i, (R i)ᵀ = R i)
    (hpos : (curvatureDirichlet t (fun i : Fin N => R (i.val + 1) - 1)).PosDef) :
    t ^ 3 * (1 - curvatureKernel (scaledFlatGreen t N)
      (fun i => R (i.val + 1))).det =
        (discretePosition R (t / (N + 1)) (N + 1)).det := by
  have hd := flatGreen_curvature_det t (fun i : Fin N => R (i.val + 1))
  rw [curvatureDirichlet_determinant_of_posDef ht R hsym hpos] at hd
  have hh : t / ((N : ℝ) + 1) ≠ 0 := div_ne_zero ht (by positivity)
  have he : (t / ((N : ℝ) + 1)) • normalizedDiscrete R (t / (N + 1)) (N + 1) =
      discretePosition R (t / (N + 1)) (N + 1) := by
    simp only [normalizedDiscrete, smul_smul, mul_inv_cancel₀ hh, one_smul]
  rw [← he, Matrix.det_smul, Fintype.card_fin, ← hd]
  field_simp

end
end PositiveEinsteinFour.Jacobi

end OAI
