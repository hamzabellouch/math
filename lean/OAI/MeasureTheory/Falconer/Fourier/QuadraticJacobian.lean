import OAI.MeasureTheory.Falconer.Estimates.QuadraticDifferential
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Function.Jacobian

namespace OAI

/-!
# The Jacobian of the quadratic-to-gnomonic change of variables

The matrix determinant lemma applies to the actual derivative, a scalar
matrix plus one radial term. This gives the measure Jacobian needed to
transfer the published gnomonic density to the quadratic chart.
-/

namespace Falconer
open Matrix

private theorem radial_matrix_det (n : ℕ) (u : Space n) {a b : ℝ} (ha : a ≠ 0) :
    (a • (1 : Matrix (Fin n) (Fin n) ℝ) +
      b • vecMulVec (fun i => u i) (fun i => u i)).det =
        a^n * (1 + b/a * ‖u‖^2) := by
  have he : a • (1 : Matrix (Fin n) (Fin n) ℝ) +
      b • vecMulVec (fun i => u i) (fun i => u i) =
      a • (1 + vecMulVec (fun i => b/a*u i) (fun i => u i)) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply]
    field_simp
  rw [he, Matrix.det_smul, vecMulVec_eq Unit,
    det_one_add_replicateCol_mul_replicateRow]
  simp only [Fintype.card_fin]
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem quadraticCoordinateDifferential_det {n : ℕ} {u : Space n} (hu : ‖u‖ < 1) :
    (quadraticCoordinateDifferential u).det =
      (quadraticRadialFactor (‖u‖^2))^n *
        (1 + (2 * quadraticRadialDerivative (‖u‖^2)) /
          quadraticRadialFactor (‖u‖^2) * ‖u‖^2) := by
  have hu2 : ‖u‖^2 < 1 := by
    simpa using (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu
  have hφ : quadraticRadialFactor (‖u‖^2) ≠ 0 := by
    unfold quadraticRadialFactor
    exact div_ne_zero (Real.sqrt_pos.mpr (by linarith)).ne' (by linarith)
  let B := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  change LinearMap.det (quadraticCoordinateDifferential u).toLinearMap = _
  rw [← LinearMap.det_toMatrix B]
  have hmatrix : LinearMap.toMatrix B B (quadraticCoordinateDifferential u).toLinearMap =
      quadraticRadialFactor (‖u‖^2) • (1 : Matrix (Fin n) (Fin n) ℝ) +
        (2 * quadraticRadialDerivative (‖u‖^2)) •
          vecMulVec (fun i => u i) (fun i => u i) := by
    ext i j
    simp only [LinearMap.toMatrix_apply, B, quadraticCoordinateDifferential,
      ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
      LinearMap.add_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
      OrthonormalBasis.coe_toBasis, map_add, map_smul, smul_eq_mul,
      Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply]
    simp only [EuclideanSpace.basisFun_apply, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul, OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      innerSL_apply_apply, EuclideanSpace.inner_single_right,
      PiLp.single_apply, Matrix.one_apply, starRingEnd_apply, star_trivial]
    split_ifs <;> ring
  rw [hmatrix]
  exact radial_matrix_det n u hφ

private theorem radial_det_factor (m : ℕ) {a : ℝ} (ha : a ≠ 0) (b s : ℝ) :
    a^(m+2) * (1+b/a*s) = a^(m+1) * (a+b*s) := by
  rw [show m+2 = (m+1)+1 by omega, pow_succ]
  field_simp

private theorem radial_quotient_factor (m : ℕ) (q a : ℝ)
    (hq : q ≠ 0) (ha : a ≠ 0) :
    (q/a)^(m+1) * (1/(q*a^2)) = q^m/a^(m+3) := by
  rw [div_pow, pow_succ, show m+3 = (m+1)+2 by omega, pow_add]
  field_simp
  rw [show m+1+2 = m+3 by omega, pow_add]

/-- The dimension range in which the published gnomonic formula is used.
The ambient dimension is `m+3` and the sphere dimension is `m+2`. -/
theorem quadraticCoordinateDifferential_det_explicit (m : ℕ) {u : Space (m+2)}
    (hu : ‖u‖ < 1) :
    (quadraticCoordinateDifferential u).det =
      (Real.sqrt (1-‖u‖^2/4))^m / (1-‖u‖^2/2)^(m+3) := by
  have hu2 : ‖u‖^2 < 1 := by
    simpa using (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu
  have hq : 0 < Real.sqrt (1-‖u‖^2/4) := Real.sqrt_pos.mpr (by linarith)
  have ha : 0 < 1-‖u‖^2/2 := by linarith
  have hφ : quadraticRadialFactor (‖u‖^2) ≠ 0 := div_ne_zero hq.ne' ha.ne'
  rw [quadraticCoordinateDifferential_det hu, radial_det_factor m hφ]
  have he : quadraticRadialFactor (‖u‖^2) +
      2 * quadraticRadialDerivative (‖u‖^2) * ‖u‖^2 =
      1 / (Real.sqrt (1-‖u‖^2/4) * (1-‖u‖^2/2)^2) := by
    convert quadratic_radial_eigenvalue hu2 using 1; ring
  rw [he]
  exact radial_quotient_factor m _ _ hq.ne' ha.ne'

theorem quadraticCoordinateDifferential_det_pos (m : ℕ) {u : Space (m+2)}
    (hu : ‖u‖ < 1) : 0 < (quadraticCoordinateDifferential u).det := by
  rw [quadraticCoordinateDifferential_det_explicit m hu]
  have hu2 : ‖u‖^2 < 1 := by
    simpa using (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu
  exact div_pos (pow_pos (Real.sqrt_pos.mpr (by linarith)) _)
    (pow_pos (by linarith) _)

end Falconer

end OAI
