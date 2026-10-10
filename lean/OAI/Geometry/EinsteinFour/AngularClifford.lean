import OAI.Geometry.EinsteinFour.AngularRotation

namespace OAI

/-! Quaternion matrix identities for the sixth-moment mixed contraction. -/

namespace PositiveEinsteinFour.Angular

open Matrix TraceHessian

noncomputable section

theorem quaternionMatrix_transpose (i : Fin 3) :
    (quaternionMatrix i)ᵀ = -quaternionMatrix i := by
  ext a b
  simp only [Matrix.transpose_apply, Matrix.neg_apply]
  fin_cases i <;> fin_cases a <;> fin_cases b <;> norm_num [quaternionMatrix]

theorem quaternionMatrix_anticommutator (i j : Fin 3) :
    quaternionMatrix i * quaternionMatrix j + quaternionMatrix j * quaternionMatrix i =
      (if i = j then (-2 : ℝ) else 0) • (1 : Mat4) := by
  ext a b
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [quaternionMatrix, Fin.sum_univ_succ]

private theorem oppositeMatrix_anticommutator_zero (j : Fin 3) :
    oppositeMatrix 0 * oppositeMatrix j + oppositeMatrix j * oppositeMatrix 0 =
      (if (0 : Fin 3) = j then (-2 : ℝ) else 0) • (1 : Mat4) := by
  ext a b
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply]
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [oppositeMatrix, Geometry.oppositeQuaternion, quaternionMatrix,
      Fin.sum_univ_succ]

private theorem oppositeMatrix_anticommutator_one (j : Fin 3) :
    oppositeMatrix 1 * oppositeMatrix j + oppositeMatrix j * oppositeMatrix 1 =
      (if (1 : Fin 3) = j then (-2 : ℝ) else 0) • (1 : Mat4) := by
  ext a b
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply]
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [oppositeMatrix, Geometry.oppositeQuaternion, quaternionMatrix,
      Fin.sum_univ_succ]

private theorem oppositeMatrix_anticommutator_two (j : Fin 3) :
    oppositeMatrix 2 * oppositeMatrix j + oppositeMatrix j * oppositeMatrix 2 =
      (if (2 : Fin 3) = j then (-2 : ℝ) else 0) • (1 : Mat4) := by
  ext a b
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply]
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [oppositeMatrix, Geometry.oppositeQuaternion, quaternionMatrix,
      Fin.sum_univ_succ]

theorem oppositeMatrix_anticommutator (i j : Fin 3) :
    oppositeMatrix i * oppositeMatrix j + oppositeMatrix j * oppositeMatrix i =
      (if i = j then (-2 : ℝ) else 0) • (1 : Mat4) := by
  fin_cases i
  · exact oppositeMatrix_anticommutator_zero j
  · exact oppositeMatrix_anticommutator_one j
  · exact oppositeMatrix_anticommutator_two j

theorem oppositeMatrix_commute (i j : Fin 3) :
    oppositeMatrix i * quaternionMatrix j = quaternionMatrix j * oppositeMatrix i := by
  ext a b
  simp only [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [oppositeMatrix, Geometry.oppositeQuaternion, quaternionMatrix,
      Fin.sum_univ_succ]

theorem mixingCoefficient_product (i j k l : Fin 3) :
    mixingCoefficient i k * mixingCoefficient j l =
      quaternionMatrix i * quaternionMatrix j * oppositeMatrix k * oppositeMatrix l := by
  unfold mixingCoefficient
  rw [quaternionMatrix_transpose, quaternionMatrix_transpose]
  calc
    (-quaternionMatrix i * oppositeMatrix k) * (-quaternionMatrix j * oppositeMatrix l) =
        quaternionMatrix i * (oppositeMatrix k * quaternionMatrix j) * oppositeMatrix l := by
      noncomm_ring
    _ = _ := by rw [oppositeMatrix_commute]; noncomm_ring

/-- The symmetrized product collapses to the scalar Clifford relation. -/
theorem mixingCoefficient_product_symm (i j k l : Fin 3) :
    mixingCoefficient i k * mixingCoefficient j l +
      mixingCoefficient j l * mixingCoefficient i k +
      mixingCoefficient j k * mixingCoefficient i l +
      mixingCoefficient i l * mixingCoefficient j k =
        (if i = j then (if k = l then (4 : ℝ) else 0) else 0) • (1 : Mat4) := by
  simp only [mixingCoefficient_product]
  calc
    _ = (quaternionMatrix i * quaternionMatrix j + quaternionMatrix j * quaternionMatrix i) *
        (oppositeMatrix k * oppositeMatrix l + oppositeMatrix l * oppositeMatrix k) := by
      noncomm_ring
    _ = _ := by
      rw [quaternionMatrix_anticommutator, oppositeMatrix_anticommutator]
      by_cases hij : i = j <;> by_cases hkl : k = l <;>
        norm_num [hij, hkl, smul_smul]

end

end PositiveEinsteinFour.Angular

end OAI
