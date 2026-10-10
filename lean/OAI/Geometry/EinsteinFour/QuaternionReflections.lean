import OAI.Geometry.EinsteinFour.AngularClifford
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

namespace OAI

/-! Pure quaternion lifts of the reflections needed to choose a local
spectral frame. Only their concrete action on the two quaternion triples
is used; no global eigenframe or representation theorem is assumed. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

def imaginaryCombination (Q : Fin 3 → Mat4) (u : Fin 3 → ℝ) : Mat4 :=
  ∑ r, u r • Q r

def axisReflection (u : Fin 3 → ℝ) : Mat :=
  fun r s => 2 * u r * u s - if r = s then 1 else 0

private theorem combination_square_expansion (Q : Fin 3 → Mat4) (u : Fin 3 → ℝ) :
    imaginaryCombination Q u * imaginaryCombination Q u =
      ∑ r, ∑ s, (u r * u s) • (Q r * Q s) := by
  simp only [imaginaryCombination, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [mul_comm]

private theorem combination_square_symmetrized (Q : Fin 3 → Mat4) (u : Fin 3 → ℝ) :
    (2 : ℝ) • (imaginaryCombination Q u * imaginaryCombination Q u) =
      ∑ r, ∑ s, (u r * u s) • (Q r * Q s + Q s * Q r) := by
  have hs : (∑ r, ∑ s, (u r * u s) • (Q s * Q r)) =
      ∑ r, ∑ s, (u r * u s) • (Q r * Q s) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [mul_comm (u s) (u r)]
  rw [combination_square_expansion]
  simp only [smul_add, Finset.sum_add_distrib, hs]
  module

/-- The square of a pure quaternion is minus its real squared norm. -/
theorem imaginaryCombination_square
    (Q : Fin 3 → Mat4)
    (hQ : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Mat4)) (u : Fin 3 → ℝ) :
    imaginaryCombination Q u * imaginaryCombination Q u =
      (-(∑ r, u r ^ 2)) • (1 : Mat4) := by
  have h := combination_square_symmetrized Q u
  simp_rw [hQ] at h
  simp only [smul_smul] at h
  simp only [mul_ite, mul_zero, ite_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
  have hs : (∑ r, (u r * u r * (-2)) • (1 : Mat4)) =
      (-2 * ∑ r, u r ^ 2) • (1 : Mat4) := by
    rw [← Finset.sum_smul]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hs] at h
  have hh := congrArg (fun M : Mat4 => (1 / 2 : ℝ) • M) h
  have hscalar : (1 / 2 : ℝ) * (-2 * ∑ r, u r ^ 2) = -(∑ r, u r ^ 2) := by ring
  simpa only [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
    one_smul, hscalar] using hh

theorem imaginaryCombination_transpose
    (Q : Fin 3 → Mat4) (hQ : ∀ r, (Q r)ᵀ = -Q r) (u : Fin 3 → ℝ) :
    (imaginaryCombination Q u)ᵀ = -imaginaryCombination Q u := by
  ext i j
  simp only [imaginaryCombination, Matrix.transpose_apply, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r _
  have h := congrArg (fun M : Mat4 => M i j) (hQ r)
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  rw [h]
  ring

theorem imaginaryCombination_anticommutator
    (Q : Fin 3 → Mat4)
    (hQ : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Mat4))
    (u : Fin 3 → ℝ) (s : Fin 3) :
    imaginaryCombination Q u * Q s + Q s * imaginaryCombination Q u =
      (-2 * u s) • (1 : Mat4) := by
  simp only [imaginaryCombination, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul]
  rw [← Finset.sum_add_distrib]
  simp_rw [← smul_add, hQ]
  simp only [smul_smul]
  simp only [mul_ite, mul_zero, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  ring

/-- The lifted spectral change sends each imaginary basis element to
its line reflection. -/
theorem axisReflection_combination (Q : Fin 3 → Mat4) (u : Fin 3 → ℝ) (s : Fin 3) :
    (∑ r, axisReflection u r s • Q r) =
      (2 * u s) • imaginaryCombination Q u - Q s := by
  simp only [axisReflection, sub_smul, Finset.sum_sub_distrib,
    ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  simp only [imaginaryCombination, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  ring

/-- A unit pure quaternion is an orthogonal four-frame transformation. -/
theorem imaginaryCombination_orthogonal
    (Q : Fin 3 → Mat4)
    (hanti : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Mat4))
    (hskew : ∀ r, (Q r)ᵀ = -Q r)
    (u : Fin 3 → ℝ) (hu : ∑ r, u r ^ 2 = 1) :
    (imaginaryCombination Q u)ᵀ * imaginaryCombination Q u = 1 := by
  rw [imaginaryCombination_transpose Q hskew, Matrix.neg_mul,
    imaginaryCombination_square Q hanti, hu]
  norm_num

/-- The explicit intertwining law for the imaginary basis, with the
line reflection represented by a unit pure quaternion. -/
theorem imaginaryCombination_intertwines
    (Q : Fin 3 → Mat4)
    (hanti : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Mat4))
    (u : Fin 3 → ℝ) (hu : ∑ r, u r ^ 2 = 1) (s : Fin 3) :
    imaginaryCombination Q u * Q s =
      (∑ r, axisReflection u r s • Q r) * imaginaryCombination Q u := by
  have h := imaginaryCombination_anticommutator Q hanti u s
  rw [axisReflection_combination, Matrix.sub_mul, Matrix.smul_mul,
    imaginaryCombination_square Q hanti, hu]
  simp only [smul_smul, mul_neg, mul_one]
  simpa only [neg_mul] using eq_sub_of_add_eq h

/-- A left pure-quaternion frame change fixes the opposite triple. -/
theorem imaginaryLeft_commutes_opposite (u : Fin 3 → ℝ) (s : Fin 3) :
    imaginaryCombination quaternionMatrix u * Angular.oppositeMatrix s =
      Angular.oppositeMatrix s * imaginaryCombination quaternionMatrix u := by
  simp only [imaginaryCombination, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul]
  apply Finset.sum_congr rfl
  intro r _
  rw [Angular.oppositeMatrix_commute]

/-- A right pure-quaternion frame change fixes the positive triple. -/
theorem imaginaryRight_commutes_positive (u : Fin 3 → ℝ) (s : Fin 3) :
    imaginaryCombination Angular.oppositeMatrix u * quaternionMatrix s =
      quaternionMatrix s * imaginaryCombination Angular.oppositeMatrix u := by
  simp only [imaginaryCombination, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul]
  apply Finset.sum_congr rfl
  intro r _
  rw [Angular.oppositeMatrix_commute]

theorem oppositeMatrix_transpose (r : Fin 3) :
    (Angular.oppositeMatrix r)ᵀ = -Angular.oppositeMatrix r := by
  ext i j
  change Geometry.oppositeQuaternion r j i = -Geometry.oppositeQuaternion r i j
  fin_cases r <;> fin_cases i <;> fin_cases j <;>
    norm_num [Geometry.oppositeQuaternion, quaternionMatrix]

/-- The unit pure-quaternion lifts preserve four-dimensional orientation. -/
private theorem imaginaryLeft_matrix (u : Fin 3 → ℝ) :
    imaginaryCombination quaternionMatrix u =
      ![![0, -u 0, -u 1, -u 2], ![u 0, 0, -u 2, u 1],
        ![u 1, u 2, 0, -u 0], ![u 2, -u 1, u 0, 0]] := by
  ext i j
  change (∑ r, u r * quaternionMatrix r i j) = _
  fin_cases i <;> fin_cases j <;>
    norm_num [imaginaryCombination, quaternionMatrix, Fin.sum_univ_three]

private theorem imaginaryRight_matrix (u : Fin 3 → ℝ) :
    imaginaryCombination Angular.oppositeMatrix u =
      ![![0, u 0, u 1, u 2], ![-u 0, 0, -u 2, u 1],
        ![-u 1, u 2, 0, -u 0], ![-u 2, -u 1, u 0, 0]] := by
  ext i j
  change (∑ r, u r * Geometry.oppositeQuaternion r i j) = _
  fin_cases i <;> fin_cases j <;>
    norm_num [imaginaryCombination, Angular.oppositeMatrix,
      Geometry.oppositeQuaternion, quaternionMatrix, Fin.sum_univ_three]

theorem imaginaryLeft_det (u : Fin 3 → ℝ) :
    Matrix.det (imaginaryCombination quaternionMatrix u) = (∑ r, u r ^ 2) ^ 2 := by
  let L : Mat4 := ![![0, -u 0, -u 1, -u 2], ![u 0, 0, -u 2, u 1],
    ![u 1, u 2, 0, -u 0], ![u 2, -u 1, u 0, 0]]
  have hL : imaginaryCombination quaternionMatrix u = L := imaginaryLeft_matrix u
  rw [hL, Matrix.det_succ_row_zero L]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
  norm_num [L, Fin.sum_univ_three, Fin.succAbove, Fin.lt_def]
  ring

theorem imaginaryRight_det (u : Fin 3 → ℝ) :
    Matrix.det (imaginaryCombination Angular.oppositeMatrix u) = (∑ r, u r ^ 2) ^ 2 := by
  let L : Mat4 := ![![0, u 0, u 1, u 2], ![-u 0, 0, -u 2, u 1],
    ![-u 1, u 2, 0, -u 0], ![-u 2, -u 1, u 0, 0]]
  have hL : imaginaryCombination Angular.oppositeMatrix u = L := imaginaryRight_matrix u
  rw [hL, Matrix.det_succ_row_zero L]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
  norm_num [L, Fin.sum_univ_three, Fin.succAbove, Fin.lt_def]
  ring

theorem imaginaryLeft_det_one (u : Fin 3 → ℝ) (hu : ∑ r, u r ^ 2 = 1) :
    Matrix.det (imaginaryCombination quaternionMatrix u) = 1 := by
  rw [imaginaryLeft_det, hu, one_pow]

theorem imaginaryRight_det_one (u : Fin 3 → ℝ) (hu : ∑ r, u r ^ 2 = 1) :
    Matrix.det (imaginaryCombination Angular.oppositeMatrix u) = 1 := by
  rw [imaginaryRight_det, hu, one_pow]

/-- The coefficient matrix is precisely the ordinary line reflection
that occurs as minus a Cartan–Dieudonné plane reflection. -/
theorem axisReflection_apply (u x : EuclideanSpace ℝ (Fin 3)) (hu : ‖u‖ = 1) :
    WithLp.toLp 2 (axisReflection u *ᵥ (x : Fin 3 → ℝ)) =
      (Submodule.reflection (ℝ ∙ u)) x := by
  rw [Submodule.reflection_singleton_apply, hu]
  ext i
  simp only [axisReflection, Matrix.mulVec, dotProduct, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  norm_num [Fin.sum_univ_three]
  ring

end
end PositiveEinsteinFour.QuaternionFrame

end OAI
