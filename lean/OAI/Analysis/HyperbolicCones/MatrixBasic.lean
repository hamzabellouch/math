import OAI.Analysis.HyperbolicCones.Model

namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

universe u

namespace Paper256

theorem sym_isHermitian {n : ℕ} (X : Sym n) : (X : Mat n ℝ).IsHermitian := X.property

theorem qMatrix_smul {R : Type u} [CommRing R] (y : Fin 3 → R) (s : R) :
    qMatrix (s • y) = s ^ 2 • qMatrix y := by
  ext i j
  by_cases h : i = j <;> simp [qMatrix, h, mul_pow] <;> ring

theorem phi_add {R : Type u} [CommRing R] (y : Fin 3 → R) (X Z : Mat 4 R) :
    phi y (X + Z) = phi y X + phi y Z := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [phi, Matrix.trace, Matrix.mul_apply, Matrix.submatrix,
      Finset.sum_add_distrib, mul_add, add_mul, add_comm]

theorem phi_smul {R : Type u} [CommRing R] (y : Fin 3 → R) (s : R) (X : Mat 4 R) :
    phi y (s • X) = s • phi y X := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [phi, Matrix.trace, Matrix.mul_apply, Matrix.submatrix,
      ← Finset.mul_sum, mul_left_comm, mul_assoc]

theorem phi_zero {R : Type u} [CommRing R] (y : Fin 3 → R) : phi y (0 : Mat 4 R) = 0 := by
  simpa using phi_smul y 0 (0 : Mat 4 R)

theorem phi_scaling_general {R : Type u} [CommRing R]
    (y : Fin 3 → R) (s : R) (X : Mat 4 R) :
    phi (s • y) X = s ^ 2 • phi y X := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [phi, qMatrix_smul, Matrix.trace, Matrix.mul_apply, Matrix.submatrix,
      ← Finset.mul_sum, mul_left_comm, mul_assoc]

theorem phi_scaling (y : Fin 3 → ℝ) (s : ℝ) (X : Mat 4 ℝ) :
    phi (s • y) X = s ^ 2 • phi y X :=
  phi_scaling_general y s X

theorem phi_zero_parameter {R : Type u} [CommRing R] (X : Mat 4 R) :
    phi (0 : Fin 3 → R) X = 0 := by
  simpa using phi_scaling_general (0 : Fin 3 → R) 0 X

theorem phi_neg_parameter {R : Type u} [CommRing R] (y : Fin 3 → R) (X : Mat 4 R) :
    phi (-y) X = phi y X := by
  simpa using phi_scaling_general y (-1) X

theorem phi_rank_one (y : Fin 3 → ℝ) (u v : Vec 4) :
    dotProduct (fun i => u i) (phi y (outer v) *ᵥ (fun i => u i)) =
      choiLam (wedgeCoordinates v u) y := by
  simp [dotProduct, mulVec, phi, Matrix.trace, Matrix.mul_apply, Matrix.submatrix,
    qMatrix, outer, wedgeCoordinates, choiLam, Fin.sum_univ_succ]
  ring

theorem matrixValue_inverse {K : Type u} [Field K] (X Z : Mat 4 K) (y : Fin 3 → K)
    (hX : IsUnit (Matrix.det X)) :
    matrixValue X Z y = Matrix.det X ^ 4 * Matrix.det (Z - phi y X⁻¹) := by
  have hadj : X.adjugate = X.det • X⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ hX, one_smul]
  rw [matrixValue, hadj, phi_smul, ← smul_sub, Matrix.det_smul]
  rfl

end Paper256

end

end OAI
