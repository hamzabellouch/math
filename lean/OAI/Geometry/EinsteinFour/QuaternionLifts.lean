import OAI.Geometry.EinsteinFour.QuaternionReflections

namespace OAI

/-! Composition of the concrete quaternion frame changes.  These identities
keep the action on both Weyl blocks, so they can be used at a single point
without selecting a moving eigenframe. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

/-- A concrete oriented four-frame lift of a change in one quaternion basis.
The opposite quaternion basis is fixed. -/
structure QuaternionLift (Q O : Fin 3 → Mat4) (A : Mat) where
  matrix : Mat4
  orthogonal : matrixᵀ * matrix = 1
  orientation : Matrix.det matrix = 1
  intertwines : ∀ s, matrix * Q s = (∑ r, A r s • Q r) * matrix
  opposite : ∀ s, matrix * O s = O s * matrix

/-- The generator intertwining identity extends to every imaginary quaternion. -/
theorem intertwines_combination (Q : Fin 3 → Mat4) (A : Mat) (P : Mat4)
    (hP : ∀ s, P * Q s = (∑ r, A r s • Q r) * P) (u : Fin 3 → ℝ) :
    P * imaginaryCombination Q u = imaginaryCombination Q (A *ᵥ u) * P := by
  simp only [imaginaryCombination, Matrix.mul_sum, Matrix.mul_smul, hP,
    Matrix.sum_mul, Matrix.smul_mul, Finset.smul_sum, smul_smul,
    Finset.sum_smul, Matrix.mulVec, dotProduct]
  change (∑ s, ∑ r, (u s * A r s) • (Q r * P)) =
    ∑ r, ∑ s, (A r s * u s) • (Q r * P)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  ring

/-- Products of four-frame lifts induce the corresponding product of
three-dimensional coefficient changes. -/
def QuaternionLift.mul {Q O : Fin 3 → Mat4} {A B : Mat}
    (P : QuaternionLift Q O A) (R : QuaternionLift Q O B) : QuaternionLift Q O (A * B) where
  matrix := P.matrix * R.matrix
  orthogonal := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc P.matrixᵀ,
      P.orthogonal, Matrix.one_mul, R.orthogonal]
  orientation := by rw [Matrix.det_mul, P.orientation, R.orientation, one_mul]
  intertwines := by
    intro s
    calc
      (P.matrix * R.matrix) * Q s = P.matrix * (R.matrix * Q s) := Matrix.mul_assoc _ _ _
      _ = P.matrix * ((∑ r, B r s • Q r) * R.matrix) := by rw [R.intertwines]
      _ = (P.matrix * imaginaryCombination Q (fun r => B r s)) * R.matrix := by
        rw [← Matrix.mul_assoc]
        rfl
      _ = (imaginaryCombination Q (A *ᵥ (fun r => B r s)) * P.matrix) * R.matrix := by
        rw [intertwines_combination Q A P.matrix P.intertwines]
      _ = (∑ r, (A * B) r s • Q r) * (P.matrix * R.matrix) := by
        rw [Matrix.mul_assoc]
        rfl
  opposite := by
    intro s
    rw [Matrix.mul_assoc, R.opposite, ← Matrix.mul_assoc, P.opposite,
      Matrix.mul_assoc]

/-- The identity frame lifts the identity change in a quaternion basis. -/
def QuaternionLift.one (Q O : Fin 3 → Mat4) : QuaternionLift Q O 1 where
  matrix := 1
  orthogonal := by simp
  orientation := Matrix.det_one
  intertwines := by
    intro s
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.one_apply, ite_smul,
      one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  opposite := by intro s; rw [Matrix.one_mul, Matrix.mul_one]

/-- Every unit axis reflection has an explicit left-quaternion lift. -/
def QuaternionLift.leftAxis (u : Fin 3 → ℝ) (hu : ∑ r, u r ^ 2 = 1) :
    QuaternionLift quaternionMatrix Angular.oppositeMatrix (axisReflection u) where
  matrix := imaginaryCombination quaternionMatrix u
  orthogonal := imaginaryCombination_orthogonal quaternionMatrix
    Angular.quaternionMatrix_anticommutator Angular.quaternionMatrix_transpose u hu
  orientation := imaginaryLeft_det_one u hu
  intertwines := imaginaryCombination_intertwines quaternionMatrix
    Angular.quaternionMatrix_anticommutator u hu
  opposite := imaginaryLeft_commutes_opposite u

/-- Every unit axis reflection has an explicit right-quaternion lift. -/
def QuaternionLift.rightAxis (u : Fin 3 → ℝ) (hu : ∑ r, u r ^ 2 = 1) :
    QuaternionLift Angular.oppositeMatrix quaternionMatrix (axisReflection u) where
  matrix := imaginaryCombination Angular.oppositeMatrix u
  orthogonal := imaginaryCombination_orthogonal Angular.oppositeMatrix
    Angular.oppositeMatrix_anticommutator oppositeMatrix_transpose u hu
  orientation := imaginaryRight_det_one u hu
  intertwines := imaginaryCombination_intertwines Angular.oppositeMatrix
    Angular.oppositeMatrix_anticommutator u hu
  opposite := imaginaryRight_commutes_positive u

end
end PositiveEinsteinFour.QuaternionFrame

end OAI
