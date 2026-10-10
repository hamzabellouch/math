import Mathlib

namespace OAI

section

open Matrix

namespace KS.W07

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

def scalarPivot (a : K) : Matrix Unit Unit K := fun _ _ => a

def pivotRow (b : n → K) : Matrix Unit n K := fun _ j => b j

def pivotBlock (a : K) (b : n → K) (D : Matrix n n K) :
    Matrix (Unit ⊕ n) (Unit ⊕ n) K :=
  Matrix.fromBlocks (scalarPivot a) (fun _ j => b j) (fun i _ => b i) D

def pivotSchur (a : K) (b : n → K) (D : Matrix n n K) : Matrix n n K :=
  fun i j => D i j - b i * b j / a

def pivotLower (a : K) (b : n → K) : Matrix (Unit ⊕ n) (Unit ⊕ n) K :=
  Matrix.fromBlocks 1 0 (fun i _ => b i / a) 1

def pivotDiagonal (a : K) (b : n → K) (D : Matrix n n K) :
    Matrix (Unit ⊕ n) (Unit ⊕ n) K :=
  Matrix.fromBlocks (scalarPivot a) 0 0 (pivotSchur a b D)

@[implicit_reducible]
def scalarPivotInvertible {a : K} (ha : a ≠ 0) : Invertible (scalarPivot a) where
  invOf := scalarPivot a⁻¹
  invOf_mul_self := by
    ext i j
    cases i; cases j
    simp [scalarPivot, Matrix.mul_apply, ha]
  mul_invOf_self := by
    ext i j
    cases i; cases j
    simp [scalarPivot, Matrix.mul_apply, ha]

theorem scalarPivot_inv {a : K} (ha : a ≠ 0) :
    (scalarPivot a)⁻¹ = scalarPivot a⁻¹ := by
  let := scalarPivotInvertible ha
  exact (Matrix.invOf_eq_nonsing_inv (scalarPivot a)).symm

theorem pivot_ldl {a : K} (ha : a ≠ 0) (b : n → K) (D : Matrix n n K) :
    pivotBlock a b D = pivotLower a b * pivotDiagonal a b D * (pivotLower a b)ᵀ := by
  simp only [pivotBlock, pivotLower, pivotDiagonal]
  ext i j
  cases i with
  | inl i =>
    cases i
    cases j with
    | inl j => cases j; simp [scalarPivot, Matrix.fromBlocks, Matrix.mul_apply]
    | inr j =>
      simp [scalarPivot, Matrix.fromBlocks, Matrix.mul_apply]
      field_simp [ha]
  | inr i =>
    cases j with
    | inl j =>
      cases j
      simp [scalarPivot, Matrix.fromBlocks, Matrix.mul_apply]
      field_simp [ha]
    | inr j =>
      simp [scalarPivot, Matrix.fromBlocks, Matrix.mul_apply, Matrix.one_apply, pivotSchur]
      field_simp [ha]
      ring

def pivotWitnessLift (a : K) (b y : n → K) : Unit ⊕ n → K :=
  Sum.elim (fun _ => -(a⁻¹ * ∑ j, b j * y j)) y

section TrivialStar

variable [StarRing K] [TrivialStar K]

omit [Fintype n] [DecidableEq n] in
theorem pivot_schur_formula {a : K} (ha : a ≠ 0)
    (b : n → K) (D : Matrix n n K) :
    D - (pivotRow b)ᴴ * (scalarPivot a)⁻¹ *
      (pivotRow b) = pivotSchur a b D := by
  ext i j
  simp [scalarPivot_inv ha, scalarPivot, pivotRow, Matrix.mul_apply, pivotSchur]
  ring

omit [DecidableEq n] [StarRing K] [TrivialStar K] in
theorem pivot_lift_cancel {a : K} (ha : a ≠ 0) (b y : n → K) :
    (fun _ : Unit => -(a⁻¹ * ∑ j, b j * y j)) +
      ((scalarPivot a)⁻¹ * (pivotRow b)) *ᵥ y = 0 := by
  ext u
  cases u
  simp [scalarPivot_inv ha, scalarPivot, pivotRow, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Finset.mul_sum, mul_assoc]

omit [DecidableEq n] in
theorem pivotWitnessLift_quadratic {a : K} (ha : a ≠ 0)
    (b y : n → K) (D : Matrix n n K) :
    pivotWitnessLift a b y ⬝ᵥ (pivotBlock a b D *ᵥ pivotWitnessLift a b y) =
      y ⬝ᵥ (pivotSchur a b D *ᵥ y) := by
  let := scalarPivotInvertible ha
  have hA : (scalarPivot a).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [scalarPivot]
  have h := Matrix.schur_complement_eq₁₁
    (pivotRow b) D
    (fun _ : Unit => -(a⁻¹ * ∑ j, b j * y j)) y hA
  rw [pivot_lift_cancel ha, pivot_schur_formula ha] at h
  have hblock : Matrix.fromBlocks (scalarPivot a) (pivotRow b) (pivotRow b)ᴴ D =
      pivotBlock a b D := by
    ext i j
    cases i <;> cases j <;> simp [pivotBlock, pivotRow, Matrix.fromBlocks]
  rw [hblock] at h
  simpa only [← Matrix.dotProduct_mulVec, star_trivial, Matrix.zero_mulVec,
    zero_dotProduct, zero_add, pivotWitnessLift] using h

end TrivialStar

end KS.W07

end

end OAI
