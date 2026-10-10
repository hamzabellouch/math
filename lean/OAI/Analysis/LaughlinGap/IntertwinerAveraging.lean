import Mathlib
import OAI.Analysis.LaughlinGap.IrrepAveraging

namespace OAI

/-! Intertwiner Averaging. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators
open Averaging

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def LadderMap.matrix {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) : Matrix κ ι ℝ := LinearMap.toMatrix' A.toLinearMap

omit [DecidableEq κ] in
@[simp] lemma LadderMap.matrix_mulVec {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) (x : ι → ℝ) : A.matrix.mulVec x = A.toLinearMap x :=
  LinearMap.toMatrix'_mulVec A.toLinearMap x

lemma LadderMap.matrix_lower {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) : loweringMatrix T * A.matrix = A.matrix * loweringMatrix S := by
  apply Matrix.toLin'.injective
  simp only [Matrix.toLin'_mul, loweringMatrix, LadderMap.matrix, Matrix.toLin'_toMatrix']
  exact LinearMap.ext A.lower

lemma LadderMap.matrix_raise {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) : (loweringMatrix T).transpose * A.matrix =
      A.matrix * (loweringMatrix S).transpose := by
  simp only [loweringMatrix_transpose]
  apply Matrix.toLin'.injective
  simp only [Matrix.toLin'_mul, LadderMap.matrix, Matrix.toLin'_toMatrix']
  exact LinearMap.ext A.raise

@[simp] lemma LadderMap.transpose_matrix {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) : A.transpose.matrix = A.matrix.transpose := toMatrix_transposeMap _

noncomputable def copyLift {S : LadderSystem ι} {T : LadderSystem κ}
    (A B : LadderMap S T) : Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ where
  toFun X := A.matrix * X * B.matrix.transpose
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' r X := by simp [Matrix.mul_smul, Matrix.smul_mul]

lemma copyLift_commutator {S : LadderSystem ι} {T : LadderSystem κ}
    (A B : LadderMap S T) (X : Matrix ι ι ℝ) :
    copyLift A B (commutator (loweringMatrix S) X) =
      commutator (loweringMatrix T) (copyLift A B X) := by
  have ht := B.transpose.matrix_lower
  rw [LadderMap.transpose_matrix] at ht
  simp only [copyLift, LinearMap.coe_mk, AddHom.coe_mk, Averaging.commutator,
    Matrix.mul_sub, Matrix.sub_mul]
  rw [← Matrix.mul_assoc A.matrix (loweringMatrix S), ← A.matrix_lower,
    Matrix.mul_assoc (loweringMatrix T), Matrix.mul_assoc (loweringMatrix T),
    Matrix.mul_assoc A.matrix X]
  simp only [Matrix.mul_assoc, ht]

lemma copyLift_commutator_transpose {S : LadderSystem ι} {T : LadderSystem κ}
    (A B : LadderMap S T) (X : Matrix ι ι ℝ) :
    copyLift A B (commutator (loweringMatrix S).transpose X) =
      commutator (loweringMatrix T).transpose (copyLift A B X) := by
  have ht := B.transpose.matrix_raise
  rw [LadderMap.transpose_matrix] at ht
  simp only [copyLift, LinearMap.coe_mk, AddHom.coe_mk, Averaging.commutator,
    Matrix.mul_sub, Matrix.sub_mul]
  rw [← Matrix.mul_assoc A.matrix (loweringMatrix S).transpose, ← A.matrix_raise,
    Matrix.mul_assoc (loweringMatrix T).transpose, Matrix.mul_assoc (loweringMatrix T).transpose,
    Matrix.mul_assoc A.matrix X]
  simp only [Matrix.mul_assoc, ht]

theorem copyLift_average {n : ℕ} {T : LadderSystem κ}
    (A B : LadderMap (standardLadderSystem n) T) (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    average (rotationCommutant (loweringMatrix T)) (copyLift A B X) =
      (X.trace / (n+1 : ℕ)) • (A.matrix * B.matrix.transpose) := by
  rw [rotation_average_natural (copyLift A B) (copyLift_commutator A B)
    (copyLift_commutator_transpose A B), standardSpin_average]
  simp [copyLift]

omit [DecidableEq κ] in
lemma copyLift_rankOne {S : LadderSystem ι} {T : LadderSystem κ}
    (A B : LadderMap S T) (x y : ι → ℝ) :
    copyLift A B (Matrix.vecMulVec x y) =
      Matrix.vecMulVec (A.toLinearMap x) (B.toLinearMap y) := by
  simp only [copyLift, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, LadderMap.matrix_mulVec, Matrix.vecMul_transpose]

lemma trace_rankOne_mul {σ : Type*} [Fintype σ] (x y : σ → ℝ) (C : Matrix σ σ ℝ) :
    (Matrix.vecMulVec x y * C).trace = dotProduct y (C.mulVec x) := by
  rw [Matrix.trace_mul_comm, trace_mul_rankOne]

theorem distinct_copy_average {n m : ℕ} {T : LadderSystem κ} (hnm : n ≠ m)
    (A : LadderMap (standardLadderSystem n) T)
    (B : LadderMap (standardLadderSystem m) T)
    (x : Fin (n+1) → ℝ) (y : Fin (m+1) → ℝ) :
    average (rotationCommutant (loweringMatrix T))
      (Matrix.vecMulVec (A.toLinearMap x) (B.toLinearMap y)) = 0 := by
  apply average_unique _ _ _ (zero_mem _)
  intro C hC
  simp only [sub_zero, Matrix.transpose_vecMulVec, trace_rankOne_mul]
  let L := A.transpose.comp ((commutantLadderMap T hC).comp B)
  have he : L.toLinearMap = 0 := standardLadderMap_eq_zero hnm.symm L
  rw [transposeMap_adjoint]
  have hv := LinearMap.congr_fun he y
  change transposeMap A.toLinearMap (Matrix.toLin' C (B.toLinearMap y)) = 0 at hv
  rw [Matrix.toLin'_apply] at hv
  rw [hv, dotProduct_zero]

theorem equal_copy_average {n : ℕ} {T : LadderSystem κ}
    (A B : LadderMap (standardLadderSystem n) T) (i j : Fin (n+1)) :
    average (rotationCommutant (loweringMatrix T))
      (Matrix.vecMulVec (A.toLinearMap (Pi.single i 1))
        (B.toLinearMap (Pi.single j 1))) =
      (if i=j then (1 : ℝ)/(n+1 : ℕ) else 0) • (A.matrix * B.matrix.transpose) := by
  rw [← copyLift_rankOne, copyLift_average, Matrix.trace_vecMulVec]
  by_cases h : i=j
  · subst j; simp
  · simp [h, eq_comm]

end LaughlinGap.Spin

end

end OAI
