import OAI.GroupTheory.PolycyclicRecognition.Geometry.FaithfulTriangularRepresentation
import Mathlib.LinearAlgebra.Matrix.Reindex

namespace OAI

/-! # Positive-size padding for the triangular representation

A trivial one-dimensional summand handles zero-dimensional Lie algebras
without a separate group-realization case.
-/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance 100] LieRing.ofAssociativeRing

def matrixTrivialSummand (m : ℕ) :
    Matrix (Fin m) (Fin m) ℝ →ₗ⁅ℝ⁆ Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) ℝ where
  toFun A := Matrix.fromBlocks A 0 0 0
  map_add' A B := by ext i j; cases i <;> cases j <;> simp
  map_smul' r A := by ext i j; cases i <;> cases j <;> simp
  map_lie' {A B} := by
    simp only [Ring.lie_def, Matrix.fromBlocks_multiply, mul_zero, add_zero]
    ext i j; cases i <;> cases j <;> simp

def padTriangularMatrix (m : ℕ) :
    Matrix (Fin m) (Fin m) ℝ →ₗ⁅ℝ⁆ Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  (Matrix.reindexAlgEquiv ℝ ℝ (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1))).toLieEquiv.toLieHom.comp
    (matrixTrivialSummand m)

theorem padTriangularMatrix_apply (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ)
    (i j : Fin m ⊕ Fin 1) :
    padTriangularMatrix m A (finSumFinEquiv i) (finSumFinEquiv j) =
      Matrix.fromBlocks A 0 0 0 i j := by
  simp [padTriangularMatrix, matrixTrivialSummand, Matrix.coe_reindexAlgEquiv]

theorem padTriangularMatrix_injective (m : ℕ) : Function.Injective (padTriangularMatrix m) := by
  intro A B h
  ext i j
  have h' := congrArg (fun M => M (finSumFinEquiv (Sum.inl i))
    (finSumFinEquiv (Sum.inl j))) h
  simpa only [padTriangularMatrix_apply, Matrix.fromBlocks_apply₁₁] using h'

theorem padTriangularMatrix_upper (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsUpperTriangular) : (padTriangularMatrix m A).IsUpperTriangular := by
  intro i j hji
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).surjective j
  rw [padTriangularMatrix_apply]
  cases i with
  | inl i =>
    cases j with
    | inl j => exact hA hji
    | inr j => simp
  | inr i => cases j <;> simp

theorem padTriangularMatrix_nilpotent (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsUpperTriangular) (hn : IsNilpotent A) : IsNilpotent (padTriangularMatrix m A) := by
  apply upperTriangular_nilpotent_of_diag_zero _ (padTriangularMatrix_upper m A hA)
  intro i
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).surjective i
  rw [padTriangularMatrix_apply]
  cases i with
  | inl i => exact upperTriangular_nilpotent_diag A hA hn i
  | inr i => simp

theorem exists_positive_faithful_triangular_representation
    {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    [LieAlgebra.IsSolvable L] {n : ℕ} (T : TriangularAdjoint L n) :
    ∃ m : ℕ, 0 < m ∧ ∃ j : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ,
      Function.Injective j ∧ (∀ x, (j x).IsUpperTriangular) ∧
      ∀ x ∈ T.kernelIdeal, IsNilpotent (j x) := by
  obtain ⟨H, hH, _⟩ := exists_cartan_model T
  let := hH
  obtain ⟨m, j, hj, hu, hn⟩ := exists_faithful_triangular_nilradical_representation T H
  exact ⟨m + 1, Nat.succ_pos m, (padTriangularMatrix m).comp j,
    (padTriangularMatrix_injective m).comp hj,
    fun x => padTriangularMatrix_upper m (j x) (hu x),
    fun x hx => padTriangularMatrix_nilpotent m (j x) (hu x) (hn x hx)⟩

end PolycyclicRecognition

end

end OAI
