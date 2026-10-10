import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTensorMatrix
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorGraph

namespace OAI

/-! Splitting off the first physical block in a finite tensor Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical ComplexOrder
variable {σ τ : Type*} {n : ℕ}

def qmaTensorSuccEquiv (σ : Type*) (n : ℕ) : (Fin (n+1) → σ) ≃ σ × (Fin n → σ) where
  toFun s := (s 0, fun i => s i.succ)
  invFun s := Fin.cases s.1 s.2
  left_inv s := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv s := by cases s; rfl

theorem qmaTensorMatrix_succ (A : Fin (n+1) → Matrix σ τ ℂ) :
    qmaTensorMatrix A =
      (A 0 ⊗ₖ qmaTensorMatrix (fun i : Fin n => A i.succ)).submatrix
        (qmaTensorSuccEquiv σ n) (qmaTensorSuccEquiv τ n) := by
  ext s t
  simp only [qmaTensorMatrix,Matrix.submatrix_apply,Matrix.kroneckerMap_apply,Fin.prod_univ_succ]
  rfl

variable [Fintype σ] [DecidableEq σ]

omit [Fintype σ] in
theorem qmaSiteMatrix_succ_zero (H : Matrix σ σ ℂ) :
    qmaSiteMatrix (0:Fin (n+1)) H =
      (H ⊗ₖ (1 : Matrix (Fin n → σ) (Fin n → σ) ℂ)).submatrix
        (qmaTensorSuccEquiv σ n) (qmaTensorSuccEquiv σ n) := by
  rw [qmaSiteMatrix,qmaTensorMatrix_succ]
  simp only [ite_true,Fin.succ_ne_zero,ite_false,qmaTensorMatrix_one]

omit [Fintype σ] in
theorem qmaSiteMatrix_succ_succ (i : Fin n) (H : Matrix σ σ ℂ) :
    qmaSiteMatrix i.succ H =
      ((1 : Matrix σ σ ℂ) ⊗ₖ qmaSiteMatrix i H).submatrix
        (qmaTensorSuccEquiv σ n) (qmaTensorSuccEquiv σ n) := by
  rw [qmaSiteMatrix,qmaTensorMatrix_succ]
  have hz : (0:Fin (n+1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  simp only [hz,ite_false,Fin.succ_inj]
  rfl

def qmaTensorPenalty (n : ℕ) (H : Matrix σ σ ℂ) :
    Matrix (Fin n → σ) (Fin n → σ) ℂ := ∑ i : Fin n, qmaSiteMatrix i H

omit [Fintype σ] in
theorem qmaTensorPenalty_succ (H : Matrix σ σ ℂ) :
    qmaTensorPenalty (n+1) H =
      (H ⊗ₖ (1 : Matrix (Fin n → σ) (Fin n → σ) ℂ)+
        (1 : Matrix σ σ ℂ) ⊗ₖ qmaTensorPenalty n H).submatrix
        (qmaTensorSuccEquiv σ n) (qmaTensorSuccEquiv σ n) := by
  rw [qmaTensorPenalty,Fin.sum_univ_succ,qmaSiteMatrix_succ_zero]
  simp only [qmaSiteMatrix_succ_succ,← MediatorGraph.submatrix_sum,
    ← MediatorGraph.kronecker_sum,← MediatorGraph.submatrix_add_apply,qmaTensorPenalty]

end ContinuumCoulomb

end

end OAI
