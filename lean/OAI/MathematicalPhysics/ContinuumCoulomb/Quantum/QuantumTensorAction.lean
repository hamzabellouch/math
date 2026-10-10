import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorGap

namespace OAI

/-! Local actions and excitation energies of actual finite tensor columns. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {Q σ τ : Type*} [Fintype Q] [DecidableEq Q]
  [Fintype σ] [DecidableEq σ] [Fintype τ]

omit [Fintype τ] in
theorem qmaSiteMatrix_tensor (i : Q) (A : Matrix σ σ ℂ) (B : Q → Matrix σ τ ℂ) :
    qmaSiteMatrix i A*qmaTensorMatrix B =
      qmaTensorMatrix (fun j => if j = i then A*B j else B j) := by
  rw [qmaSiteMatrix,qmaTensorMatrix_mul]
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]

omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq Q] in
theorem qmaTensorMatrix_zero_at (A : Q → Matrix σ τ ℂ) (i : Q) (hA : A i = 0) :
    qmaTensorMatrix A = 0 := by
  ext s t
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hA])

omit [Fintype σ] [DecidableEq σ] [Fintype τ] in
theorem qmaTensorMatrix_smul_at (A : Q → Matrix σ τ ℂ) (i : Q) (c : ℂ) :
    qmaTensorMatrix (fun j => if j = i then c • A j else A j) = c • qmaTensorMatrix A := by
  ext s t
  simp only [qmaTensorMatrix,Matrix.smul_apply,smul_eq_mul]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true,Matrix.smul_apply,smul_eq_mul]
  have hp : (∏ j ∈ Finset.univ.erase i,
      (if j = i then c • A j else A j) (s j) (t j)) =
      ∏ j ∈ Finset.univ.erase i, A j (s j) (t j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [ite_eq_right (Finset.mem_erase.mp hj).1]
  rw [hp]
  ring

omit [Fintype τ] in
theorem qmaSiteMatrix_tensor_eigen (i : Q) (H : Matrix σ σ ℂ) (A : Q → Matrix σ τ ℂ)
    (c : ℂ) (hA : H*A i = c • A i) :
    qmaSiteMatrix i H*qmaTensorMatrix A = c • qmaTensorMatrix A := by
  rw [qmaSiteMatrix_tensor,← qmaTensorMatrix_smul_at A i c]
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    simp only [ite_true,hA]
  · simp only [hj,ite_false]

variable {n : ℕ}

omit [Fintype τ] in
theorem qmaTensorPenalty_eigen (H : Matrix σ σ ℂ) (A : Fin n → Matrix σ τ ℂ)
    (c : Fin n → ℂ) (hA : ∀ i, H*A i = c i • A i) :
    qmaTensorPenalty n H*qmaTensorMatrix A = (∑ i, c i) • qmaTensorMatrix A := by
  rw [qmaTensorPenalty,Matrix.sum_mul]
  simp only [qmaSiteMatrix_tensor_eigen _ H A _ (hA _),Finset.sum_smul]

theorem qmaFourTensorPenalty_encoding (n : ℕ) :
    qmaFourTensorPenalty n*qmaFourTensorEncoding n = 0 := by
  have h := qmaTensorPenalty_eigen qmaFourPenalty (fun _ : Fin n => qmaFourEncoding)
    (fun _ => (0:ℂ)) (by intro i; simp [qmaFourPenalty_encoding])
  simpa only [qmaFourTensorPenalty,qmaFourTensorEncoding,Finset.sum_const_zero,zero_smul] using h

end ContinuumCoulomb

end

end OAI
