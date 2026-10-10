import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumReferenceTensor

namespace OAI

/-! Exact diagonal tensors and the computational-basis reference-chain penalty. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem sourceTensor_diagonal (n : ℕ) (d : Fin n → Fin 2 → ℂ) :
    sourceTensor n (fun i => Matrix.diagonal (d i)) =
      Matrix.diagonal (fun s => ∏ i, d i (s i)) := by
  ext s t
  by_cases h : s = t
  · subst t
    simp [sourceTensor]
  · rw [Matrix.diagonal_apply_ne _ h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

def qmaZSign (b : Fin 2) : ℂ := if b = 0 then 1 else -1

theorem pauliZ_diagonal : pauliZ = Matrix.diagonal qmaZSign := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pauliZ,qmaZSign]

theorem sourceLocalPauli_z_diagonal (n : ℕ) (i : Fin n) :
    sourceLocalPauli n i 2 = Matrix.diagonal (fun s => qmaZSign (s i)) := by
  have hlocal (k : Fin n) : (if k = i then pauli 2 else (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      Matrix.diagonal (fun b => if k = i then qmaZSign b else 1) := by
    by_cases hk : k = i
    · simp only [hk,ite_true]
      exact pauliZ_diagonal
    · simp [hk]
  unfold sourceLocalPauli
  simp_rw [hlocal]
  rw [sourceTensor_diagonal]
  congr 1
  funext s
  simp

theorem qmaZSign_wall (a b : Fin 2) :
    (1/2 : ℂ)*(1-qmaZSign a*qmaZSign b) = if a = b then 0 else 1 := by
  fin_cases a <;> fin_cases b <;> norm_num [qmaZSign]

def qmaReferenceZPenalty (n : ℕ) :
    Matrix (SourceSpinBasis (n+1)) (SourceSpinBasis (n+1)) ℂ :=
  ∑ i : Fin n, (1/2 : ℂ) • (1-sourceLocalPauli (n+1) i.castSucc 2*
    sourceLocalPauli (n+1) i.succ 2)

theorem qmaReferenceZPenalty_diagonal (n : ℕ) :
    qmaReferenceZPenalty n = qmaReferenceWallMatrix n := by
  unfold qmaReferenceZPenalty
  simp_rw [sourceLocalPauli_z_diagonal,Matrix.diagonal_mul_diagonal]
  ext s t
  by_cases h : s = t
  · subst t
    simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply,
      Matrix.one_apply_eq,Matrix.diagonal_apply_eq,qmaReferenceWallMatrix]
    simp_rw [qmaZSign_wall]
    simp [qmaReferenceWalls,Finset.card_filter]
  · simp [Matrix.sum_apply,Matrix.smul_apply,qmaReferenceWallMatrix,h]

end ContinuumCoulomb

end

end OAI
