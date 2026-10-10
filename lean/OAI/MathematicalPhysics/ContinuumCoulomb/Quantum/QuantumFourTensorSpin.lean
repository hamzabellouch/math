import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTensorAction

namespace OAI

/-! Single physical-spin excitations in the full tensor code. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourTensorSpinColumn (n : ℕ) (i : Fin n) (p : Fin 4) (μ : Fin 3) :
    Matrix (Fin n → Fin 16) (Fin n → Fin 2) ℂ :=
  qmaTensorMatrix (fun k => if k = i then qmaFourSpin p μ*qmaFourEncoding else qmaFourEncoding)

theorem qmaFourTensorSpinColumn_action (n : ℕ) (i : Fin n) (p : Fin 4) (μ : Fin 3) :
    qmaSiteMatrix i (qmaFourSpin p μ)*qmaFourTensorEncoding n = qmaFourTensorSpinColumn n i p μ := by
  rw [qmaFourTensorEncoding,qmaSiteMatrix_tensor]
  rfl

theorem qmaFourTensorSpinColumn_orthogonal (n : ℕ) (i : Fin n) (p : Fin 4) (μ : Fin 3) :
    (qmaFourTensorEncoding n).conjTranspose*qmaFourTensorSpinColumn n i p μ = 0 := by
  rw [qmaFourTensorEncoding,qmaFourTensorSpinColumn,qmaTensorMatrix_star,qmaTensorMatrix_mul]
  apply qmaTensorMatrix_zero_at _ i
  simp only [ite_true,← Matrix.mul_assoc,qmaFourSpin_orthogonal]

theorem qmaFourTensorSpinColumn_excitation (n : ℕ) (i : Fin n) (p : Fin 4) (μ : Fin 3) :
    qmaFourTensorPenalty n*qmaFourTensorSpinColumn n i p μ =
      (4:ℂ) • qmaFourTensorSpinColumn n i p μ := by
  have h := qmaTensorPenalty_eigen qmaFourPenalty
    (fun k : Fin n => if k = i then qmaFourSpin p μ*qmaFourEncoding else qmaFourEncoding)
    (fun k => if k = i then (4:ℂ) else 0) (by
      intro k
      by_cases hk : k = i
      · simp only [hk,ite_true]
        exact qmaFourSpin_excitation p μ
      · simp only [hk,ite_false,zero_smul,qmaFourPenalty_encoding])
  simpa only [qmaFourTensorPenalty,qmaFourTensorSpinColumn,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true] using h

end ContinuumCoulomb

end

end OAI
