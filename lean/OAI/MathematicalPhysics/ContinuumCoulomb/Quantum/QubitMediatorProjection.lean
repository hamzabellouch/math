import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRectangularOperator
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.DiagonalPenalty

namespace OAI

/-! The exact vacuum and complementary projections for the physical qubits. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

def qmaMediatorVacuumColumn : Matrix (σ × (κ → Fin 2)) σ ℂ :=
  qmaSliceColumn qmaAncillaVacuum 1

def qmaMediatorHighMatrix : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  qmaAncillaDiagonal (fun a => if a = qmaAncillaVacuum then 0 else 1)

omit [Fintype σ] [DecidableEq κ] in
theorem qmaAncillaDiagonal_eq (w : (κ → Fin 2) → ℂ) :
    (qmaAncillaDiagonal w : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ) =
      Matrix.diagonal (fun p => w p.2) := by
  ext ⟨s,a⟩ ⟨t,b⟩
  by_cases hs : s = t <;> by_cases hab : a = b <;>
    simp [qmaAncillaDiagonal,Prod.mk.injEq,hs,hab]

theorem qmaMediatorVacuum_gram :
    (qmaMediatorVacuumColumn (σ := σ) (κ := κ)).conjTranspose*
      qmaMediatorVacuumColumn (σ := σ) (κ := κ) = 1 := by
  rw [qmaMediatorVacuumColumn,qmaSliceColumn_gram]
  simp

theorem qmaMediatorHigh_column (V : κ → Matrix σ σ ℂ) :
    qmaMediatorHighMatrix*qmaAncillaColumn V = qmaAncillaColumn V := by
  unfold qmaMediatorHighMatrix
  simpa only [one_smul] using qmaAncillaDiagonal_column
    (fun a => if a = qmaAncillaVacuum then (0:ℂ) else 1) V 1
    (fun e => ite_eq_right (qmaAncillaSingle_ne_vacuum e))

theorem qmaMediatorHigh_vacuum :
    (qmaMediatorHighMatrix (σ := σ) (κ := κ))*qmaMediatorVacuumColumn (σ := σ) (κ := κ) = 0 := by
  rw [qmaMediatorHighMatrix,qmaMediatorVacuumColumn,qmaAncillaDiagonal_slice]
  simp

omit [Fintype σ] [DecidableEq κ] in
theorem qmaMediatorHigh_star :
    (qmaMediatorHighMatrix (σ := σ) (κ := κ)).conjTranspose = qmaMediatorHighMatrix := by
  rw [qmaMediatorHighMatrix,qmaAncillaDiagonal_eq]
  ext p q
  by_cases hpq : p = q
  · subst q
    by_cases hp : p.2 = qmaAncillaVacuum <;>
      simp [Matrix.conjTranspose_apply,hp]
  · simp [Matrix.conjTranspose_apply,hpq,Ne.symm hpq]

theorem qmaMediatorHigh_square :
    (qmaMediatorHighMatrix (σ := σ) (κ := κ))*qmaMediatorHighMatrix = qmaMediatorHighMatrix := by
  simp only [qmaMediatorHighMatrix,qmaAncillaDiagonal_eq,Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  split_ifs <;> norm_num

theorem qmaMediatorVacuum_high :
    (qmaMediatorVacuumColumn (σ := σ) (κ := κ)).conjTranspose*
      qmaMediatorHighMatrix (σ := σ) (κ := κ) = 0 := by
  have h := congrArg Matrix.conjTranspose (qmaMediatorHigh_vacuum (σ := σ) (κ := κ))
  simpa only [Matrix.conjTranspose_mul,qmaMediatorHigh_star,Matrix.conjTranspose_zero] using h

omit [DecidableEq κ] in
theorem qmaMediator_projection_sum :
    (qmaMediatorVacuumColumn (σ := σ) (κ := κ))*qmaMediatorVacuumColumn.conjTranspose+
      qmaMediatorHighMatrix = 1 := by
  rw [qmaMediatorHighMatrix,qmaAncillaDiagonal_eq]
  ext ⟨s,a⟩ ⟨t,b⟩
  by_cases ha : a = qmaAncillaVacuum <;> by_cases hb : b = qmaAncillaVacuum <;>
    simp [qmaMediatorVacuumColumn,qmaSliceColumn,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.one_apply,Matrix.diagonal_apply,ha,hb,eq_comm,Prod.mk.injEq]

theorem qmaMediatorHigh_norm :
    ‖spinMatrixOperator (qmaMediatorHighMatrix (σ := σ) (κ := κ))‖ ≤ 1 := by
  have he : (spinMatrixOperator (qmaMediatorHighMatrix (σ := σ) (κ := κ))).restrictScalars ℝ =
      diagonalPenalty (fun p : σ × (κ → Fin 2) => if p.2 = qmaAncillaVacuum then 0 else 1) := by
    ext x p
    change spinMatrixOperator qmaMediatorHighMatrix x p = _
    rw [qmaMediatorHighMatrix,qmaAncillaDiagonal_eq]
    simp [spinMatrixOperator_apply,Matrix.diagonal_apply]
  have hn := congrArg (fun f => ‖f‖) he
  rw [ContinuousLinearMap.norm_restrictScalars] at hn
  rw [hn]
  apply diagonalPenalty_norm_le _ zero_le_one
  intro p
  split_ifs <;> norm_num

end ContinuumCoulomb

end

end OAI
