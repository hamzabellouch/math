import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorHilbert
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorSeriesMatrix

namespace OAI

/-! The physical parallel-qubit Hamiltonian has the calculated vacuum column. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

omit [DecidableEq σ] [DecidableEq κ] in
theorem qmaSliceColumn_right_mul (a : κ → Fin 2) (A B : Matrix σ σ ℂ) :
    qmaSliceColumn a A*B = qmaSliceColumn a (A*B) := by
  ext ⟨s,b⟩ t
  by_cases h : b = a <;> simp [Matrix.mul_apply,qmaSliceColumn,h]

def qmaPhysicalPenaltyMatrix (g : ℝ) : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  qmaAncillaDiagonal (fun a => (g*qmaAncillaNumber a : ℝ))

def qmaPhysicalMediatorMatrix (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ) :
    Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  qmaPhysicalPenaltyMatrix g+qmaMediatorPerturbation C D V

theorem qmaPhysicalPenalty_vacuum (g : ℝ) :
    qmaPhysicalPenaltyMatrix (σ := σ) (κ := κ) g*
      qmaMediatorVacuumColumn (σ := σ) (κ := κ) = 0 := by
  rw [qmaPhysicalPenaltyMatrix,qmaMediatorVacuumColumn,qmaAncillaDiagonal_slice]
  simp

theorem qmaLiftedLow_vacuum (C : Matrix σ σ ℂ) :
    (C ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ))*qmaMediatorVacuumColumn =
      qmaMediatorVacuumColumn*C := by
  rw [qmaMediatorVacuumColumn,qmaSliceColumn_right_mul,Matrix.one_mul]
  ext ⟨s,a⟩ t
  rw [qmaSliceColumn_kronecker_apply,Matrix.mul_one]
  simp [qmaSliceColumn,Matrix.one_apply]

theorem qmaPhysicalMediator_vacuum (g : ℝ) (C : Matrix σ σ ℂ)
    (D V : κ → Matrix σ σ ℂ) :
    qmaPhysicalMediatorMatrix g C D V*qmaMediatorVacuumColumn =
      qmaMediatorVacuumColumn*C+qmaAncillaColumn V := by
  have hd0 : qmaMediatorOccupations D*qmaMediatorVacuumColumn (σ := σ) (κ := κ) = 0 := by
    simpa only [qmaMediatorVacuumColumn] using qmaMediatorOccupations_vacuum D
  have hv : qmaMediatorFlips V*qmaMediatorVacuumColumn (σ := σ) (κ := κ) = qmaAncillaColumn V := by
    simpa only [qmaMediatorVacuumColumn] using qmaMediatorFlips_vacuum V
  unfold qmaPhysicalMediatorMatrix qmaMediatorPerturbation
  rw [Matrix.add_mul,qmaPhysicalPenalty_vacuum,zero_add,Matrix.add_mul,Matrix.add_mul,
    qmaLiftedLow_vacuum,hd0,hv,add_zero]

omit [Fintype σ] [DecidableEq κ] in
theorem qmaAncillaDiagonal_real_star (w : (κ → Fin 2) → ℝ) :
    (qmaAncillaDiagonal (σ := σ) (fun a => (w a : ℂ))).conjTranspose =
      qmaAncillaDiagonal (fun a => (w a : ℂ)) := by
  rw [qmaAncillaDiagonal_eq]
  ext p q
  by_cases hpq : p = q
  · subst q
    simp [Matrix.conjTranspose_apply]
  · simp [Matrix.conjTranspose_apply,hpq,Ne.symm hpq]

omit [DecidableEq κ] in
theorem qmaAncillaOccupation_star (e : κ) :
    (qmaAncillaOccupation e).conjTranspose = qmaAncillaOccupation e := by
  ext a b
  by_cases hab : a = b
  · subst b
    by_cases ha : a e = 1 <;> simp [qmaAncillaOccupation,Matrix.conjTranspose_apply,ha]
  · simp [qmaAncillaOccupation,Matrix.conjTranspose_apply,hab,Ne.symm hab]

omit [Fintype σ] [DecidableEq σ] in
theorem qmaMediatorPerturbation_star (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (hC : C.conjTranspose = C) (hD : ∀ e, (D e).conjTranspose = D e)
    (hV : ∀ e, (V e).conjTranspose = V e) :
    (qmaMediatorPerturbation C D V).conjTranspose = qmaMediatorPerturbation C D V := by
  simp only [qmaMediatorPerturbation,qmaMediatorOccupations,qmaMediatorFlips,
    Matrix.conjTranspose_add,Matrix.conjTranspose_sum,Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one,qmaAncillaOccupation_star,qmaBitFlipMatrix_star,hC,hD,hV]

omit [Fintype σ] in
theorem qmaPhysicalMediator_star (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (hC : C.conjTranspose = C) (hD : ∀ e, (D e).conjTranspose = D e)
    (hV : ∀ e, (V e).conjTranspose = V e) :
    (qmaPhysicalMediatorMatrix g C D V).conjTranspose = qmaPhysicalMediatorMatrix g C D V := by
  rw [qmaPhysicalMediatorMatrix,Matrix.conjTranspose_add,qmaPhysicalPenaltyMatrix,
    qmaAncillaDiagonal_real_star,qmaMediatorPerturbation_star C D V hC hD hV]

end ContinuumCoulomb

end

end OAI
