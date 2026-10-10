import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitPhaseLocal
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorPhysical

namespace OAI

/-! Independent mediator phase rotations preserve the full physical spectrum. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

def qmaPhaseLift (m : κ → Bool) : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  (1 : Matrix σ σ ℂ) ⊗ₖ qmaPhaseMatrix m

theorem qmaPhaseLift_gram (m : κ → Bool) :
    (qmaPhaseLift (σ := σ) m).conjTranspose*qmaPhaseLift m = 1 := by
  unfold qmaPhaseLift
  rw [Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one,one_mul,qmaPhaseMatrix_gram,Matrix.one_kronecker_one]

theorem qmaPhaseLift_cogram (m : κ → Bool) :
    qmaPhaseLift (σ := σ) m*(qmaPhaseLift m).conjTranspose = 1 := by
  unfold qmaPhaseLift
  rw [Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one,one_mul,qmaPhaseMatrix_cogram,Matrix.one_kronecker_one]

theorem qmaPhaseLift_sandwich (m : κ → Bool) (M : Matrix σ σ ℂ)
    (N : Matrix (κ → Fin 2) (κ → Fin 2) ℂ) :
    (qmaPhaseLift m).conjTranspose*(M ⊗ₖ N)*qmaPhaseLift m =
      M ⊗ₖ ((qmaPhaseMatrix m).conjTranspose*N*qmaPhaseMatrix m) := by
  unfold qmaPhaseLift
  rw [Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one,one_mul,mul_one]

theorem qmaPhaseLift_diagonal (m : κ → Bool) (M : Matrix σ σ ℂ)
    (d : (κ → Fin 2) → ℂ) :
    (qmaPhaseLift m).conjTranspose*(M ⊗ₖ Matrix.diagonal d)*qmaPhaseLift m = M ⊗ₖ Matrix.diagonal d := by
  rw [qmaPhaseLift_sandwich,qmaPhaseMatrix_diagonal]

theorem qmaPhaseLift_old (m : κ → Bool) (M : Matrix σ σ ℂ) :
    (qmaPhaseLift m).conjTranspose*(M ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ))*qmaPhaseLift m =
      M ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ) := by
  rw [qmaPhaseLift_sandwich,mul_one,qmaPhaseMatrix_gram]

theorem qmaPhaseLift_flip (m : κ → Bool) (M : Matrix σ σ ℂ) (e : κ) :
    (qmaPhaseLift m).conjTranspose*(M ⊗ₖ qmaBitFlipMatrix e)*qmaPhaseLift m =
      M ⊗ₖ qmaPolarizedFlip m e := by
  rw [qmaPhaseLift_sandwich,qmaPhaseMatrix_flip]

def qmaPolarizedPhysical (g : ℝ) (L : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (m : κ → Bool) : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  qmaPhysicalPenaltyMatrix g+(L ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ)+
    qmaMediatorOccupations D+∑ e, V e ⊗ₖ qmaPolarizedFlip m e)

theorem qmaPhaseLift_physical (g : ℝ) (L : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (m : κ → Bool) :
    (qmaPhaseLift m).conjTranspose*qmaPhysicalMediatorMatrix g L D V*qmaPhaseLift m =
      qmaPolarizedPhysical g L D V m := by
  have hpen : (qmaPhaseLift m).conjTranspose*qmaPhysicalPenaltyMatrix (σ := σ) g*qmaPhaseLift m =
      qmaPhysicalPenaltyMatrix g := qmaPhaseLift_diagonal m 1 _
  have hocc (e : κ) :
      (qmaPhaseLift m).conjTranspose*(D e ⊗ₖ qmaAncillaOccupation e)*qmaPhaseLift m =
        D e ⊗ₖ qmaAncillaOccupation e := qmaPhaseLift_diagonal m (D e) _
  unfold qmaPhysicalMediatorMatrix qmaMediatorPerturbation qmaMediatorOccupations qmaMediatorFlips
    qmaPolarizedPhysical
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_sum,Matrix.sum_mul,
    hpen,hocc,qmaPhaseLift_old,qmaPhaseLift_flip]
  rfl

theorem qmaPolarizedPhysical_bottom (g : ℝ) (L : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (m : κ → Bool) :
    MediatorGraph.normalizedBottom (qmaPolarizedPhysical g L D V m) =
      MediatorGraph.normalizedBottom (qmaPhysicalMediatorMatrix g L D V) := by
  rw [← qmaPhaseLift_physical]
  exact qmaNormalizedBottom_unitary (qmaPhaseLift m) (qmaPhysicalMediatorMatrix g L D V)
    (qmaPhaseLift_gram m) (qmaPhaseLift_cogram m)

end ContinuumCoulomb

end

end OAI
