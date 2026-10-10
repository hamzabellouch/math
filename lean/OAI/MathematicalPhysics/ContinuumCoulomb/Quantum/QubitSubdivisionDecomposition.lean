import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitSubdivisionGadget
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitThirdDecomposition
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitPhasePhysical

namespace OAI

/-! An exact four-term output family for a phase-rotated subdivision gadget. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

def qmaSubdivisionPolarized (H : Matrix σ σ ℂ) (A B : κ → Matrix σ σ ℂ)
    (R : ℝ) (J : κ → ℝ) (m : κ → Bool) :
    Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  qmaPolarizedPhysical (R^2) (qmaSubdivisionLow H (fun e => J e)) (fun _ => 0)
    (fun e => (R:ℝ) • qmaThirdSeriesPair (A e) (B e) (-J e)) m

def qmaSubdivisionPiece (A B : Matrix σ σ ℂ) (e : κ) (R j : ℝ) (m : κ → Bool) :
    Fin 4 → Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  ![(R^2:ℝ) • ((1 : Matrix σ σ ℂ) ⊗ₖ qmaAncillaOccupation e),
    (1+(j/2)^2:ℝ) • (1 : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ),
    (R:ℝ) • (A ⊗ₖ qmaPolarizedFlip m e),
    (-R*j/2:ℝ) • (B ⊗ₖ qmaPolarizedFlip m e)]

omit [Fintype σ] in
theorem qmaSubdivisionPiece_sum (A B : Matrix σ σ ℂ) (e : κ) (R j : ℝ) (m : κ → Bool) :
    (∑ k, qmaSubdivisionPiece A B e R j m k) =
      (R^2:ℝ) • ((1 : Matrix σ σ ℂ) ⊗ₖ qmaAncillaOccupation e)+
      qmaSubdivisionCounter (j:ℂ) ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ)+
      ((R:ℝ) • qmaThirdSeriesPair A B (-j)) ⊗ₖ qmaPolarizedFlip m e := by
  have hr (r : ℝ) (M : Matrix σ σ ℂ) : r • M = (r:ℂ) • M := rfl
  have hp (r : ℝ) (M : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ) :
      r • M = (r:ℂ) • M := rfl
  simp only [qmaSubdivisionPiece,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,qmaSubdivisionCounter,qmaThirdSeriesPair,
    hr,hp,Matrix.add_kronecker,Matrix.smul_kronecker,Matrix.one_kronecker_one,
    smul_add,smul_smul]
  push_cast
  module

omit [Fintype σ] in
theorem qmaSubdivisionPolarized_decomposition (H : Matrix σ σ ℂ) (A B : κ → Matrix σ σ ℂ)
    (R : ℝ) (J : κ → ℝ) (m : κ → Bool) :
    qmaSubdivisionPolarized H A B R J m =
      H ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ)+
        ∑ e, ∑ k, qmaSubdivisionPiece (A e) (B e) e R (J e) m k := by
  simp only [qmaSubdivisionPolarized,qmaPolarizedPhysical,qmaSubdivisionLow,
    qmaPhysicalPenalty_sum,qmaMediatorOccupations,qmaSubdivisionPiece_sum,
    Matrix.add_kronecker,MediatorGraph.sum_kronecker,Matrix.zero_kronecker,
    Finset.sum_const_zero,add_zero,Finset.sum_add_distrib]
  have hs (r : ℝ) (M : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ) :
      r • M = (r:ℂ) • M := rfl
  simp only [hs]
  abel

theorem qmaSubdivisionPolarized_bottom (H : Matrix σ σ ℂ) (A B : κ → Matrix σ σ ℂ)
    (R : ℝ) (J : κ → ℝ) (m : κ → Bool) :
    MediatorGraph.normalizedBottom (qmaSubdivisionPolarized H A B R J m) =
      MediatorGraph.normalizedBottom (qmaSubdivisionGadget H A B R J) :=
  qmaPolarizedPhysical_bottom _ _ _ _ _

end ContinuumCoulomb

end

end OAI
