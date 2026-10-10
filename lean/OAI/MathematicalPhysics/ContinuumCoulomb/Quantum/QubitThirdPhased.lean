import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitThirdLocalFamily
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitSubdivisionHermitian

namespace OAI

/-! The third-order family with the real-preserving mediator phases. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {σ ι κ : Type*} [Fintype σ] [DecidableEq σ]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def qmaThirdPhasedPiece (A B C : Matrix σ σ ℂ) (e : κ) (R j : ℝ) (m : κ → Bool) :
    Fin 7 → Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  ![(R^3:ℝ) • ((1 : Matrix σ σ ℂ) ⊗ₖ qmaAncillaOccupation e),
    (R*(1+(j/2)^2):ℝ) • (1 : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ),
    (R*j:ℝ) • ((A*B) ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ)),
    (-(1+(j/2)^2):ℝ) • (C ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ)),
    (R^2:ℝ) • (C ⊗ₖ qmaAncillaOccupation e),
    (R^2:ℝ) • (A ⊗ₖ qmaPolarizedFlip m e),
    (R^2*j/2:ℝ) • (B ⊗ₖ qmaPolarizedFlip m e)]

theorem qmaThirdPhasedPiece_sum (A B C : Matrix σ σ ℂ) (e : κ) (R j : ℝ) (m : κ → Bool) :
    (∑ k, qmaThirdPhasedPiece A B C e R j m k) =
      (R^3:ℝ) • ((1 : Matrix σ σ ℂ) ⊗ₖ qmaAncillaOccupation e)+
      qmaThirdSeriesCounter A B C R j ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ)+
      ((R^2:ℝ) • C) ⊗ₖ qmaAncillaOccupation e+
      ((R^2:ℝ) • qmaThirdSeriesPair A B j) ⊗ₖ qmaPolarizedFlip m e := by
  have hr (r : ℝ) (M : Matrix σ σ ℂ) : r • M = (r:ℂ) • M := rfl
  have hp (r : ℝ) (M : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ) :
      r • M = (r:ℂ) • M := rfl
  have hk (M N : Matrix σ σ ℂ) :
      (M-N) ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ) =
        M ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ)-
          N ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ) := by
    ext p q
    rcases p with ⟨s,a⟩
    rcases q with ⟨t,b⟩
    simp only [Matrix.kronecker_apply,Matrix.sub_apply,sub_mul]
  simp only [qmaThirdPhasedPiece,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,qmaThirdSeriesCounter,qmaThirdSeriesPair,
    hr,hp,Matrix.add_kronecker,hk,Matrix.smul_kronecker,Matrix.one_kronecker_one,
    smul_add,smul_smul]
  push_cast
  module

def qmaThirdPhased (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (R : ℝ) (J : κ → ℝ) (m : κ → Bool) :
    Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  qmaPolarizedPhysical (R^3) (qmaThirdSeriesLow H A B C R (fun e => J e))
    (fun e => (R^2:ℝ) • C e) (fun e => (R^2:ℝ) • qmaThirdSeriesPair (A e) (B e) (J e)) m

theorem qmaThirdPhased_decomposition (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (R : ℝ) (J : κ → ℝ) (m : κ → Bool) :
    qmaThirdPhased H A B C R J m =
      H ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ)+
        ∑ e, ∑ k, qmaThirdPhasedPiece (A e) (B e) (C e) e R (J e) m k := by
  simp only [qmaThirdPhased,qmaPolarizedPhysical,qmaMediatorOccupations,qmaThirdSeriesLow,
    qmaPhysicalPenalty_sum,Matrix.add_kronecker,MediatorGraph.sum_kronecker,
    qmaThirdPhasedPiece_sum,Finset.sum_add_distrib]
  have hs (r : ℝ) (M : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ) :
      r • M = (r:ℂ) • M := rfl
  simp only [hs]
  abel

theorem qmaThirdPhased_bottom (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (R : ℝ) (J : κ → ℝ) (m : κ → Bool) :
    MediatorGraph.normalizedBottom (qmaThirdPhased H A B C R J m) =
      MediatorGraph.normalizedBottom (qmaThirdGadget H A B C R J) :=
  qmaPolarizedPhysical_bottom _ _ _ _ _

def qmaThirdPhasedLocalPiece (A B C : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (e : κ) (R j : ℝ) (m : κ → Bool) (k : Fin 7) :
    Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ :=
  (qmaThirdPhasedPiece A B C e R j m k).submatrix
    (Equiv.sumArrowEquivProdArrow ι κ (Fin 2)) (Equiv.sumArrowEquivProdArrow ι κ (Fin 2))

theorem qmaThirdPhasedLocalPiece_eq (A B C : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (e : κ) (R j : ℝ) (m : κ → Bool) :
    qmaThirdPhasedLocalPiece A B C e R j m =
      ![(R^3:ℝ) • qmaJoinMatrix (1 : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (qmaAncillaOccupation e),
        (R*(1+(j/2)^2):ℝ) • (1 : Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ),
        (R*j:ℝ) • qmaJoinMatrix (A*B) (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ),
        (-(1+(j/2)^2):ℝ) • qmaJoinMatrix C (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ),
        (R^2:ℝ) • qmaJoinMatrix C (qmaAncillaOccupation e),
        (R^2:ℝ) • qmaJoinMatrix A (qmaPolarizedFlip m e),
        (R^2*j/2:ℝ) • qmaJoinMatrix B (qmaPolarizedFlip m e)] := by
  funext k
  fin_cases k <;> simp [qmaThirdPhasedLocalPiece,qmaThirdPhasedPiece,qmaJoinMatrix,
    Matrix.submatrix_smul,Matrix.submatrix_one_equiv]

end ContinuumCoulomb

end

end OAI
