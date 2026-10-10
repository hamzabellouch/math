import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitThirdGadget

namespace OAI

/-! The physical gadget is a sum of seven explicit terms per mediator. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

theorem qmaFinTwo_cast (a : Fin 2) : (a.val : ℂ) = if a = 1 then 1 else 0 := by
  fin_cases a <;> norm_num

omit [Fintype σ] [DecidableEq κ] in
theorem qmaPhysicalPenalty_sum (g : ℝ) : qmaPhysicalPenaltyMatrix (σ := σ) (κ := κ) g =
    ∑ e, (g:ℂ) • ((1 : Matrix σ σ ℂ) ⊗ₖ qmaAncillaOccupation e) := by
  ext p q
  rcases p with ⟨s,a⟩
  rcases q with ⟨t,b⟩
  simp only [qmaPhysicalPenaltyMatrix,qmaAncillaDiagonal,Matrix.kronecker_apply,
    qmaAncillaOccupation,Matrix.diagonal_apply,Matrix.one_apply,Matrix.sum_apply,
    Matrix.smul_apply,smul_eq_mul]
  by_cases hst : s = t <;> by_cases hab : a = b
  · subst t
    subst b
    simp only [ite_true,one_mul,qmaAncillaNumber,Nat.cast_sum]
    push_cast
    rw [Finset.mul_sum]
    simp only [qmaFinTwo_cast]
  · simp [hst,hab]
  · simp [hst,hab]
  · simp [hst,hab]

def qmaThirdPiece (A B C : Matrix σ σ ℂ) (e : κ) (R j : ℝ) :
    Fin 7 → Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  ![(R^3:ℝ) • ((1 : Matrix σ σ ℂ) ⊗ₖ qmaAncillaOccupation e),
    (R*(1+(j/2)^2):ℝ) • (1 : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ),
    (R*j:ℝ) • ((A*B) ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ)),
    (-(1+(j/2)^2):ℝ) • (C ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ)),
    (R^2:ℝ) • (C ⊗ₖ qmaAncillaOccupation e),
    (R^2:ℝ) • (A ⊗ₖ qmaBitFlipMatrix e),
    (R^2*j/2:ℝ) • (B ⊗ₖ qmaBitFlipMatrix e)]

theorem qmaThirdPiece_sum (A B C : Matrix σ σ ℂ) (e : κ) (R j : ℝ) :
    (∑ k, qmaThirdPiece A B C e R j k) =
      (R^3:ℝ) • ((1 : Matrix σ σ ℂ) ⊗ₖ qmaAncillaOccupation e)+
      qmaThirdSeriesCounter A B C R j ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ)+
      ((R^2:ℝ) • C) ⊗ₖ qmaAncillaOccupation e+
      ((R^2:ℝ) • qmaThirdSeriesPair A B j) ⊗ₖ qmaBitFlipMatrix e := by
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
  simp only [qmaThirdPiece,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,
    qmaThirdSeriesCounter,qmaThirdSeriesPair,
    hr,hp,Matrix.add_kronecker,hk,Matrix.smul_kronecker,
    Matrix.one_kronecker_one,smul_add,smul_smul]
  push_cast
  module

theorem qmaThirdGadget_decomposition (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (R : ℝ) (J : κ → ℝ) :
    qmaThirdGadget H A B C R J =
      H ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ)+
        ∑ e, ∑ k, qmaThirdPiece (A e) (B e) (C e) e R (J e) k := by
  simp only [qmaThirdGadget,qmaPhysicalMediatorMatrix,qmaMediatorPerturbation,
    qmaMediatorOccupations,qmaMediatorFlips,qmaThirdSeriesLow,qmaPhysicalPenalty_sum,
    Matrix.add_kronecker,MediatorGraph.sum_kronecker,qmaThirdPiece_sum,
    Finset.sum_add_distrib]
  have hs (r : ℝ) (M : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ) :
      r • M = (r:ℂ) • M := rfl
  simp only [hs]
  abel

end ContinuumCoulomb

end

end OAI
