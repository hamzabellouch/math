import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitThirdDecomposition
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalJoin

namespace OAI

/-! Every explicit third-order term acts on at most two qubits when its
three input factors each act on a single old qubit. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem qmaLocal_identity (S : Finset ι) : QMALocalOn S (1 : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) :=
  ⟨1,(qmaLocalLift_one S).symm⟩

theorem QMALocalOn.real_smul {S : Finset ι} {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ}
    (hA : QMALocalOn S A) (r : ℝ) : QMALocalOn S (r • A) := hA.smul (r:ℂ)

theorem qmaOccupation_local (e : κ) : QMALocalOn {e} (qmaAncillaOccupation e) := by
  apply qmaLocalOn_diagonal
  intro s t h
  rw [h e (Finset.mem_singleton_self e)]

def qmaThirdLocalPiece (A B C : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (e : κ) (R j : ℝ) :
    Fin 7 → Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ :=
  ![(R^3:ℝ) • qmaJoinMatrix (1 : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (qmaAncillaOccupation e),
    (R*(1+(j/2)^2):ℝ) • (1 : Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ),
    (R*j:ℝ) • qmaJoinMatrix (A*B) (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ),
    (-(1+(j/2)^2):ℝ) • qmaJoinMatrix C (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ),
    (R^2:ℝ) • qmaJoinMatrix C (qmaAncillaOccupation e),
    (R^2:ℝ) • qmaJoinMatrix A (qmaBitFlipMatrix e),
    (R^2*j/2:ℝ) • qmaJoinMatrix B (qmaBitFlipMatrix e)]

theorem qmaThirdPiece_reindex (A B C : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (e : κ) (R j : ℝ) (k : Fin 7) :
    (qmaThirdPiece A B C e R j k).submatrix (Equiv.sumArrowEquivProdArrow ι κ (Fin 2))
      (Equiv.sumArrowEquivProdArrow ι κ (Fin 2)) = qmaThirdLocalPiece A B C e R j k := by
  fin_cases k <;> simp [qmaThirdPiece,qmaThirdLocalPiece,qmaJoinMatrix,
    Matrix.submatrix_smul,Matrix.submatrix_one_equiv]

theorem qmaThirdLocalPiece_two_local (A B C : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (e : κ) (R j : ℝ) {SA SB SC : Finset ι}
    (hA : QMALocalOn SA A) (hB : QMALocalOn SB B) (hC : QMALocalOn SC C)
    (hSA : SA.card ≤ 1) (hSB : SB.card ≤ 1) (hSC : SC.card ≤ 1) (k : Fin 7) :
    ∃ U : Finset (ι ⊕ κ), U.card ≤ 2 ∧ QMALocalOn U (qmaThirdLocalPiece A B C e R j k) := by
  have hOcc := qmaOccupation_local e
  have hFlip := qmaBitFlipMatrix_local e
  have hsingle : ({e} : Finset κ).card ≤ 1 := by simp
  fin_cases k
  · obtain ⟨U,hU,hM⟩ := qmaJoin_two_local (qmaLocal_identity (∅ : Finset ι)) hOcc (by simp) hsingle
    exact ⟨U,hU,hM.real_smul (R^3)⟩
  · exact ⟨∅,by simp,(qmaLocal_identity (∅ : Finset (ι ⊕ κ))).real_smul (R*(1+(j/2)^2))⟩
  · have hAB := (hA.mono Finset.subset_union_left).mul (hB.mono Finset.subset_union_right)
    refine ⟨(SA ∪ SB).map (Function.Embedding.inl : ι ↪ ι ⊕ κ),?_,hAB.joinLeft.real_smul (R*j)⟩
    rw [Finset.card_map]
    exact (Finset.card_union_le SA SB).trans (by omega)
  · refine ⟨SC.map (Function.Embedding.inl : ι ↪ ι ⊕ κ),?_,hC.joinLeft.real_smul (-(1+(j/2)^2))⟩
    simpa only [Finset.card_map] using hSC.trans (by norm_num : (1:ℕ) ≤ 2)
  · obtain ⟨U,hU,hM⟩ := qmaJoin_two_local hC hOcc hSC hsingle
    exact ⟨U,hU,hM.real_smul (R^2)⟩
  · obtain ⟨U,hU,hM⟩ := qmaJoin_two_local hA hFlip hSA hsingle
    exact ⟨U,hU,hM.real_smul (R^2)⟩
  · obtain ⟨U,hU,hM⟩ := qmaJoin_two_local hB hFlip hSB hsingle
    exact ⟨U,hU,hM.real_smul (R^2*j/2)⟩

end ContinuumCoulomb

end

end OAI
