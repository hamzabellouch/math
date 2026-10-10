import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitThirdPhased

namespace OAI

/-! The seven phase-corrected terms are real Hermitian two-local matrices. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {σ : Type*} [Fintype σ]

theorem QMAEntryParity.mul_same {p : Bool} {M N : Matrix σ σ ℂ}
    (hM : QMAEntryParity p M) (hN : QMAEntryParity p N) : QMAEntryParity false (M*N) := by
  intro s t
  change Complex.imAddGroupHom (∑ i, M s i*N i t) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  cases p <;> simp only [QMAEntryParity,Bool.false_eq_true,ite_false,ite_true] at hM hN
  · change (M s i*N i t).im = 0
    simp only [Complex.mul_im,hM s i,hN i t,mul_zero,zero_mul,add_zero]
  · change (M s i*N i t).im = 0
    simp only [Complex.mul_im,hM s i,hN i t,mul_zero,zero_mul,add_zero]

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem qmaThirdPhasedLocalPiece_two_local (A B C : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (e : κ) (R j : ℝ) (m : κ → Bool) {SA SB SC : Finset ι}
    (hA : QMALocalOn SA A) (hB : QMALocalOn SB B) (hC : QMALocalOn SC C)
    (hSA : SA.card ≤ 1) (hSB : SB.card ≤ 1) (hSC : SC.card ≤ 1) (k : Fin 7) :
    ∃ U : Finset (ι ⊕ κ), U.card ≤ 2 ∧ QMALocalOn U (qmaThirdPhasedLocalPiece A B C e R j m k) := by
  rw [qmaThirdPhasedLocalPiece_eq]
  have hOcc := qmaOccupation_local e
  have hFlip := qmaPolarizedFlip_local m e
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

theorem qmaThirdPhasedLocalPiece_real (A B C : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (e : κ) (R j : ℝ) (m : κ → Bool)
    (hA : QMAEntryParity (m e) A) (hB : QMAEntryParity (m e) B)
    (hC : QMAEntryParity false C) (k : Fin 7) :
    QMAEntryParity false (qmaThirdPhasedLocalPiece A B C e R j m k) := by
  rw [qmaThirdPhasedLocalPiece_eq]
  fin_cases k
  · exact (qmaJoinMatrix_real qmaIdentity_real (qmaOccupation_real e)).real_smul (R^3)
  · exact qmaIdentity_real.real_smul (R*(1+(j/2)^2))
  · exact (qmaJoinMatrix_real (hA.mul_same hB) qmaIdentity_real).real_smul (R*j)
  · exact (qmaJoinMatrix_real hC qmaIdentity_real).real_smul (-(1+(j/2)^2))
  · exact (qmaJoinMatrix_real hC (qmaOccupation_real e)).real_smul (R^2)
  · exact (qmaPolarizedJoin_real A m e hA).real_smul (R^2)
  · exact (qmaPolarizedJoin_real B m e hB).real_smul (R^2*j/2)

theorem qmaThirdPhasedLocalPiece_star (A B C : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (e : κ) (R j : ℝ) (m : κ → Bool)
    (hA : A.conjTranspose = A) (hB : B.conjTranspose = B) (hC : C.conjTranspose = C)
    (hAB : A*B = B*A) (k : Fin 7) :
    (qmaThirdPhasedLocalPiece A B C e R j m k).conjTranspose =
      qmaThirdPhasedLocalPiece A B C e R j m k := by
  have hab : (A*B).conjTranspose = A*B := by rw [Matrix.conjTranspose_mul,hA,hB,hAB]
  rw [qmaThirdPhasedLocalPiece_eq]
  fin_cases k
  · exact qmaMatrix_real_smul_star _ _ (qmaJoinMatrix_star _ _
      Matrix.conjTranspose_one (qmaAncillaOccupation_star e))
  · exact qmaMatrix_real_smul_star _ _ Matrix.conjTranspose_one
  · exact qmaMatrix_real_smul_star _ _ (qmaJoinMatrix_star _ _ hab Matrix.conjTranspose_one)
  · exact qmaMatrix_real_smul_star _ _ (qmaJoinMatrix_star _ _ hC Matrix.conjTranspose_one)
  · exact qmaMatrix_real_smul_star _ _ (qmaJoinMatrix_star _ _ hC (qmaAncillaOccupation_star e))
  · exact qmaMatrix_real_smul_star _ _ (qmaJoinMatrix_star _ _ hA (qmaPolarizedFlip_star m e))
  · exact qmaMatrix_real_smul_star _ _ (qmaJoinMatrix_star _ _ hB (qmaPolarizedFlip_star m e))

end ContinuumCoulomb

end

end OAI
