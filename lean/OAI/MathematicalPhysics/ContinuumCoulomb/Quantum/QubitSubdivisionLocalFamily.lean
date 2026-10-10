import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitSubdivisionDecomposition
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitThirdLocality

namespace OAI

/-! Subdivision increases each factor's support by at most its one fresh mediator. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ι κ α : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype α]

def qmaSubdivisionLocalPiece (A B : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (e : κ) (R j : ℝ) (m : κ → Bool) :
    Fin 4 → Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ :=
  ![(R^2:ℝ) • qmaJoinMatrix (1 : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (qmaAncillaOccupation e),
    (1+(j/2)^2:ℝ) • (1 : Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ),
    (R:ℝ) • qmaJoinMatrix A (qmaPolarizedFlip m e),
    (-R*j/2:ℝ) • qmaJoinMatrix B (qmaPolarizedFlip m e)]

omit [DecidableEq ι] in
theorem qmaSubdivisionPiece_reindex (A B : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (e : κ) (R j : ℝ) (m : κ → Bool) (k : Fin 4) :
    (qmaSubdivisionPiece A B e R j m k).submatrix (Equiv.sumArrowEquivProdArrow ι κ (Fin 2))
      (Equiv.sumArrowEquivProdArrow ι κ (Fin 2)) = qmaSubdivisionLocalPiece A B e R j m k := by
  fin_cases k <;> simp [qmaSubdivisionPiece,qmaSubdivisionLocalPiece,qmaJoinMatrix,
    Matrix.submatrix_smul,Matrix.submatrix_one_equiv]

def qmaSubdivisionOnQubits (H : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (A B : κ → Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (R : ℝ) (J : κ → ℝ) (m : κ → Bool) :
    Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ :=
  (qmaSubdivisionPolarized H A B R J m).submatrix (Equiv.sumArrowEquivProdArrow ι κ (Fin 2))
    (Equiv.sumArrowEquivProdArrow ι κ (Fin 2))

def qmaSubdivisionLocalFamily (F : α → Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (A B : κ → Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (R : ℝ) (J : κ → ℝ) (m : κ → Bool) :
    α ⊕ (κ × Fin 4) → Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ
  | .inl a => qmaJoinMatrix (F a) 1
  | .inr (e,k) => qmaSubdivisionLocalPiece (A e) (B e) e R (J e) m k

omit [DecidableEq ι] in
theorem qmaSubdivisionLocalFamily_sum (F : α → Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (A B : κ → Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (R : ℝ) (J : κ → ℝ) (m : κ → Bool) :
    (∑ a, qmaSubdivisionLocalFamily F A B R J m a) = qmaSubdivisionOnQubits (∑ a, F a) A B R J m := by
  unfold qmaSubdivisionOnQubits
  rw [qmaSubdivisionPolarized_decomposition,MediatorGraph.submatrix_add_apply]
  simp only [MediatorGraph.submatrix_sum,qmaSubdivisionPiece_reindex,MediatorGraph.sum_kronecker]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,qmaSubdivisionLocalFamily,qmaJoinMatrix]

omit [DecidableEq κ] in
theorem qmaSubdivisionLocalFamily_count : Fintype.card (α ⊕ (κ × Fin 4)) =
    Fintype.card α+4*Fintype.card κ := by
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  omega

omit [Fintype α] in
theorem qmaSubdivisionLocalPiece_local (A B : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (e : κ) (R j : ℝ) (m : κ → Bool) {SA SB : Finset ι} {d : ℕ}
    (hA : QMALocalOn SA A) (hB : QMALocalOn SB B)
    (hSA : SA.card ≤ d) (hSB : SB.card ≤ d) (k : Fin 4) :
    ∃ U : Finset (ι ⊕ κ), U.card ≤ d+1 ∧ QMALocalOn U (qmaSubdivisionLocalPiece A B e R j m k) := by
  have hjoin {S : Finset ι} {T : Finset κ}
      {M : Matrix (ι → Fin 2) (ι → Fin 2) ℂ} {N : Matrix (κ → Fin 2) (κ → Fin 2) ℂ}
      (hM : QMALocalOn S M) (hN : QMALocalOn T N) (hS : S.card ≤ d) (hT : T.card ≤ 1) :
      ∃ U : Finset (ι ⊕ κ), U.card ≤ d+1 ∧ QMALocalOn U (qmaJoinMatrix M N) := by
    refine ⟨_,?_,hM.join hN⟩
    have hc := Finset.card_union_le (S.map (Function.Embedding.inl : ι ↪ ι ⊕ κ))
      (T.map (Function.Embedding.inr : κ ↪ ι ⊕ κ))
    simp only [Finset.card_map] at hc
    omega
  fin_cases k
  · obtain ⟨U,hU,hM⟩ := hjoin (qmaLocal_identity (∅ : Finset ι))
      (qmaOccupation_local e) (by simp) (by simp)
    exact ⟨U,hU,hM.real_smul (R^2)⟩
  · exact ⟨∅,by simp,(qmaLocal_identity (∅ : Finset (ι ⊕ κ))).real_smul (1+(j/2)^2)⟩
  · obtain ⟨U,hU,hM⟩ := hjoin hA (qmaPolarizedFlip_local m e) hSA (by simp)
    exact ⟨U,hU,hM.real_smul R⟩
  · obtain ⟨U,hU,hM⟩ := hjoin hB (qmaPolarizedFlip_local m e) hSB (by simp)
    exact ⟨U,hU,hM.real_smul (-R*j/2)⟩

omit [Fintype α] in
theorem qmaSubdivisionLocalFamily_local (F : α → Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (A B : κ → Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (R : ℝ) (J : κ → ℝ) (m : κ → Bool)
    (SF : α → Finset ι) (SA SB : κ → Finset ι) {d : ℕ}
    (hF : ∀ a, QMALocalOn (SF a) (F a)) (hSF : ∀ a, (SF a).card ≤ d+1)
    (hA : ∀ e, QMALocalOn (SA e) (A e)) (hB : ∀ e, QMALocalOn (SB e) (B e))
    (hSA : ∀ e, (SA e).card ≤ d) (hSB : ∀ e, (SB e).card ≤ d)
    (a : α ⊕ (κ × Fin 4)) :
    ∃ U : Finset (ι ⊕ κ), U.card ≤ d+1 ∧ QMALocalOn U (qmaSubdivisionLocalFamily F A B R J m a) := by
  cases a with
  | inl a =>
    refine ⟨(SF a).map (Function.Embedding.inl : ι ↪ ι ⊕ κ),?_,(hF a).joinLeft⟩
    simpa only [Finset.card_map] using hSF a
  | inr p =>
    exact qmaSubdivisionLocalPiece_local (A p.1) (B p.1) p.1 R (J p.1) m
      (hA p.1) (hB p.1) (hSA p.1) (hSB p.1) p.2

theorem qmaSubdivisionOnQubits_bottom (H : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (A B : κ → Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (R : ℝ) (J : κ → ℝ) (m : κ → Bool) :
    MediatorGraph.normalizedBottom (qmaSubdivisionOnQubits H A B R J m) =
      MediatorGraph.normalizedBottom (qmaSubdivisionGadget H A B R J) := by
  rw [qmaSubdivisionOnQubits,MediatorGraph.normalizedBottom_reindex,qmaSubdivisionPolarized_bottom]

end ContinuumCoulomb

end

end OAI
