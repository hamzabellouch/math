import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitThirdLocality

namespace OAI

/-! The actual output family has seven new two-local terms per mediator. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ι κ α : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype α]

def qmaThirdOnQubits (H : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (A B C : κ → Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (R : ℝ) (J : κ → ℝ) :
    Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ :=
  (qmaThirdGadget H A B C R J).submatrix (Equiv.sumArrowEquivProdArrow ι κ (Fin 2))
    (Equiv.sumArrowEquivProdArrow ι κ (Fin 2))

def qmaThirdLocalFamily (F : α → Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (A B C : κ → Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (R : ℝ) (J : κ → ℝ) :
    α ⊕ (κ × Fin 7) → Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ
  | .inl a => qmaJoinMatrix (F a) 1
  | .inr (e,k) => qmaThirdLocalPiece (A e) (B e) (C e) e R (J e) k

theorem qmaThirdLocalFamily_sum (F : α → Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (A B C : κ → Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (R : ℝ) (J : κ → ℝ) :
    (∑ a, qmaThirdLocalFamily F A B C R J a) = qmaThirdOnQubits (∑ a, F a) A B C R J := by
  unfold qmaThirdOnQubits
  rw [qmaThirdGadget_decomposition,MediatorGraph.submatrix_add_apply]
  simp only [MediatorGraph.submatrix_sum,qmaThirdPiece_reindex,MediatorGraph.sum_kronecker]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,qmaThirdLocalFamily,qmaJoinMatrix]

omit [DecidableEq κ] in
theorem qmaThirdLocalFamily_count : Fintype.card (α ⊕ (κ × Fin 7)) =
    Fintype.card α+7*Fintype.card κ := by
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  omega

omit [Fintype α] in
theorem qmaThirdLocalFamily_two_local (F : α → Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (A B C : κ → Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (R : ℝ) (J : κ → ℝ)
    (SF : α → Finset ι) (SA SB SC : κ → Finset ι)
    (hF : ∀ a, QMALocalOn (SF a) (F a)) (hSF : ∀ a, (SF a).card ≤ 2)
    (hA : ∀ e, QMALocalOn (SA e) (A e)) (hB : ∀ e, QMALocalOn (SB e) (B e))
    (hC : ∀ e, QMALocalOn (SC e) (C e))
    (hSA : ∀ e, (SA e).card ≤ 1) (hSB : ∀ e, (SB e).card ≤ 1) (hSC : ∀ e, (SC e).card ≤ 1)
    (a : α ⊕ (κ × Fin 7)) :
    ∃ U : Finset (ι ⊕ κ), U.card ≤ 2 ∧ QMALocalOn U (qmaThirdLocalFamily F A B C R J a) := by
  cases a with
  | inl a =>
    refine ⟨(SF a).map (Function.Embedding.inl : ι ↪ ι ⊕ κ),?_,(hF a).joinLeft⟩
    simpa only [Finset.card_map] using hSF a
  | inr p =>
    exact qmaThirdLocalPiece_two_local (A p.1) (B p.1) (C p.1) p.1 R (J p.1)
      (hA p.1) (hB p.1) (hC p.1) (hSA p.1) (hSB p.1) (hSC p.1) p.2

theorem qmaThirdOnQubits_bottom (H : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (A B C : κ → Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (R : ℝ) (J : κ → ℝ) :
    MediatorGraph.normalizedBottom (qmaThirdOnQubits H A B C R J) =
      MediatorGraph.normalizedBottom (qmaThirdGadget H A B C R J) :=
  MediatorGraph.normalizedBottom_reindex (Equiv.sumArrowEquivProdArrow ι κ (Fin 2)) _

end ContinuumCoulomb

end

end OAI
