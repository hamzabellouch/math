import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTripleSupported
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitThirdEnvelope

namespace OAI

/-! The actual phase-corrected third-order gadget reduces real three-local
Pauli families to real two-local families with inverse-polynomial error. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem qmaPauliThird_supported (w : κ → ι → Fin 4) (J : κ → ℝ)
    (hw : ∀ e, (qmaPauliSupport (w e)).card ≤ 3)
    (hEven : ∀ e, Even (qmaPauliYCount (w e))) {N : ℝ} (hN : 1 ≤ N) :
    ∃ G : (κ × Fin 7) → Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ,
      (∀ p, (G p).IsHermitian) ∧ (∀ p, QMAEntryParity false (G p)) ∧
      (∀ p, ∃ S : Finset (ι ⊕ κ), S.card ≤ 2 ∧ QMALocalOn S (G p) ∧
        S ⊆ qmaMediatorSupport (qmaPauliSupport (w p.1)) p.1) ∧
      |MediatorGraph.normalizedBottom (∑ p, G p)-
        MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • qmaPauliWord (w e))| ≤ 1/N := by
  choose a b c hsa hsb hsc ha hb hc habc hab hac hbc hpar hce using
    fun e => qmaPauliWord_triple_supported (w e) (hw e) (hEven e)
  let A := fun e => qmaPauliWord (a e)
  let B := fun e => qmaPauliWord (b e)
  let C := fun e => qmaPauliWord (c e)
  let m := fun e => decide (Odd (qmaPauliYCount (a e)))
  let R := 8*(qmaThirdBudget 0 J)^4*N
  let G := fun p : κ × Fin 7 => qmaThirdPhasedLocalPiece (A p.1) (B p.1) (C p.1) p.1 R (J p.1) m p.2
  have hAst (e : κ) : (A e).conjTranspose = A e := qmaPauliWord_hermitian _
  have hBst (e : κ) : (B e).conjTranspose = B e := qmaPauliWord_hermitian _
  have hCst (e : κ) : (C e).conjTranspose = C e := qmaPauliWord_hermitian _
  have hAr (e : κ) : QMAEntryParity (m e) (A e) := qmaPauliWord_entryParity _
  have hBr (e : κ) : QMAEntryParity (m e) (B e) := by
    dsimp only [m,B]
    rw [hpar e]
    exact qmaPauliWord_entryParity _
  have hCr (e : κ) : QMAEntryParity false (C e) := qmaPauliWord_real_of_even _ (hce e)
  refine ⟨G,?_,?_,?_,?_⟩
  · intro p
    exact qmaThirdPhasedLocalPiece_star _ _ _ _ _ _ _ (hAst p.1) (hBst p.1) (hCst p.1) (hab p.1) p.2
  · intro p
    exact qmaThirdPhasedLocalPiece_real _ _ _ _ _ _ _ (hAr p.1) (hBr p.1) (hCr p.1) p.2
  · intro p
    refine ⟨qmaThirdPieceSites (qmaPauliSupport (a p.1)) (qmaPauliSupport (b p.1))
      (qmaPauliSupport (c p.1)) p.1 p.2,
      qmaThirdPieceSites_card (ha p.1) (hb p.1) (hc p.1) _ _,
      qmaThirdPieceSites_local _ _ _ _ _ _ _ (qmaPauliWord_support (a p.1))
        (qmaPauliWord_support (b p.1)) (qmaPauliWord_support (c p.1)) p.2,
      qmaThirdPieceSites_subset (hsa p.1) (hsb p.1) (hsc p.1) _ _⟩
  · have hsum : (∑ p, G p) = (qmaThirdPhased 0 A B C R J m).submatrix
        (Equiv.sumArrowEquivProdArrow ι κ (Fin 2)) (Equiv.sumArrowEquivProdArrow ι κ (Fin 2)) := by
      rw [qmaThirdPhased_decomposition]
      simp only [Matrix.zero_kronecker,zero_add,MediatorGraph.submatrix_sum,
        Fintype.sum_prod_type,G,qmaThirdPhasedLocalPiece]
    have htarget : qmaThirdSeriesTarget 0 A B C (fun e => (J e:ℂ)) =
        ∑ e, (J e:ℂ) • qmaPauliWord (w e) := by
      simp only [qmaThirdSeriesTarget,zero_add,A,B,C,habc]
    rw [hsum,MediatorGraph.normalizedBottom_reindex,qmaThirdPhased_bottom,← htarget]
    apply qmaThirdGadget_polynomial_accuracy 0 A B C J (by norm_num) hN
      Matrix.conjTranspose_zero (by simp) hAst hBst hCst
      (fun e => qmaPauliWord_square _) (fun e => qmaPauliWord_square _) (fun e => qmaPauliWord_square _)
      hab hac hbc (EuclideanSpace.single (fun _ : ι => (0 : Fin 2)) (1:ℂ))
    simp [PiLp.norm_single]

end ContinuumCoulomb

end

end OAI
