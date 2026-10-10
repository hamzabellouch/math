import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitSubdivisionHermitian

namespace OAI

/-! A simultaneous real subdivision step for bounded-support even-Y words. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem qmaPauliSubdivision_exists (w : κ → ι → Fin 4) (J : κ → ℝ) {d : ℕ}
    (hw : ∀ e, (qmaPauliSupport (w e)).card ≤ 2*d)
    (hEven : ∀ e, Even (qmaPauliYCount (w e))) {N : ℝ} (hN : 1 ≤ N) :
    ∃ G : (κ × Fin 4) → Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ,
      (∀ p, (G p).IsHermitian) ∧ (∀ p, QMAEntryParity false (G p)) ∧
      (∀ p, ∃ S : Finset (ι ⊕ κ), S.card ≤ d+1 ∧ QMALocalOn S (G p)) ∧
      |MediatorGraph.normalizedBottom (∑ p, G p)-
        MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • qmaPauliWord (w e))| ≤ 1/N := by
  choose L T hL hT hdis hcover using fun e => qmaBalancedSupport (qmaPauliSupport (w e)) d (hw e)
  let A := fun e => qmaPauliWord (qmaPauliRestrict (L e) (w e))
  let B := fun e => qmaPauliWord (qmaPauliRestrict (T e) (w e))
  let m := fun e => decide (Odd (qmaPauliYCount (qmaPauliRestrict (L e) (w e))))
  let R := 8*(qmaThirdBudget 0 J)^4*N
  let G := fun p : κ × Fin 4 => qmaSubdivisionLocalPiece (A p.1) (B p.1) p.1 R (J p.1) m p.2
  have hcover' (e : κ) : qmaPauliSupport (w e) ⊆ L e ∪ T e := by rw [hcover e]
  have hAst (e : κ) : (A e).conjTranspose = A e := qmaPauliWord_hermitian _
  have hBst (e : κ) : (B e).conjTranspose = B e := qmaPauliWord_hermitian _
  have hAr (e : κ) : QMAEntryParity (m e) (A e) := qmaPauliWord_entryParity _
  have hBr (e : κ) : QMAEntryParity (m e) (B e) := by
    dsimp only [m,B]
    rw [qmaPauliRestrict_same_parity (L e) (T e) (w e) (hdis e) (hcover' e) (hEven e)]
    exact qmaPauliWord_entryParity _
  have hAB (e : κ) : A e*B e = B e*A e := qmaPauliRestrict_commute _ _ _ (hdis e)
  have hfactor (e : κ) : A e*B e = qmaPauliWord (w e) :=
    qmaPauliRestrict_factor _ _ _ (hdis e) (hcover' e)
  have hAl (e : κ) : QMALocalOn (L e) (A e) :=
    (qmaPauliWord_support _).mono (qmaPauliRestrict_support _ _)
  have hBl (e : κ) : QMALocalOn (T e) (B e) :=
    (qmaPauliWord_support _).mono (qmaPauliRestrict_support _ _)
  refine ⟨G,?_,?_,?_,?_⟩
  · intro p
    exact qmaSubdivisionLocalPiece_star _ _ _ _ _ _ (hAst p.1) (hBst p.1) p.2
  · intro p
    exact qmaSubdivisionLocalPiece_real _ _ _ _ _ _ (hAr p.1) (hBr p.1) p.2
  · intro p
    exact qmaSubdivisionLocalPiece_local _ _ _ _ _ _ (hAl p.1) (hBl p.1) (hL p.1) (hT p.1) p.2
  · have hsum : (∑ p, G p) = qmaSubdivisionOnQubits 0 A B R J m := by
      unfold qmaSubdivisionOnQubits
      rw [qmaSubdivisionPolarized_decomposition]
      simp only [Matrix.zero_kronecker,zero_add,MediatorGraph.submatrix_sum,
        qmaSubdivisionPiece_reindex,Fintype.sum_prod_type,G]
    have htarget : qmaSubdivisionTarget 0 A B (fun e => (J e:ℂ)) =
        ∑ e, (J e:ℂ) • qmaPauliWord (w e) := by
      simp only [qmaSubdivisionTarget,zero_add,hfactor]
    rw [hsum,qmaSubdivisionOnQubits_bottom,← htarget]
    apply qmaSubdivision_polynomial_accuracy 0 A B J (by norm_num) hN
      Matrix.conjTranspose_zero (by simp) hAst hBst
      (fun e => qmaPauliWord_square _) (fun e => qmaPauliWord_square _) hAB
      (EuclideanSpace.single (fun _ : ι => (0 : Fin 2)) (1:ℂ))
    simp [PiLp.norm_single]

end ContinuumCoulomb

end

end OAI
