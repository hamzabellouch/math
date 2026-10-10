import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZSubdivision

namespace OAI

/-! Elimination of all YY terms by an explicit three-local X/Z family. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem qmaXZSubdivision_accuracy (a b : κ → ι → Fin 4) (J : κ → ℝ)
    (hab : ∀ e, qmaPauliWord (a e)*qmaPauliWord (b e) =
      qmaPauliWord (b e)*qmaPauliWord (a e)) {N : ℝ} (hN : 1 ≤ N) :
    let R := 8*(qmaThirdBudget 0 J)^4*N
    |MediatorGraph.normalizedBottom (∑ p : κ × Fin 4,
      (qmaXZSubdivisionWeight R (J p.1) p.2 : ℂ) •
        qmaPauliWord (qmaXZSubdivisionWord (a p.1) (b p.1) p.1 p.2)) -
      MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) •
        (qmaPauliWord (a e)*qmaPauliWord (b e)))| ≤ 1/N := by
  dsimp only
  let A := fun e => qmaPauliWord (a e)
  let B := fun e => qmaPauliWord (b e)
  let R := 8*(qmaThirdBudget 0 J)^4*N
  have hsum : (∑ p : κ × Fin 4, (qmaXZSubdivisionWeight R (J p.1) p.2 : ℂ) •
      qmaPauliWord (qmaXZSubdivisionWord (a p.1) (b p.1) p.1 p.2)) =
      qmaSubdivisionOnQubits 0 A B R J (fun _ => false) := by
    rw [Fintype.sum_prod_type]
    simp only [qmaXZSubdivision_sum]
    unfold qmaSubdivisionOnQubits
    rw [qmaSubdivisionPolarized_decomposition]
    simp only [Matrix.zero_kronecker,zero_add,MediatorGraph.submatrix_sum,
      qmaSubdivisionPiece_reindex,A,B]
  have ht : qmaSubdivisionTarget 0 A B (fun e => (J e:ℂ)) =
      ∑ e, (J e:ℂ) • (qmaPauliWord (a e)*qmaPauliWord (b e)) := by
    simp [qmaSubdivisionTarget,A,B]
  rw [hsum,qmaSubdivisionOnQubits_bottom,← ht]
  apply qmaSubdivision_polynomial_accuracy 0 A B J (by norm_num) hN
    Matrix.conjTranspose_zero (by simp)
    (fun _ => qmaPauliWord_hermitian _) (fun _ => qmaPauliWord_hermitian _)
    (fun _ => qmaPauliWord_square _) (fun _ => qmaPauliWord_square _) hab
    (EuclideanSpace.single (fun _ : ι => (0:Fin 2)) (1:ℂ))
  simp [PiLp.norm_single]

theorem qmaYYReduction_exists (w : κ → ι → Fin 4) (J : κ → ℝ)
    (hw : ∀ e, (qmaPauliSupport (w e)).card ≤ 2)
    (he : ∀ e, Even (qmaPauliYCount (w e))) {N : ℝ} (hN : 1 ≤ N) :
    ∃ (v : (κ × Fin 4) → (ι ⊕ κ → Fin 4)) (K : (κ × Fin 4) → ℝ),
      (∀ p i, v p i ≠ 2) ∧ (∀ p, (qmaPauliSupport (v p)).card ≤ 3) ∧
      |MediatorGraph.normalizedBottom (∑ p, (K p:ℂ) • qmaPauliWord (v p)) -
        MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • qmaPauliWord (w e))| ≤ 1/N := by
  choose a b ha hb hsa hsb hfactor hcomm using
    fun e => qmaTwoLocalEvenXZFactor (w e) (hw e) (he e)
  let R := 8*(qmaThirdBudget 0 J)^4*N
  refine ⟨fun p => qmaXZSubdivisionWord (a p.1) (b p.1) p.1 p.2,
    fun p => qmaXZSubdivisionWeight R (J p.1) p.2,?_,?_,?_⟩
  · intro p i
    exact qmaXZSubdivision_noY _ _ _ (ha p.1) (hb p.1) _ _
  · intro p
    exact qmaXZSubdivision_support _ _ _ (hsa p.1) (hsb p.1) _
  · have h := qmaXZSubdivision_accuracy a b J hcomm hN
    simpa only [hfactor] using h

end ContinuumCoulomb

end

end OAI
