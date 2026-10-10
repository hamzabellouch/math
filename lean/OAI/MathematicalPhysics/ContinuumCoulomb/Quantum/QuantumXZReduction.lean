import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZThird
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumYYReduction

namespace OAI

/-! Explicit reduction to two-local X/Z Pauli terms, with full-space spectral error. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem qmaXZThird_exists (w : κ → ι → Fin 4) (J : κ → ℝ)
    (hw : ∀ e, (qmaPauliSupport (w e)).card ≤ 3)
    (hy : ∀ e i, w e i ≠ 2) {N : ℝ} (hN : 1 ≤ N) :
    ∃ (v : (κ × Fin 7) → (ι ⊕ κ → Fin 4)) (K : (κ × Fin 7) → ℝ),
      (∀ p i, v p i ≠ 2) ∧ (∀ p, (qmaPauliSupport (v p)).card ≤ 2) ∧
      |MediatorGraph.normalizedBottom (∑ p, (K p:ℂ) • qmaPauliWord (v p)) -
        MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • qmaPauliWord (w e))| ≤ 1/N := by
  choose a b c v hay hby hcy hvy ha hb hc hv hab hvc habc hac hbc using
    fun e => qmaXZTripleFactor (w e) (hw e) (hy e)
  let A := fun e => qmaPauliWord (a e)
  let B := fun e => qmaPauliWord (b e)
  let C := fun e => qmaPauliWord (c e)
  let R := 8*(qmaThirdBudget 0 J)^4*N
  refine ⟨fun p => qmaXZThirdWord (a p.1) (b p.1) (c p.1) (v p.1) p.1 p.2,
    fun p => qmaXZThirdWeight R (J p.1) p.2,?_,?_,?_⟩
  · intro p i
    exact qmaXZThird_noY _ _ _ _ _ (hay p.1) (hby p.1) (hcy p.1) (hvy p.1) _ _
  · intro p
    exact qmaXZThird_support _ _ _ _ _ (ha p.1) (hb p.1) (hc p.1) (hv p.1) _
  · have hsum : (∑ p : κ × Fin 7, (qmaXZThirdWeight R (J p.1) p.2 : ℂ) •
        qmaPauliWord (qmaXZThirdWord (a p.1) (b p.1) (c p.1) (v p.1) p.1 p.2)) =
        (qmaThirdGadget 0 A B C R J).submatrix
          (Equiv.sumArrowEquivProdArrow ι κ (Fin 2))
          (Equiv.sumArrowEquivProdArrow ι κ (Fin 2)) := by
      rw [Fintype.sum_prod_type]
      simp only [qmaXZThird_sum _ _ _ _ _ _ _ (hab _)]
      rw [qmaThirdGadget_decomposition]
      simp only [Matrix.zero_kronecker,zero_add,MediatorGraph.submatrix_sum,qmaThirdPiece_reindex,A,B,C]
    have ht : qmaThirdSeriesTarget 0 A B C (fun e => (J e:ℂ)) =
        ∑ e, (J e:ℂ) • qmaPauliWord (w e) := by
      simp only [qmaThirdSeriesTarget,zero_add,A,B,C,hab,hvc]
    rw [hsum,MediatorGraph.normalizedBottom_reindex,← ht]
    apply qmaThirdGadget_polynomial_accuracy 0 A B C J (by norm_num) hN
      Matrix.conjTranspose_zero (by simp)
      (fun _ => qmaPauliWord_hermitian _) (fun _ => qmaPauliWord_hermitian _)
      (fun _ => qmaPauliWord_hermitian _)
      (fun _ => qmaPauliWord_square _) (fun _ => qmaPauliWord_square _)
      (fun _ => qmaPauliWord_square _) habc hac hbc
      (EuclideanSpace.single (fun _ : ι => (0:Fin 2)) (1:ℂ))
    simp [PiLp.norm_single]

theorem qmaTwoLocalXZ_exists (w : κ → ι → Fin 4) (J : κ → ℝ)
    (hw : ∀ e, (qmaPauliSupport (w e)).card ≤ 2)
    (he : ∀ e, Even (qmaPauliYCount (w e))) {N : ℝ} (hN : 1 ≤ N) :
    ∃ (v : ((κ × Fin 4) × Fin 7) → ((ι ⊕ κ) ⊕ (κ × Fin 4) → Fin 4))
      (K : ((κ × Fin 4) × Fin 7) → ℝ),
      (∀ p i, v p i ≠ 2) ∧ (∀ p, (qmaPauliSupport (v p)).card ≤ 2) ∧
      |MediatorGraph.normalizedBottom (∑ p, (K p:ℂ) • qmaPauliWord (v p)) -
        MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • qmaPauliWord (w e))| ≤ 1/N := by
  have h2N : 1 ≤ 2*N := by linarith
  obtain ⟨u,L,huy,hu,he₁⟩ := qmaYYReduction_exists w J hw he h2N
  obtain ⟨v,K,hvy,hv,he₂⟩ := qmaXZThird_exists u L hu huy h2N
  refine ⟨v,K,hvy,hv,?_⟩
  calc
    _ ≤ |MediatorGraph.normalizedBottom (∑ p, (K p:ℂ) • qmaPauliWord (v p)) -
          MediatorGraph.normalizedBottom (∑ p, (L p:ℂ) • qmaPauliWord (u p))| +
        |MediatorGraph.normalizedBottom (∑ p, (L p:ℂ) • qmaPauliWord (u p)) -
          MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • qmaPauliWord (w e))| := abs_sub_le _ _ _
    _ ≤ 1/(2*N)+1/(2*N) := add_le_add he₂ he₁
    _ = 1/N := by ring

end ContinuumCoulomb

end

end OAI
