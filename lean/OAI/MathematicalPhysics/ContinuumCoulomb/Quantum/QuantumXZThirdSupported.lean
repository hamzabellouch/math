import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZReduction
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZSupportFactors
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZEnvelopes

namespace OAI

/-! X/Z third-order reduction preserves an explicit support envelope for every emitted term. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem qmaXZThird_supported (w : κ → ι → Fin 4) (J : κ → ℝ)
    (hw : ∀ e, (qmaPauliSupport (w e)).card ≤ 3)
    (hy : ∀ e i, w e i ≠ 2) {N : ℝ} (hN : 1 ≤ N) :
    ∃ (v : (κ × Fin 7) → (ι ⊕ κ → Fin 4)) (K : (κ × Fin 7) → ℝ),
      (∀ p i, v p i ≠ 2) ∧ (∀ p, (qmaPauliSupport (v p)).card ≤ 2) ∧
      (∀ p, qmaPauliSupport (v p) ⊆ qmaMediatorSupport (qmaPauliSupport (w p.1)) p.1) ∧
      |MediatorGraph.normalizedBottom (∑ p, (K p:ℂ) • qmaPauliWord (v p)) -
        MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • qmaPauliWord (w e))| ≤ 1/N := by
  choose a b c v has hbs hcs hvs hay hby hcy hvy ha hb hc hv hab hvc habc hac hbc using
    fun e => qmaXZTriple_supported (w e) (hw e) (hy e)
  let A := fun e => qmaPauliWord (a e)
  let B := fun e => qmaPauliWord (b e)
  let C := fun e => qmaPauliWord (c e)
  let R := 8*(qmaThirdBudget 0 J)^4*N
  refine ⟨fun p => qmaXZThirdWord (a p.1) (b p.1) (c p.1) (v p.1) p.1 p.2,
    fun p => qmaXZThirdWeight R (J p.1) p.2,?_,?_,?_,?_⟩
  · intro p i
    exact qmaXZThird_noY _ _ _ _ _ (hay p.1) (hby p.1) (hcy p.1) (hvy p.1) _ _
  · intro p
    exact qmaXZThird_support _ _ _ _ _ (ha p.1) (hb p.1) (hc p.1) (hv p.1) _
  · intro p
    exact qmaXZThirdWord_envelope _ _ _ _ _ (has p.1) (hbs p.1) (hcs p.1) (hvs p.1) p.2
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


end ContinuumCoulomb

end

end OAI
