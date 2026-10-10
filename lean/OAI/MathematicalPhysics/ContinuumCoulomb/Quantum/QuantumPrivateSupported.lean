import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZPrivate
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZEnvelopes

namespace OAI

/-! Private-pair subdivision retains its source support envelope. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem qmaXZPrivate_supported (w : κ → ι → Fin 4) (J : κ → ℝ)
    (hw : ∀ e, (qmaPauliSupport (w e)).card ≤ 2)
    (hy : ∀ e i, w e i ≠ 2) {N : ℝ} (hN : 1 ≤ N) :
    ∃ (v : (κ × Fin 4) → (ι ⊕ κ → Fin 4)) (K : (κ × Fin 4) → ℝ),
      (∀ p i, v p i ≠ 2) ∧ (∀ p, (qmaPauliSupport (v p)).card ≤ 2) ∧
      (∀ p q, (qmaPauliSupport (v p)).card = 2 →
        qmaPauliSupport (v p) = qmaPauliSupport (v q) → p = q) ∧
      (∀ p, qmaPauliSupport (v p) ⊆ qmaMediatorSupport (qmaPauliSupport (w p.1)) p.1) ∧
      |MediatorGraph.normalizedBottom (∑ p, (K p:ℂ) • qmaPauliWord (v p)) -
        MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • qmaPauliWord (w e))| ≤ 1/N := by
  choose L T hL hT hdis hcover using fun e =>
    qmaBalancedSupport (qmaPauliSupport (w e)) 1 (hw e)
  let a := fun e => qmaPauliRestrict (L e) (w e)
  let b := fun e => qmaPauliRestrict (T e) (w e)
  have ha (e : κ) : (qmaPauliSupport (a e)).card ≤ 1 :=
    (Finset.card_le_card (qmaPauliRestrict_support _ _)).trans (hL e)
  have hb (e : κ) : (qmaPauliSupport (b e)).card ≤ 1 :=
    (Finset.card_le_card (qmaPauliRestrict_support _ _)).trans (hT e)
  have hab (e : κ) : qmaPauliWord (a e)*qmaPauliWord (b e) = qmaPauliWord (w e) :=
    qmaPauliRestrict_factor _ _ _ (hdis e) (by rw [hcover e])
  have hcomm (e : κ) : qmaPauliWord (a e)*qmaPauliWord (b e) =
      qmaPauliWord (b e)*qmaPauliWord (a e) := qmaPauliRestrict_commute _ _ _ (hdis e)
  have hd (e : κ) : Disjoint (qmaPauliSupport (a e)) (qmaPauliSupport (b e)) :=
    (hdis e).mono (qmaPauliRestrict_support _ _) (qmaPauliRestrict_support _ _)
  let R := 8*(qmaThirdBudget 0 J)^4*N
  refine ⟨fun p => qmaXZSubdivisionWord (a p.1) (b p.1) p.1 p.2,
    fun p => qmaXZSubdivisionWeight R (J p.1) p.2,?_,?_,?_,?_,?_⟩
  · intro p i
    exact qmaXZSubdivision_noY _ _ _ (qmaPauliRestrict_noY _ _ (hy p.1))
      (qmaPauliRestrict_noY _ _ (hy p.1)) _ _
  · intro p
    exact qmaXZSubdivision_support _ _ _ (ha p.1) (hb p.1) _
  · intro p q hp hpq
    obtain ⟨he,hk⟩ := qmaXZSubdivision_private_pair a b hd p.1 q.1 p.2 q.2 hp hpq
    exact Prod.ext he hk
  · intro p
    apply qmaXZSubdivisionWord_envelope
    · exact (qmaPauliRestrict_support _ _).trans
        (by intro i hi; rw [← hcover p.1]; exact Finset.mem_union_left _ hi)
    · exact (qmaPauliRestrict_support _ _).trans
        (by intro i hi; rw [← hcover p.1]; exact Finset.mem_union_right _ hi)
  · have h := qmaXZSubdivision_accuracy a b J hcomm hN
    simpa only [hab] using h


end ContinuumCoulomb

end

end OAI
