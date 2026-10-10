import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedThird
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSubdivisionSites

namespace OAI

/-! Exact ordered support lists for the seven emitted third-order terms. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedThird
open QuantumOrderedTriple QuantumOrderedSubdivision
open scoped Classical
variable {ι κ : Type}

def outputSites (xs : κ → List ι) (w : κ → ι → Fin 4) (p : κ × Fin 7) : List (ι ⊕ κ) :=
  let pair := (partition (xs p.1) (w p.1)).1
  let real := (partition (xs p.1) (w p.1)).2
  ![[],[Sum.inr p.1],pair.map Sum.inl,real.map Sum.inl,
    appendMediator real p.1,appendMediator (pair.take 1) p.1,
    appendMediator (pair.drop 1) p.1] p.2

theorem outputSites_nodup (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 3) (hx : ∀ e, (xs e).Nodup) (p : κ × Fin 7) :
    (outputSites xs w p).Nodup := by
  rcases p with ⟨e,k⟩
  have hp := pair_nodup (xs e) (w e) (hlen e) (hx e)
  have hc := (partition_nodup (xs e) (w e) (hlen e) (hx e)).of_append_right
  fin_cases k
  · exact List.nodup_nil
  · exact List.nodup_singleton _
  · exact hp.map Sum.inl_injective
  · exact hc.map Sum.inl_injective
  · exact appendMediator_nodup _ hc e
  · exact appendMediator_nodup _ (hp.sublist (List.take_sublist 1 _)) e
  · exact appendMediator_nodup _ (hp.sublist (List.drop_sublist 1 _)) e

theorem outputSites_length (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 3) (p : κ × Fin 7) :
    (outputSites xs w p).length ≤ 2 := by
  rcases p with ⟨e,k⟩
  have hp := (partition_spec (xs e) (w e) (hlen e)).2.1
  have hc := (partition_spec (xs e) (w e) (hlen e)).2.2
  fin_cases k
  · change 0 ≤ 2
    omega
  · change 1 ≤ 2
    omega
  · change ((partition (xs e) (w e)).1.map Sum.inl).length ≤ 2
    simpa only [List.length_map] using hp
  · change ((partition (xs e) (w e)).2.map Sum.inl).length ≤ 2
    simpa only [List.length_map] using hc.trans (by omega : 1 ≤ 2)
  · change (appendMediator (partition (xs e) (w e)).2 e).length ≤ 2
    rw [appendMediator_length]
    omega
  · change (appendMediator ((partition (xs e) (w e)).1.take 1) e).length ≤ 2
    rw [appendMediator_length,List.length_take]
    omega
  · change (appendMediator ((partition (xs e) (w e)).1.drop 1) e).length ≤ 2
    rw [appendMediator_length,List.length_drop]
    omega

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem lift_support_cover (xs : List ι) (w : ι → Fin 4)
    (h : qmaPauliSupport w ⊆ xs.toFinset) :
    qmaPauliSupport (Sum.elim w (fun _ : κ => 0)) ⊆ (xs.map Sum.inl).toFinset := by
  intro x hx
  cases x with
  | inl i =>
    have hi : i ∈ qmaPauliSupport w := by simpa [qmaPauliSupport] using hx
    simpa using h hi
  | inr j => simp [qmaPauliSupport] at hx

theorem outputSites_cover (xs : κ → List ι) (w : κ → ι → Fin 4) (p : κ × Fin 7) :
    qmaPauliSupport (outputWord xs w p) ⊆ (outputSites xs w p).toFinset := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · change qmaPauliSupport (fun _ : ι ⊕ κ => 0) ⊆ ([] : List (ι ⊕ κ)).toFinset
    simp [qmaPauliSupport]
  · intro x hx
    cases x with
    | inl i => simp [outputWord,QuantumPolarizedThird.word,qmaPauliSupport] at hx
    | inr j =>
      have hj : j ∈ qmaPauliSupport (qmaSinglePauliWord e 3) := by
        simpa [outputWord,QuantumPolarizedThird.word,qmaPauliSupport] using hx
      have hje := qmaSinglePauliWord_support e 3 hj
      simpa [outputSites] using hje
  · exact lift_support_cover _ (pairWord (xs e) (w e)) (qmaPauliRestrict_support _ _)
  · exact lift_support_cover _ (third (xs e) (w e)) (qmaPauliRestrict_support _ _)
  · exact join_support_cover _ (third (xs e) (w e)) (qmaPauliRestrict_support _ _) e 3
  · exact join_support_cover _ (first (xs e) (w e)) (qmaPauliRestrict_support _ _) e _
  · exact join_support_cover _ (second (xs e) (w e)) (qmaPauliRestrict_support _ _) e _

end ContinuumCoulomb.QuantumOrderedThird

end

end OAI
