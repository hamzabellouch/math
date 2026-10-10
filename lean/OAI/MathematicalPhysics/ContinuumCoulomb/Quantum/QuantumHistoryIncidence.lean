import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedIncidence
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPaddedLabelTable
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridNeighbors

namespace OAI

/-! The sparse verifier history has uniformly bounded site incidence, even
with all 4096 padded Pauli patterns retained. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryIncidence
open QuantumOrderedIncidence
open scoped BigOperators Classical

theorem sparse_reference_bound (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) :
    Bounded (QuantumOrderedSupport.sites (qmaSparseCircuit c) hT) 576 := by
  intro q
  let ss : QMAReferenceTerm (qmaHistoryReferenceWork (qmaSparseCircuit c)) →
      Finset (QuantumOrderedSupport.Qubit (qmaSparseCircuit c)) :=
    fun a => (QuantumOrderedSupport.sites (qmaSparseCircuit c) hT a).toFinset
  have hlocal : ∀ a, ∀ j ∈ ss a,
      QMAGridCellsNear (qmaOrderedQubitCell c hT j) (qmaOrderedTermCell c hT a) := by
    intro a j hj
    apply qmaOrderedHistoryModel_spatial c hc hT hne a j
    exact (QuantumOrderedSupport.sites_finset (qmaSparseCircuit c) hT a) ▸ hj
  have h := qmaGrid_incidence_bound (qmaOrderedQubitCell c hT) (qmaOrderedTermCell c hT)
    ss hlocal (qmaOrderedTermCell_fiber_card c hT hne) q
  have hm (a : QMAReferenceTerm (qmaHistoryReferenceWork (qmaSparseCircuit c))) :
      q ∈ QuantumOrderedSupport.sites (qmaSparseCircuit c) hT a ↔ q ∈ ss a :=
    List.mem_toFinset.symm
  have he : count (QuantumOrderedSupport.sites (qmaSparseCircuit c) hT) q =
      (Finset.univ.filter (fun a : QMAReferenceTerm
        (qmaHistoryReferenceWork (qmaSparseCircuit c)) =>
          q ∈ ss a)).card := by
    rw [count,Finset.card_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : q ∈ QuantumOrderedSupport.sites (qmaSparseCircuit c) hT a
    · rw [ite_eq_left ha,ite_eq_left ((hm a).mp ha)]
    · rw [ite_eq_right ha,ite_eq_right (mt (hm a).mpr ha)]
  exact he.trans_le (h.trans (by norm_num : 9*64 ≤ 576))

theorem padded_bound {ι κ ν : Type} [Fintype κ] [Fintype ν]
    (xs : κ → List ι) {D : ℕ} (hx : Bounded xs D) :
    Bounded (fun p : κ × ν => xs p.1) (Fintype.card ν*D) := by
  intro q
  calc
    count (fun p : κ × ν => xs p.1) q = Fintype.card ν*count xs q := by
      rw [count,Fintype.sum_prod_type]
      have hi (e : κ) : (∑ _k : ν, if q ∈ xs e then 1 else 0) =
          Fintype.card ν*(if q ∈ xs e then 1 else 0) := by
        by_cases h : q ∈ xs e <;> simp [h]
      simp_rw [hi]
      exact (Finset.mul_sum _ _ _).symm
    _ ≤ Fintype.card ν*D := Nat.mul_le_mul_left _ (hx q)

theorem sparse_padded_bound (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) :
    Bounded (fun p : QuantumPaddedHistory.Term (qmaSparseCircuit c) =>
      QuantumOrderedSupport.sites (qmaSparseCircuit c) hT p.1) 2359296 := by
  have h := padded_bound (ν := Fin 6 → Fin 4)
    (QuantumOrderedSupport.sites (qmaSparseCircuit c) hT)
    (sparse_reference_bound c hc hT hne)
  simp only [Fintype.card_fun,Fintype.card_fin] at h
  have hn : 4^6*576=2359296 := by norm_num
  rw [hn] at h
  exact h

end ContinuumCoulomb.QuantumHistoryIncidence

end

end OAI
