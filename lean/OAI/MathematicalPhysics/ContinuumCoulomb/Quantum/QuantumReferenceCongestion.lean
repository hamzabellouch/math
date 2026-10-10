import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTimeCongestion

namespace OAI

/-! Time ordering gives a constant number of reference qubits per spatial cell. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaOrderedReferenceTime_fiber_card (c : QMACircuit) (hT : 0 < c.gates.length)
    (hi : ∀ i, qmaFirstUse c i < c.gates.length) (t : Fin c.gates.length) :
    (Finset.univ.filter (fun i => qmaOrderedReferenceTime c hT (qmaFirstUseTime c) i = t)).card ≤ 8 := by
  calc
    _ = (Finset.univ.filter (fun a : QMACircuitTerm c =>
        qmaHistoryTermTime c hT (qmaFirstUseTime c) a = t)).card := by
      apply Finset.card_equiv (qmaOrderedTermEquiv c hT (qmaFirstUseTime c))
      intro i
      constructor
      · intro hm
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hm).2⟩
      · intro hm
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hm).2⟩
    _ ≤ 8 := qmaHistoryTimeFiber_card c hT hi t

def qmaSparseReferenceCellIndices (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    Finset (Fin (qmaHistoryReferenceWork (qmaSparseCircuit c)+1)) :=
  (qmaSparseCellTimes c p).biUnion (fun t => Finset.univ.filter
    (fun i => qmaOrderedReferenceTime (qmaSparseCircuit c) hT
      (qmaFirstUseTime (qmaSparseCircuit c)) i = qmaSparseTime c t))

theorem qmaSparseReferenceCellIndices_card (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ [])
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    (qmaSparseReferenceCellIndices c hT p).card ≤ 32 := by
  calc
    _ ≤ ∑ t ∈ qmaSparseCellTimes c p, (Finset.univ.filter
        (fun i => qmaOrderedReferenceTime (qmaSparseCircuit c) hT
          (qmaFirstUseTime (qmaSparseCircuit c)) i = qmaSparseTime c t)).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ qmaSparseCellTimes c p, 8 := by
      apply Finset.sum_le_sum
      intro t _
      exact qmaOrderedReferenceTime_fiber_card _ hT (qmaSweepFirstUse_lt _ hne) _
    _ = (qmaSparseCellTimes c p).card*8 := by simp
    _ ≤ 32 := by have := qmaSparseCellTimes_card c p; omega

theorem qmaSparseReferenceCellIndices_mem (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (i : Fin (qmaHistoryReferenceWork (qmaSparseCircuit c)+1)) :
    i ∈ qmaSparseReferenceCellIndices c hT (qmaOrderedSparseReferenceCell c hT i) := by
  let t := (qmaOrderedReferenceTime (qmaSparseCircuit c) hT
    (qmaFirstUseTime (qmaSparseCircuit c)) i).cast (qmaSparseTags_length c).symm
  apply Finset.mem_biUnion.mpr
  refine ⟨t,?_,?_⟩
  · simp only [qmaSparseCellTimes,Finset.mem_filter,Finset.mem_univ,true_and]
    rfl
  · simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    apply Fin.ext
    rfl

end ContinuumCoulomb

end

end OAI
