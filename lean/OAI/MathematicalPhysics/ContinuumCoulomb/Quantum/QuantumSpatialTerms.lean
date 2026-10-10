import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSparseEndpoint
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialClockTerms

namespace OAI

/-! Every term in the actual distributed history is near its ordered reference. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaSparseOutput_cell (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (k : QMACircuitQubit (qmaSparseCircuit c))
    (hk : k ∈ qmaCircuitTermSites (qmaSparseCircuit c) (.inr (.inr (.inr (.inl ()))))) :
    QMAGridCellsNear (qmaSparseQubitCell c hT k)
      (qmaSparseGateCell c (qmaBoundedClockTime _ hT (qmaSparseCircuit c).gates.length)) := by
  have he : qmaBoundedClockTime _ hT (qmaSparseCircuit c).gates.length =
      (⟨(qmaSparseCircuit c).gates.length-1,by omega⟩ : Fin (qmaSparseCircuit c).gates.length) := by
    apply Fin.ext
    change min _ (_-1) = _-1
    omega
  have hk' : k = .inl (qmaOutputMarker (qmaSparseCircuit c)) ∨
      k = .inr (Fin.last (qmaSparseCircuit c).work) := by
    simpa [qmaCircuitTermSites] using hk
  rcases hk' with rfl | rfl
  · rw [he]
    apply qmaSparseClockCells_near_gate c hT
    change (qmaSparseCircuit c).gates.length-1 ≤ (qmaSparseCircuit c).gates.length ∧
      (qmaSparseCircuit c).gates.length ≤ (qmaSparseCircuit c).gates.length-1+2
    omega
  · change QMAGridCellsNear (qmaSparseWorkCell c (Fin.last (qmaSparseCircuit c).work)) _
    rw [he,qmaSparseWorkCell_last,qmaSparseGateCell_last c hT]
    unfold QMAGridCellsNear
    simp only [Fin.val_last]
    omega

theorem qmaSparseHistoryTerm_cell (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (a : QMACircuitTerm (qmaSparseCircuit c))
    (k : QMACircuitQubit (qmaSparseCircuit c))
    (hk : k ∈ qmaDistributedTermSites (qmaSparseCircuit c)
      (qmaFirstUseTime (qmaSparseCircuit c)) a) :
    QMAGridCellsNear (qmaSparseQubitCell c hT k)
      (qmaSparseGateCell c (qmaHistoryTermTime (qmaSparseCircuit c) hT
        (qmaFirstUseTime (qmaSparseCircuit c)) a)) := by
  rcases a with i | (b | (i | (u | t)))
  · exact qmaSparseClockFault_cell c hT i k hk
  · exact qmaSparseClockPin_cell c hT b k hk
  · have hi := qmaSweepFirstUse_lt (qmaNearestCircuit c) hne i
    have he := qmaBoundedClockTime_eq _ hT (⟨qmaFirstUse (qmaSparseCircuit c) i,hi⟩ :
      Fin (qmaSparseCircuit c).gates.length)
    change QMAGridCellsNear _ (qmaSparseGateCell c (qmaBoundedClockTime _ hT _))
    rw [he]
    exact qmaSparseInput_cell c hc hT i hi k hk
  · cases u
    exact qmaSparseOutput_cell c hT k hk
  · exact qmaSparsePropagation_cell c hc hT t k hk

end ContinuumCoulomb

end

end OAI
