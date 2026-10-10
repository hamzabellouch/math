import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridCoordinates

namespace OAI

/-! Every actual propagation interaction is contained near its computation-gate anchor. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaSparsePropagation_cell (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length) (t : Fin (qmaSparseCircuit c).gates.length)
    (k : QMACircuitQubit (qmaSparseCircuit c)) (hk : k ∈ qmaPropagationSites (qmaSparseCircuit c) t) :
    QMAGridCellsNear (qmaSparseQubitCell c hT k) (qmaSparseGateCell c t) := by
  cases k with
  | inl b =>
    have hb : b = qmaClockLeft _ t ∨ b = qmaClockMiddle _ t ∨ b = qmaClockRight _ t := by
      simpa [qmaPropagationSites] using hk
    rcases hb with rfl | rfl | rfl
    · exact qmaSparseClockCells_near_gate c hT t _ ⟨le_rfl,by simp [qmaClockLeft]⟩
    · apply qmaSparseClockCells_near_gate c hT t
      simp [qmaClockMiddle]
    · apply qmaSparseClockCells_near_gate c hT t
      simp [qmaClockRight]
  | inr i =>
    apply qmaSparseWorkCell_near_gate c hc t i
    have hi : i ∈ qmaGateSites (qmaSparseCircuit c).work
        ((qmaSparseCircuit c).gates.getD t.val (.hadamard 0)) := by
      simpa [qmaPropagationSites] using hk
    simpa only [List.getD_eq_getElem _ _ t.isLt] using hi

end ContinuumCoulomb

end

end OAI
