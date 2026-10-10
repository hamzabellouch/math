import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialPropagation
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumReferenceModel

namespace OAI

/-! Both clock bits and the initialized qubit are near the first-use gate. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaSparseInput_cell (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length) (i : Fin ((qmaSparseCircuit c).work+1))
    (ht : qmaFirstUse (qmaSparseCircuit c) i < (qmaSparseCircuit c).gates.length)
    (k : QMACircuitQubit (qmaSparseCircuit c))
    (hk : k ∈ qmaDistributedInputSites (qmaSparseCircuit c) (qmaFirstUseTime (qmaSparseCircuit c)) i) :
    QMAGridCellsNear (qmaSparseQubitCell c hT k)
      (qmaSparseGateCell c ⟨qmaFirstUse (qmaSparseCircuit c) i,ht⟩) := by
  let t : Fin (qmaSparseCircuit c).gates.length := ⟨qmaFirstUse (qmaSparseCircuit c) i,ht⟩
  cases k with
  | inl b =>
    have hb : b = (qmaFirstUseTime (qmaSparseCircuit c) i).castSucc ∨
        b = (qmaFirstUseTime (qmaSparseCircuit c) i).succ := by
      simpa [qmaDistributedInputSites] using hk
    rcases hb with rfl | rfl
    · apply qmaSparseClockCells_near_gate c hT t
      change t.val ≤ t.val ∧ t.val ≤ t.val+2
      omega
    · apply qmaSparseClockCells_near_gate c hT t
      change t.val ≤ t.val+1 ∧ t.val+1 ≤ t.val+2
      omega
  | inr j =>
    have hj : j = i := by simpa [qmaDistributedInputSites] using hk
    subst j
    apply qmaSparseWorkCell_near_gate c hc t i
    apply qmaFirstUseSites_subset
    simp only [qmaFirstUseSites,Finset.mem_filter,Finset.mem_univ,true_and]
    rfl

end ContinuumCoulomb

end

end OAI
