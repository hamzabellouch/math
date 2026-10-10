import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedReference

namespace OAI

/-! Clock faults and endpoint pins are close to their assigned history time. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaBoundedClockTime_pair (T : ℕ) (hT : 0 < T) (i : Fin (T+1)) :
    (qmaBoundedClockTime T hT i.val).val ≤ i.val ∧
      i.val+1 ≤ (qmaBoundedClockTime T hT i.val).val+2 := by
  dsimp only [qmaBoundedClockTime]
  omega

theorem qmaSparseClockFault_cell (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (i : Fin ((qmaSparseCircuit c).gates.length+1))
    (k : QMACircuitQubit (qmaSparseCircuit c))
    (hk : k ∈ qmaCircuitTermSites (qmaSparseCircuit c) (.inl i)) :
    QMAGridCellsNear (qmaSparseQubitCell c hT k)
      (qmaSparseGateCell c (qmaBoundedClockTime _ hT i.val)) := by
  have hb := qmaBoundedClockTime_pair _ hT i
  have hk' : k = .inl i.castSucc ∨ k = .inl i.succ := by
    simpa [qmaCircuitTermSites] using hk
  rcases hk' with rfl | rfl
  · apply qmaSparseClockCells_near_gate c hT
    change (qmaBoundedClockTime _ hT i.val).val ≤ i.val ∧
      i.val ≤ (qmaBoundedClockTime _ hT i.val).val+2
    omega
  · apply qmaSparseClockCells_near_gate c hT
    change (qmaBoundedClockTime _ hT i.val).val ≤ i.val+1 ∧
      i.val+1 ≤ (qmaBoundedClockTime _ hT i.val).val+2
    omega

theorem qmaSparseClockPin_cell (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length) (b : Fin 2)
    (k : QMACircuitQubit (qmaSparseCircuit c))
    (hk : k ∈ qmaCircuitTermSites (qmaSparseCircuit c) (.inr (.inl b))) :
    QMAGridCellsNear (qmaSparseQubitCell c hT k)
      (qmaSparseGateCell c (qmaHistoryTermTime (qmaSparseCircuit c) hT
        (qmaFirstUseTime (qmaSparseCircuit c)) (.inr (.inl b)))) := by
  fin_cases b
  · have hk' : k = .inl 0 := by simpa [qmaCircuitTermSites] using hk
    subst k
    apply qmaSparseClockCells_near_gate
    exact ⟨by simp [qmaHistoryTermTime],by simp [qmaHistoryTermTime]⟩
  · have hk' : k = .inl (Fin.last ((qmaSparseCircuit c).gates.length+1)) := by
      simpa [qmaCircuitTermSites] using hk
    subst k
    apply qmaSparseClockCells_near_gate
    dsimp [qmaHistoryTermTime,qmaBoundedClockTime]
    omega

end ContinuumCoulomb

end

end OAI
