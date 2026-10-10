import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialReference

namespace OAI

/-! The concrete real history model has bounded qubit and term density in its grid. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaSparseWorkCell_injective (c : QMACircuit) : Function.Injective (qmaSparseWorkCell c) := by
  intro i j h
  have hh := congrArg (fun p => qmaGridQubit (qmaNearestCircuit c).gates.length c.work p.1 p.2) h
  simpa only [qmaSparseWorkCell,qmaGridCoordinates_right] using hh

theorem qmaSparseWorkCell_fiber_card (c : QMACircuit)
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    (Finset.univ.filter (fun i => qmaSparseWorkCell c i = p)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact qmaSparseWorkCell_injective c
    ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)

theorem qmaSparseClockCell_fiber_card (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    (Finset.univ.filter (fun b => qmaSparseClockCell c hT b = p)).card ≤ 12 := by
  apply (Finset.card_le_card (show _ ⊆ qmaSparseClockCellBits c hT p from ?_)).trans
    (qmaSparseClockCellBits_card c hT p)
  intro b hb
  have hm := qmaSparseClockCellBits_mem c hT b
  rw [(Finset.mem_filter.mp hb).2] at hm
  exact hm

theorem qmaOrderedReferenceCell_fiber_card (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ [])
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    (Finset.univ.filter (fun i => qmaOrderedSparseReferenceCell c hT i = p)).card ≤ 32 := by
  apply (Finset.card_le_card (show _ ⊆ qmaSparseReferenceCellIndices c hT p from ?_)).trans
    (qmaSparseReferenceCellIndices_card c hT hne p)
  intro i hi
  have hm := qmaSparseReferenceCellIndices_mem c hT i
  rw [(Finset.mem_filter.mp hi).2] at hm
  exact hm

theorem qmaOrderedQubitCell_fiber_card (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ [])
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    (Finset.univ.filter (fun k => qmaOrderedQubitCell c hT k = p)).card ≤ 45 := by
  rw [qmaSumFilter_card]
  change (Finset.univ.filter (fun i => qmaOrderedSparseReferenceCell c hT i = p)).card+
    (Finset.univ.filter (fun k : Fin ((qmaSparseCircuit c).gates.length+2) ⊕
      Fin ((qmaSparseCircuit c).work+1) => qmaSparseQubitCell c hT k = p)).card ≤ 45
  rw [qmaSumFilter_card]
  exact (Nat.add_le_add (qmaOrderedReferenceCell_fiber_card c hT hne p)
    (Nat.add_le_add (qmaSparseClockCell_fiber_card c hT p) (qmaSparseWorkCell_fiber_card c p))).trans
      (by decide)

theorem qmaOrderedTermCell_fiber_card (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ [])
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    (Finset.univ.filter (fun a => qmaOrderedTermCell c hT a = p)).card ≤ 64 := by
  have hr := qmaOrderedReferenceCell_fiber_card c hT hne p
  have he : (Finset.univ.filter (fun i : Fin (qmaHistoryReferenceWork (qmaSparseCircuit c)) =>
      qmaOrderedSparseReferenceCell c hT i.castSucc = p)).card ≤
      (Finset.univ.filter (fun i => qmaOrderedSparseReferenceCell c hT i = p)).card := by
    apply Finset.card_le_card_of_injOn Fin.castSucc
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
    · intro i _ j _ h
      exact (Fin.castSucc_inj.mp h)
  change (Finset.univ.filter (fun a : Fin (qmaHistoryReferenceWork (qmaSparseCircuit c)+1) ⊕
    Fin (qmaHistoryReferenceWork (qmaSparseCircuit c)) => qmaOrderedTermCell c hT a = p)).card ≤ 64
  rw [qmaSumFilter_card]
  exact (Nat.add_le_add hr (he.trans hr)).trans (by decide)

end ContinuumCoulomb

end

end OAI
