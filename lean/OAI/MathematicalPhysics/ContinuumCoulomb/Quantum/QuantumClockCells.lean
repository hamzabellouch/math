import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumClockAnchor

namespace OAI

/-! The actual unary clock bits stay next to their computation gates with bounded cell occupancy. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def QMAGridCellsNear {rows width : ℕ} (p q : QMAGridCell rows width) : Prop :=
  p.1.val ≤ q.1.val+1 ∧ q.1.val ≤ p.1.val+1 ∧
    p.2.val ≤ q.2.val+1 ∧ q.2.val ≤ p.2.val+1

def qmaSparseGateCell (c : QMACircuit) (t : Fin (qmaSparseCircuit c).gates.length) :
    QMAGridCell (qmaNearestCircuit c).gates.length c.work :=
  qmaSparseCell c (t.cast (qmaSparseTags_length c).symm)

def qmaSparseClockCell (c : QMACircuit) (hT : 0 < (qmaSparseCircuit c).gates.length)
    (b : Fin ((qmaSparseCircuit c).gates.length+2)) :
    QMAGridCell (qmaNearestCircuit c).gates.length c.work :=
  qmaSparseGateCell c (qmaClockAnchorIndex _ hT b)

theorem qmaSparseGateCells_near (c : QMACircuit) (i j : Fin (qmaSparseCircuit c).gates.length)
    (hij : i.val ≤ j.val+1) (hji : j.val ≤ i.val+1) :
    QMAGridCellsNear (qmaSparseGateCell c i) (qmaSparseGateCell c j) := by
  exact qmaGridTagChain_near (qmaSparseTags c) (qmaSparseTags_chain c)
    (i.cast (qmaSparseTags_length c).symm) (j.cast (qmaSparseTags_length c).symm) hij hji

theorem qmaSparseClockCells_near_gate (c : QMACircuit) (hT : 0 < (qmaSparseCircuit c).gates.length)
    (t : Fin (qmaSparseCircuit c).gates.length) (b : Fin ((qmaSparseCircuit c).gates.length+2))
    (hb : t.val ≤ b.val ∧ b.val ≤ t.val+2) :
    QMAGridCellsNear (qmaSparseClockCell c hT b) (qmaSparseGateCell c t) :=
  qmaSparseGateCells_near c _ t (qmaClockAnchorIndex_near _ hT t b hb).1
    (qmaClockAnchorIndex_near _ hT t b hb).2

theorem qmaSparseClockCell_middle (c : QMACircuit) (hT : 0 < (qmaSparseCircuit c).gates.length)
    (t : Fin (qmaSparseCircuit c).gates.length) :
    qmaSparseClockCell c hT (qmaClockMiddle _ t) = qmaSparseGateCell c t := by
  unfold qmaSparseClockCell
  rw [qmaClockAnchorIndex_middle]

def qmaSparseClockCellBits (c : QMACircuit) (hT : 0 < (qmaSparseCircuit c).gates.length)
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    Finset (Fin ((qmaSparseCircuit c).gates.length+2)) :=
  (qmaSparseCellTimes c p).biUnion (fun t => Finset.univ.filter
    (fun b => qmaClockAnchorIndex _ hT b = qmaSparseTime c t))

theorem qmaSparseClockCellBits_card (c : QMACircuit) (hT : 0 < (qmaSparseCircuit c).gates.length)
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    (qmaSparseClockCellBits c hT p).card ≤ 12 := by
  calc
    _ ≤ ∑ t ∈ qmaSparseCellTimes c p, (Finset.univ.filter
        (fun b => qmaClockAnchorIndex _ hT b = qmaSparseTime c t)).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ qmaSparseCellTimes c p, 3 :=
      Finset.sum_le_sum (fun t _ => qmaClockAnchorIndex_fiber_card _ hT (qmaSparseTime c t))
    _ = (qmaSparseCellTimes c p).card*3 := by simp
    _ ≤ 12 := by have := qmaSparseCellTimes_card c p; omega

theorem qmaSparseClockCellBits_mem (c : QMACircuit) (hT : 0 < (qmaSparseCircuit c).gates.length)
    (b : Fin ((qmaSparseCircuit c).gates.length+2)) :
    b ∈ qmaSparseClockCellBits c hT (qmaSparseClockCell c hT b) := by
  let t := (qmaClockAnchorIndex _ hT b).cast (qmaSparseTags_length c).symm
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
