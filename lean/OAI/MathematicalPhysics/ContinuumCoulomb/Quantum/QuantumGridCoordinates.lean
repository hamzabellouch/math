import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumClockCells
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumDistributedFamily

namespace OAI

/-! Explicit row/column coordinates for every physical computation qubit. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaGridCoordinates (rows width : ℕ) (k : Fin (qmaGridWork rows width+1)) : QMAGridCell rows width :=
  (⟨k.val/(width+1),by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < width+1)).mpr
    have hk := k.isLt
    change k.val < width+rows*(width+1)+1 at hk
    nlinarith⟩,
   ⟨k.val%(width+1),Nat.mod_lt _ (by omega)⟩)

theorem qmaGridCoordinates_right (rows width : ℕ) (k : Fin (qmaGridWork rows width+1)) :
    qmaGridQubit rows width (qmaGridCoordinates rows width k).1 (qmaGridCoordinates rows width k).2 = k := by
  apply Fin.ext
  change k.val/(width+1)*(width+1)+k.val%(width+1) = k.val
  simpa only [Nat.mul_comm] using Nat.div_add_mod k.val (width+1)

theorem qmaGridCoordinates_left (rows width : ℕ) (r : Fin (rows+1)) (j : Fin (width+1)) :
    qmaGridCoordinates rows width (qmaGridQubit rows width r j) = (r,j) :=
  qmaGridQubit_injective rows width (qmaGridCoordinates_right _ _ _)

def qmaSparseWorkCell (c : QMACircuit) (i : Fin ((qmaSparseCircuit c).work+1)) :
    QMAGridCell (qmaNearestCircuit c).gates.length c.work :=
  qmaGridCoordinates (qmaNearestCircuit c).gates.length c.work i

theorem qmaSparseWorkCell_near_gate (c : QMACircuit) (hc : c.WellFormed)
    (t : Fin (qmaSparseCircuit c).gates.length) (i : Fin ((qmaSparseCircuit c).work+1))
    (hi : i ∈ qmaGateSites (qmaSparseCircuit c).work (qmaSparseCircuit c).gates[t.val]) :
    QMAGridCellsNear (qmaSparseWorkCell c i) (qmaSparseGateCell c t) := by
  let u := t.cast (qmaSparseTags_length c).symm
  have hu : qmaSparseTime c u = t := by apply Fin.ext; rfl
  rw [←hu,←qmaSparseTag_gate] at hi
  obtain ⟨r,j,he,hl,hr,hj,hj'⟩ :=
    qmaSparseTags_located c hc _ (List.getElem_mem u.isLt) i hi
  unfold qmaSparseWorkCell
  rw [he,qmaGridCoordinates_left]
  change r.val ≤ (qmaSparseCell c u).1.val+1 ∧
    (qmaSparseCell c u).1.val ≤ r.val+1 ∧
    j.val ≤ (qmaSparseCell c u).2.val+1 ∧ (qmaSparseCell c u).2.val ≤ j.val+1
  exact ⟨hr,hl.trans (Nat.le_succ _),hj,hj'⟩

def qmaSparseQubitCell (c : QMACircuit) (hT : 0 < (qmaSparseCircuit c).gates.length) :
    QMACircuitQubit (qmaSparseCircuit c) → QMAGridCell (qmaNearestCircuit c).gates.length c.work
  | .inl b => qmaSparseClockCell c hT b
  | .inr i => qmaSparseWorkCell c i

end ContinuumCoulomb

end

end OAI
