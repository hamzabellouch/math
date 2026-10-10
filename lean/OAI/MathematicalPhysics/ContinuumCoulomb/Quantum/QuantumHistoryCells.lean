import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSweepCells
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumDescriptorSites
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialReference
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedCellTable
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPaddedLabelTable

namespace OAI

/-! Natural cell lookups for the actual sparse history.  The reference
lookup uses the same time-grouped descriptors as the sampled Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryCells
open QuantumHistoryDescriptors QuantumOrderedSourceIndex

def encodeCell {rows width : ℕ} (p : QMAGridCell rows width) : ℕ × ℕ :=
  (p.1.val,p.2.val)

def gateCell (c : QMACircuit) (t : ℕ) : ℕ × ℕ :=
  ((QuantumSweepCells.value c).drop t).headD (0,0)

def referenceCell (c : QMACircuit) (i : ℕ) : ℕ × ℕ :=
  gateCell c (timeValue (qmaSparseCircuit c) (orderedAt (qmaSparseCircuit c) i))

def qubitCell (c : QMACircuit) (j : ℕ) : ℕ × ℕ :=
  let s := qmaSparseCircuit c
  let refs := referenceWork s+1
  if j<refs then referenceCell c j else
  let k := j-refs
  if k<s.gates.length+2 then gateCell c (min (k-1) (s.gates.length-1)) else
    let w := k-(s.gates.length+2)
    (w/(c.work+1),w%(c.work+1))

def termCell (c : QMACircuit) (i : ℕ) : ℕ × ℕ :=
  let refs := referenceWork (qmaSparseCircuit c)+1
  referenceCell c (if i<refs then i else i-refs)

def qubitCells (c : QMACircuit) : List (ℕ × ℕ) :=
  (List.range (qubitCount (qmaSparseCircuit c))).map (qubitCell c)

def referenceCells (c : QMACircuit) : List (ℕ × ℕ) :=
  (List.range (referenceCount (qmaSparseCircuit c))).map (termCell c)

def value (c : QMACircuit) : QuantumOrderedCellProgram.State :=
  (qubitCells c,QuantumOrderedCellProgram.anchors patternCount (referenceCells c))

theorem patternCount_eq : patternCount=4096 := by
  norm_num [patternCount,Pattern,Fintype.card_fun]

theorem gateCell_actual (c : QMACircuit) (t : Fin (qmaSparseCircuit c).gates.length) :
    gateCell c t.val=encodeCell (qmaSparseGateCell c t) := by
  unfold gateCell
  rw [List.headD_eq_head?_getD,List.head?_drop]
  rw [List.getElem?_eq_getElem (by rw [QuantumSweepCells.value_length]; exact t.isLt)]
  simp only [QuantumSweepCells.value_actual,List.getElem_map,encodeCell,
    qmaSparseGateCell,qmaSparseCell,Fin.val_cast,Option.getD_some]

theorem referenceCell_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (i : Fin (qmaHistoryReferenceWork (qmaSparseCircuit c)+1)) :
    referenceCell c i.val=encodeCell (qmaOrderedSparseReferenceCell c hT i) := by
  unfold referenceCell
  rw [orderedAt_actual _ hT i,time_encode _ hT]
  exact gateCell_actual c _

theorem qubitCell_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (q : QuantumOrderedSupport.Qubit (qmaSparseCircuit c)) :
    qubitCell c (QuantumOrderedSupport.siteNumber (qmaSparseCircuit c) q)=
      encodeCell (qmaOrderedQubitCell c hT q) := by
  rcases q with i | (b | w)
  · have hi : i.val<referenceWork (qmaSparseCircuit c)+1 := by
      simpa only [referenceWork_eq] using i.isLt
    simp only [qubitCell,QuantumOrderedSupport.siteNumber,hi,ite_true,
      qmaOrderedQubitCell,Sum.elim_inl]
    exact referenceCell_actual c hT i
  · change (if qmaHistoryReferenceWork (qmaSparseCircuit c)+1+b.val<
        qmaHistoryReferenceWork (qmaSparseCircuit c)+1 then _ else _)=_
    rw [ite_eq_right (by omega)]
    simp only [QuantumOrderedSupport.siteNumber,referenceWork_eq,Nat.add_sub_cancel_left]
    change (if b.val<(qmaSparseCircuit c).gates.length+2 then _ else _)=_
    rw [ite_eq_left b.isLt]
    exact gateCell_actual c (qmaClockAnchorIndex _ hT b)
  · have hnot : ¬qmaHistoryReferenceWork (qmaSparseCircuit c)+1+
        ((qmaSparseCircuit c).gates.length+2)+w.val<
        referenceWork (qmaSparseCircuit c)+1 := by rw [referenceWork_eq]; omega
    have hd : qmaHistoryReferenceWork (qmaSparseCircuit c)+1+
        ((qmaSparseCircuit c).gates.length+2)+w.val-
        (referenceWork (qmaSparseCircuit c)+1)=
        (qmaSparseCircuit c).gates.length+2+w.val := by rw [referenceWork_eq]; omega
    simp only [qubitCell,QuantumOrderedSupport.siteNumber,hnot,ite_false,hd]
    rw [ite_eq_right (by omega),Nat.add_sub_cancel_left]
    rfl

theorem termCell_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork (qmaSparseCircuit c))) :
    termCell c ((reference (qmaSparseCircuit c)).symm a).val=
      encodeCell (qmaOrderedTermCell c hT a) := by
  cases a with
  | inl i =>
    change referenceCell c (if i.val<referenceWork (qmaSparseCircuit c)+1
      then i.val else _)=_
    rw [ite_eq_left (by simpa only [referenceWork_eq] using i.isLt)]
    exact referenceCell_actual c hT i
  | inr i =>
    change referenceCell c (if qmaHistoryReferenceWork (qmaSparseCircuit c)+1+i.val<
      qmaHistoryReferenceWork (qmaSparseCircuit c)+1
      then qmaHistoryReferenceWork (qmaSparseCircuit c)+1+i.val
      else qmaHistoryReferenceWork (qmaSparseCircuit c)+1+i.val-
        (qmaHistoryReferenceWork (qmaSparseCircuit c)+1))=_
    rw [ite_eq_right (by omega),Nat.add_sub_cancel_left]
    exact referenceCell_actual c hT i.castSucc

theorem qubitCells_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) :
    qubitCells c=List.ofFn (fun i : Fin (qubitCount (qmaSparseCircuit c)) =>
      encodeCell (qmaOrderedQubitCell c hT (qubits (qmaSparseCircuit c) i))) := by
  apply List.ext_getElem
  · simp only [qubitCells,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    simp only [qubitCells,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    let j : Fin (qubitCount (qmaSparseCircuit c)) := ⟨i,by
      simpa only [List.length_ofFn] using hj⟩
    have he := congrFun (qubits_index (qmaSparseCircuit c)) (qubits (qmaSparseCircuit c) j)
    simp only [QuantumOrderedLabelTable.index,Equiv.symm_apply_apply] at he
    simpa only [←he] using qubitCell_actual c hT (qubits (qmaSparseCircuit c) j)

theorem referenceCells_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) :
    referenceCells c=List.ofFn (fun i : Fin (referenceCount (qmaSparseCircuit c)) =>
      encodeCell (qmaOrderedTermCell c hT (reference (qmaSparseCircuit c) i))) := by
  apply List.ext_getElem
  · simp only [referenceCells,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    simp only [referenceCells,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    let j : Fin (referenceCount (qmaSparseCircuit c)) := ⟨i,by
      simpa only [List.length_ofFn] using hj⟩
    simpa only [Equiv.symm_apply_apply] using
      termCell_actual c hT (reference (qmaSparseCircuit c) j)

private theorem sourceTerms_first (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (referenceCount c*patternCount)) :
    (QuantumPaddedLabelProgram.sourceTerms c hT i).1=
      reference c (finProdFinEquiv.symm i).1 := by
  simp only [QuantumPaddedLabelProgram.sourceTerms,Equiv.trans_apply,
    Equiv.prodShear_apply]

private theorem anchors_source (c : QMACircuit) (hT : 0<c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c) → ℕ × ℕ) :
    QuantumOrderedCellProgram.anchors patternCount
      (List.ofFn (fun i : Fin (referenceCount c) => a (reference c i)))=
      List.ofFn (fun i : Fin (referenceCount c*patternCount) =>
        a (QuantumPaddedLabelProgram.sourceTerms c hT i).1) := by
  rw [QuantumOrderedCellProgram.anchors_ofFn]
  rw [←QuantumOrderedLabelTable.product_table (fun p :
    Fin (referenceCount c) × Fin patternCount => a (reference c p.1))]
  apply congrArg List.ofFn
  funext i
  rw [sourceTerms_first]

theorem value_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) :
    value c=QuantumOrderedCellTable.table (qubits (qmaSparseCircuit c))
      (QuantumPaddedLabelProgram.sourceTerms (qmaSparseCircuit c) hT)
      (fun q => encodeCell (qmaOrderedQubitCell c hT q))
      (fun a => encodeCell (qmaOrderedTermCell c hT a.1)) := by
  apply Prod.ext
  · exact qubitCells_actual c hT
  · change QuantumOrderedCellProgram.anchors patternCount (referenceCells c)=_
    rw [referenceCells_actual c hT]
    dsimp only [QuantumOrderedCellTable.table]
    exact anchors_source (qmaSparseCircuit c) hT (fun a => encodeCell (qmaOrderedTermCell c hT a))

end ContinuumCoulomb.QuantumHistoryCells

end

end OAI
