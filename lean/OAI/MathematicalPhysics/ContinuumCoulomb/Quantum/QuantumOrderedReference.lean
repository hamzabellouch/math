import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSortedTime

namespace OAI

/-! A consecutive reference label for the time-ordered actual interaction family. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaOrderedTermEquiv (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    Fin (qmaHistoryReferenceWork c+1) ≃ QMACircuitTerm c :=
  (finCongr (qmaOrderedHistoryTerms_length c hT τ).symm).trans
    (List.Nodup.getEquivOfForallMemList _ (qmaOrderedHistoryTerms_nodup c hT τ)
      (qmaOrderedHistoryTerms_mem c hT τ))

theorem qmaOrderedTermEquiv_get (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (i : Fin (qmaHistoryReferenceWork c+1)) :
    qmaOrderedTermEquiv c hT τ i = (qmaOrderedHistoryTerms c hT τ)[i.val]'(by
      rw [qmaOrderedHistoryTerms_length]; exact i.isLt) := rfl

def qmaOrderedReferenceTime (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (i : Fin (qmaHistoryReferenceWork c+1)) : Fin c.gates.length :=
  qmaHistoryTermTime c hT τ (qmaOrderedTermEquiv c hT τ i)

theorem qmaOrderedReferenceTime_step (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (i : Fin (qmaHistoryReferenceWork c)) :
    (qmaOrderedReferenceTime c hT τ i.castSucc).val ≤
        (qmaOrderedReferenceTime c hT τ i.succ).val ∧
      (qmaOrderedReferenceTime c hT τ i.succ).val ≤
        (qmaOrderedReferenceTime c hT τ i.castSucc).val+1 := by
  let j : Fin (qmaOrderedHistoryTerms c hT τ).length :=
    i.castSucc.cast (qmaOrderedHistoryTerms_length c hT τ).symm
  let k : Fin (qmaOrderedHistoryTerms c hT τ).length :=
    i.succ.cast (qmaOrderedHistoryTerms_length c hT τ).symm
  have hjk : k.val = j.val+1 := rfl
  have hle := (qmaOrderedHistoryTerms_sorted c hT τ).rel_getElem_of_lt j.isLt k.isLt
    (by change i.val < i.val+1; omega)
  have hstep := qmaOrderedHistoryTerms_step c hT τ j k hjk
  simp only [qmaOrderedReferenceTime,qmaOrderedTermEquiv_get]
  exact ⟨hle,hstep⟩

def qmaOrderedSparseReferenceCell (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (i : Fin (qmaHistoryReferenceWork (qmaSparseCircuit c)+1)) :
    QMAGridCell (qmaNearestCircuit c).gates.length c.work :=
  qmaSparseGateCell c (qmaOrderedReferenceTime (qmaSparseCircuit c) hT
    (qmaFirstUseTime (qmaSparseCircuit c)) i)

theorem qmaOrderedSparseReferenceCell_near (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (i : Fin (qmaHistoryReferenceWork (qmaSparseCircuit c))) :
    QMAGridCellsNear (qmaOrderedSparseReferenceCell c hT i.castSucc)
      (qmaOrderedSparseReferenceCell c hT i.succ) := by
  have h := qmaOrderedReferenceTime_step (qmaSparseCircuit c) hT
    (qmaFirstUseTime (qmaSparseCircuit c)) i
  exact qmaSparseGateCells_near c _ _ (by omega) h.2

end ContinuumCoulomb

end

end OAI
