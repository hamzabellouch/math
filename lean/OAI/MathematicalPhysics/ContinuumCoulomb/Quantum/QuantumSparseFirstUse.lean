import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFirstUseSites

namespace OAI

/-! First-use input checks inherit the actual sweep geometry and constant congestion. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaSparseTags_length (c : QMACircuit) :
    (qmaSparseTags c).length = (qmaSparseCircuit c).gates.length := by
  have h := congrArg List.length (qmaSparseTags_gates c)
  simpa only [List.length_map] using h

def qmaSparseTime (c : QMACircuit) (t : Fin (qmaSparseTags c).length) :
    Fin (qmaSparseCircuit c).gates.length := t.cast (qmaSparseTags_length c)

def qmaSparseCell (c : QMACircuit) (t : Fin (qmaSparseTags c).length) :
    QMAGridCell (qmaNearestCircuit c).gates.length c.work := (qmaSparseTags c)[t.val].2

theorem qmaSparseTag_gate (c : QMACircuit) (t : Fin (qmaSparseTags c).length) :
    (qmaSparseTags c)[t.val].1 = (qmaSparseCircuit c).gates[(qmaSparseTime c t).val] := by
  have ht : t.val < (qmaSparseCircuit c).gates.length := by
    rw [←qmaSparseTags_length]
    exact t.isLt
  have hm : ((qmaSparseTags c)[t.val]?).map Prod.fst = (qmaSparseCircuit c).gates[t.val]? := by
    rw [←List.getElem?_map,qmaSparseTags_gates]
  simpa only [List.getElem?_eq_getElem t.isLt,List.getElem?_eq_getElem ht,
    Option.map_some,Option.some.injEq,qmaSparseTime,Fin.val_cast] using hm

def qmaSparseCellTimes (c : QMACircuit)
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) : Finset (Fin (qmaSparseTags c).length) :=
  Finset.univ.filter (fun t => qmaSparseCell c t = p)

theorem qmaSparseCellTimes_card (c : QMACircuit)
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    (qmaSparseCellTimes c p).card ≤ 4 := by
  have he := qmaList_filter_index_card (qmaSparseTags c) (fun q => decide (q.2 = p))
  change (Finset.univ.filter (fun t : Fin (qmaSparseTags c).length =>
    (qmaSparseTags c)[t.val].2 = p)).card ≤ 4
  simpa only [decide_eq_true_eq] using he.trans_le (qmaSparseTags_count c p)

def qmaSparseInitialCellSites (c : QMACircuit)
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) : Finset (Fin ((qmaSparseCircuit c).work+1)) :=
  (qmaSparseCellTimes c p).biUnion (fun t => qmaFirstUseSites (qmaSparseCircuit c) (qmaSparseTime c t))

theorem qmaSparseInitialCellSites_card (c : QMACircuit)
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    (qmaSparseInitialCellSites c p).card ≤ 8 := by
  calc
    _ ≤ ∑ t ∈ qmaSparseCellTimes c p,
        (qmaFirstUseSites (qmaSparseCircuit c) (qmaSparseTime c t)).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ qmaSparseCellTimes c p, 2 :=
      Finset.sum_le_sum (fun t _ => qmaFirstUseSites_card _ _)
    _ = (qmaSparseCellTimes c p).card*2 := by simp
    _ ≤ 8 := by have := qmaSparseCellTimes_card c p; omega

theorem qmaSparseFirstUse_located (c : QMACircuit) (hc : c.WellFormed)
    (t : Fin (qmaSparseTags c).length) (i : Fin ((qmaSparseCircuit c).work+1))
    (hi : i ∈ qmaFirstUseSites (qmaSparseCircuit c) (qmaSparseTime c t)) :
    ∃ r : Fin ((qmaNearestCircuit c).gates.length+1), ∃ j : Fin (c.work+1),
      i = qmaGridQubit (qmaNearestCircuit c).gates.length c.work r j ∧
      (qmaSparseCell c t).1.val ≤ r.val ∧ r.val ≤ (qmaSparseCell c t).1.val+1 ∧
      j.val ≤ (qmaSparseCell c t).2.val+1 ∧ (qmaSparseCell c t).2.val ≤ j.val+1 := by
  have hs := qmaFirstUseSites_subset (qmaSparseCircuit c) (qmaSparseTime c t) hi
  rw [←qmaSparseTag_gate] at hs
  exact qmaSparseTags_located c hc _ (List.getElem_mem t.isLt) i hs

theorem qmaSparseInitialCellSites_cover (c : QMACircuit)
    (hne : (qmaNearestCircuit c).gates ≠ []) (i : Fin ((qmaSparseCircuit c).work+1)) :
    ∃ p, i ∈ qmaSparseInitialCellSites c p := by
  have ht := qmaSweepFirstUse_lt (qmaNearestCircuit c) hne i
  let t : Fin (qmaSparseTags c).length :=
    ⟨qmaFirstUse (qmaSparseCircuit c) i,by rw [qmaSparseTags_length]; exact ht⟩
  refine ⟨qmaSparseCell c t,Finset.mem_biUnion.mpr ⟨t,?_,?_⟩⟩
  · simp [qmaSparseCellTimes]
  · simp only [qmaFirstUseSites,Finset.mem_filter,Finset.mem_univ,true_and]
    rfl

end ContinuumCoulomb

end

end OAI
