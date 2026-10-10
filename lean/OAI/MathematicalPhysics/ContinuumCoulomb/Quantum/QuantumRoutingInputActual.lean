import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingInputProgram

namespace OAI

/-! The encoded cell/edge arrays evaluate to the actual buffered path of the
ordinal-slot spatial model. No arbitrary finite-fiber choice remains in this
part of the routing compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingInputProgram
open QuantumRouteCode

def actualData {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) : Data :=
  ((List.ofFn (QuantumOrdinalPlacement.coordinates M.cell),
    List.ofFn (QuantumOrdinalPlacement.coordinates (M.anchor ∘ labels.symm))),
    List.ofFn (fun i => ((M.left (labels.symm i)).val,(M.right (labels.symm i)).val)))

theorem edge_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (e : M.Term) :
    edge (actualData M labels) (labels e).val = ((M.left e).val,(M.right e).val) := by
  unfold edge actualData
  rw [QuantumOrdinalProgram.lookup_ofFn]
  simp only [Equiv.symm_apply_apply]

theorem fine_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (q : Fin M.n) :
    fine A (actualData M labels) q.val = (M.withOrdinalSlots labels).routeVertex q := by
  unfold fine actualData
  simp only [List.length_ofFn,Nat.min_eq_right q.isLt.le]
  exact QuantumSpatialSlotProgram.fineSite_actual M labels q

theorem lane_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (e : M.Term) :
    lane B ((labels e).val,actualData M labels) = ((M.withOrdinalSlots labels).laneColor e).val :=
  QuantumSpatialSlotProgram.lane_actual M labels e

theorem entry_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (e : M.Term) :
    entry B (actualData M labels) (labels e).val =
      QuantumPortRankProgram.entries (M.withOrdinalSlots labels) labels (labels e) := by
  unfold entry
  rw [edge_actual,lane_actual]
  exact (congrArg (fun t : M.Term => ((M.left t).val,(M.right t).val,
    ((M.withOrdinalSlots labels).laneColor t).val)) (labels.symm_apply_apply e)).symm

private theorem entries_ofFn (B : ℕ) (d : Data) {m : ℕ}
    (f : Fin m → QuantumPortRankProgram.Entry) (hlen : d.2.length = m)
    (h : ∀ i : Fin m, entry B d i.val = f i) : entries B d = List.ofFn f := by
  apply List.ext_getElem
  · simp only [entries,List.length_map,List.length_range,List.length_ofFn,hlen]
  · intro i hi hj
    have hi' : i < m := by simpa only [List.length_ofFn] using hj
    simpa only [entries,List.getElem_map,List.getElem_range,List.getElem_ofFn] using h ⟨i,hi'⟩

theorem entries_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) :
    entries B (actualData M labels) =
      List.ofFn (QuantumPortRankProgram.entries (M.withOrdinalSlots labels) labels) := by
  apply entries_ofFn B (actualData M labels)
    (QuantumPortRankProgram.entries (M.withOrdinalSlots labels) labels)
    (by simp only [actualData,List.length_ofFn])
  intro j
  calc
    entry B (actualData M labels) j.val =
        entry B (actualData M labels) (labels (labels.symm j)).val :=
      congrArg (fun k : Fin m => entry B (actualData M labels) k.val)
        (labels.apply_symm_apply j).symm
    _ = QuantumPortRankProgram.entries (M.withOrdinalSlots labels) labels
        (labels (labels.symm j)) := entry_actual M labels (labels.symm j)
    _ = _ := congrArg (QuantumPortRankProgram.entries (M.withOrdinalSlots labels) labels)
      (labels.apply_symm_apply j)

theorem value_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    value A B ((labels e).val,actualData M labels) =
      QuantumBufferedListProgram.actualInput (M.withOrdinalSlots labels) hd e := by
  unfold value
  rw [edge_actual,lane_actual,entries_actual]
  dsimp only
  exact congrArg₂ Prod.mk
    (congrArg₂ Prod.mk (fine_actual M labels (M.left e)) (fine_actual M labels (M.right e)))
    (congrArg (Prod.mk ((M.withOrdinalSlots labels).laneColor e).val)
      (congrArg₂ Prod.mk
        (QuantumPortRankProgram.value_actual (M.withOrdinalSlots labels) labels hA hd
          (M.left e) ⟨e,Or.inl rfl⟩)
        (QuantumPortRankProgram.value_actual (M.withOrdinalSlots labels) labels hA hd
          (M.right e) ⟨e,Or.inr rfl⟩)))

theorem path_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    QuantumBufferedListProgram.path A B (value A B ((labels e).val,actualData M labels)) =
      ((M.withOrdinalSlots labels).bufferedPath hd e).val.support := by
  exact (congrArg (QuantumBufferedListProgram.path A B)
    (value_actual M labels hA hd e)).trans
    (QuantumBufferedListProgram.path_actual (M.withOrdinalSlots labels) hd e)

end ContinuumCoulomb.QuantumRoutingInputProgram

end

end OAI
