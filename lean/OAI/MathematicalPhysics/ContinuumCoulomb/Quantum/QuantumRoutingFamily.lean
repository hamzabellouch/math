import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkRoutingPaths
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumComputedRouteSelector

namespace OAI

/-! Literal enumeration of every coarse route and source center. These are
the exact lists consumed by the finite crossing and permission tables. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingFamily
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumRoutingInputProgram

def placed (A B : ℕ) (x : Input) : Pair :=
  qmaBufferedCellPoint (9*B+3)
    (QuantumSpatialSlotProgram.fineSite A (x.1,x.2.1.1)) (17,17)

noncomputable opaque placedProgram (A B : ℕ) : Procedure inputCode pairCode (placed A B) := by
  let cells := (Procedure.first (listCode pairCode) (listCode pairCode)).comp
    ((Procedure.first (prodCode (listCode pairCode) (listCode pairCode))
      (listCode pairCode)).comp dataProgram)
  let fine := (QuantumSpatialSlotProgram.fineSiteProgram A).comp (indexProgram.pair cells)
  exact (QuantumEndpointListProgram.translateProgram B).comp
    (fine.pair (Procedure.constant inputCode pairCode (17,17)))

def positions (A B : ℕ) (d : Data) : List Pair :=
  (List.range d.1.1.length).map (fun i => placed A B (i,d))

noncomputable opaque positionsProgram (A B : ℕ) : Procedure dataCode (listCode pairCode)
    (positions A B) := by
  let cells : Procedure dataCode (listCode pairCode) (fun d => d.1.1) :=
    (Procedure.first (listCode pairCode) (listCode pairCode)).comp
    (Procedure.first (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode))
  let count : Procedure dataCode unaryCode (fun d => d.1.1.length) :=
    (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pairCode (0,0)).comp cells
  let tab : Procedure inputCode (listCode pairCode)
      (fun x => (List.range x.1).map (fun i => placed A B (i,x.2))) :=
    Procedure.tabulate (f := fun d i => placed A B (i,d)) (0,0) (placedProgram A B)
  exact (tab.comp (count.pair (Procedure.identity dataCode))).congrFun (by intro d; rfl)

def coarse (A B : ℕ) (d : Data) : List (List Pair) :=
  (List.range d.2.length).map (fun i =>
    QuantumBufferedListProgram.path A B (value A B (i,d)))

noncomputable opaque coarseProgram (A B : ℕ) : Procedure dataCode (listCode (listCode pairCode))
    (coarse A B) := by
  let edges : Procedure dataCode (listCode pairCode) (fun d => d.2) :=
    Procedure.second (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode)
  let count : Procedure dataCode unaryCode (fun d => d.2.length) :=
    (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pairCode (0,0)).comp edges
  let tab : Procedure inputCode (listCode (listCode pairCode))
      (fun x => (List.range x.1).map (fun i =>
        QuantumBufferedListProgram.path A B (value A B (i,x.2)))) :=
    Procedure.tabulate
      (f := fun d i => QuantumBufferedListProgram.path A B (value A B (i,d))) [] (pathProgram A B)
  exact (tab.comp (count.pair (Procedure.identity dataCode))).congrFun (by intro d; rfl)

def table (A B : ℕ) (d : Data) : QuantumPathTable.Input :=
  (positions A B d,coarse A B d)

noncomputable def tableProgram (A B : ℕ) :
    Procedure dataCode QuantumPathTable.inputCode (table A B) :=
  (positionsProgram A B).pair (coarseProgram A B)

theorem placed_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (q : Fin M.n) :
    placed A B (q.val,actualData M labels) = (M.withOrdinalSlots labels).placedVertex q := by
  unfold placed actualData
  rw [QuantumSpatialSlotProgram.fineSite_actual M labels q]
  rfl

theorem positions_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) :
    positions A B (actualData M labels) = List.ofFn (M.withOrdinalSlots labels).placedVertex := by
  apply List.ext_getElem
  · simp only [positions,actualData,List.length_map,List.length_range,List.length_ofFn]
    rfl
  · intro i hi hj
    have hi' : i < M.n := by simpa only [List.length_ofFn,
      QMASpatialExchangeModel.withOrdinalSlots] using hj
    simp only [positions,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact placed_actual M labels ⟨i,hi'⟩

theorem coarse_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) :
    coarse A B (actualData M labels) = List.ofFn (fun e : Fin m =>
      ((M.withOrdinalSlots labels).bufferedPath hd (labels.symm e)).val.support) := by
  apply List.ext_getElem
  · simp only [coarse,actualData,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    have hi' : i < m := by simpa only [List.length_ofFn] using hj
    have h := path_actual M labels hA hd (labels.symm ⟨i,hi'⟩)
    simpa only [coarse,List.getElem_map,List.getElem_range,List.getElem_ofFn,
      Equiv.apply_symm_apply] using h

private theorem support_range {u v : Pair} (p : qmaSquareGrid.Walk u v) :
    p.support = (List.range (p.length+1)).map p.getVert := by
  apply List.ext_getElem
  · simp only [p.length_support,List.length_map,List.length_range]
  · intro i hi hj
    have hi' : i ≤ p.length := by
      simp only [p.length_support] at hi
      omega
    simpa only [List.getElem_map,List.getElem_range] using
      (p.getVert_eq_support_getElem hi').symm

theorem table_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) :
    table A B (actualData M labels) =
      (List.ofFn (M.withOrdinalSlots labels).placedVertex,
        List.ofFn (fun e : Fin m =>
          ((M.withOrdinalSlots labels).portRouteData hA hd).routeList (labels.symm e))) := by
  unfold table
  rw [positions_actual,coarse_actual M labels hA hd]
  apply congrArg (Prod.mk _)
  apply congrArg List.ofFn
  funext e
  exact support_range ((M.withOrdinalSlots labels).bufferedPath hd (labels.symm e)).val

end ContinuumCoulomb.QuantumRoutingFamily

end

end OAI
