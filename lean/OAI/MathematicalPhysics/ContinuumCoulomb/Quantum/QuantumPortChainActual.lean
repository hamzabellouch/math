import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortChainProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingInputActual
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedPortChain

namespace OAI

/-! The literal port-chain program returns precisely the sites used by the
physical subdivision construction, including its two endpoint centers. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortChainProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

theorem lookup_support {u v : Pair} (p : qmaSquareGrid.Walk u v) (k : ℕ)
    (hk : k ≤ p.length) : QuantumPathVisitProgram.lookup p.support k = p.getVert k := by
  unfold QuantumPathVisitProgram.lookup
  rw [List.headD_eq_head?_getD,List.head?_drop,← p.getVert_eq_support_getElem? hk]
  rfl

theorem point_eq (xs : List Pair) (p : ℕ → Pair) (L : ℕ)
    (hlen : xs.length = L+1) (hp : ∀ i ≤ L, QuantumPathVisitProgram.lookup xs i = p i)
    (k : ℕ) (hk : k ≤ 2*L+1) : point xs k = qmaPortChain p L k := by
  have hlen' : xs.length-1 = L := by omega
  unfold point
  rw [hlen']
  unfold qmaPortChain
  split_ifs with hzero hlast
  · rw [hp 0 (by omega)]
  · rw [hp L le_rfl]
  · have hi := qmaPortNeighborIndex_bounds (L := L) (by omega : 0 < k)
      (by omega : k < 2*L+1)
    unfold qmaRoutePort
    rw [hp _ hi.1,hp _ hi.2]

theorem value_support {u v : Pair} (p : qmaSquareGrid.Walk u v) :
    value p.support = (List.range (2*p.length+2)).map (qmaPortChain p.getVert p.length) := by
  unfold value
  rw [p.length_support]
  simp only [Nat.add_sub_cancel]
  apply List.map_congr_left
  intro k hk
  have hk' : k < 2*p.length+2 := List.mem_range.mp hk
  exact point_eq p.support p.getVert p.length p.length_support
    (lookup_support p) k (by omega)

def routed (A B : ℕ) (x : QuantumRoutingInputProgram.Input) : List Pair :=
  value (QuantumBufferedListProgram.path A B (QuantumRoutingInputProgram.value A B x))

noncomputable opaque routedProgram (A B : ℕ) :
    Procedure QuantumRoutingInputProgram.inputCode (listCode pairCode) (routed A B) :=
  program.comp (QuantumRoutingInputProgram.pathProgram A B)

def allRouted (A B : ℕ) (d : QuantumRoutingInputProgram.Data) : List (List Pair) :=
  (List.range d.2.length).map (fun i => routed A B (i,d))

noncomputable opaque allRoutedProgram (A B : ℕ) :
    Procedure QuantumRoutingInputProgram.dataCode (listCode (listCode pairCode))
      (allRouted A B) := by
  let edges : Procedure QuantumRoutingInputProgram.dataCode (listCode pairCode)
      (fun d => d.2) := Procedure.second
    (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode)
  let n : Procedure QuantumRoutingInputProgram.dataCode unaryCode (fun d => d.2.length) :=
    (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pairCode (0,0)).comp edges
  let tab : Procedure (prodCode unaryCode QuantumRoutingInputProgram.dataCode)
      (listCode (listCode pairCode))
      (fun x => (List.range x.1).map (fun i => routed A B (i,x.2))) :=
    Procedure.tabulate (f := fun d i => routed A B (i,d)) [] (routedProgram A B)
  exact (tab.comp (n.pair (Procedure.identity QuantumRoutingInputProgram.dataCode))).congrFun
    (by intro d; rfl)

@[simp] theorem allRouted_length (A B : ℕ) (d : QuantumRoutingInputProgram.Data) :
    (allRouted A B d).length = d.2.length := by
  simp only [allRouted,List.length_map,List.length_range]

theorem allRouted_get (A B : ℕ) (d : QuantumRoutingInputProgram.Data) (i : Fin d.2.length) :
    (allRouted A B d)[i.val]'(by simpa only [allRouted_length] using i.isLt) =
      routed A B (i.val,d) := by
  simp only [allRouted,List.getElem_map,List.getElem_range]

theorem routed_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    routed A B ((labels e).val,QuantumRoutingInputProgram.actualData M labels) =
      (List.range (2*(M.withOrdinalSlots labels).coarseLength hd e+2)).map
        (qmaPortChain ((M.withOrdinalSlots labels).coarseRoute hd e)
          ((M.withOrdinalSlots labels).coarseLength hd e)) := by
  exact (congrArg value (QuantumRoutingInputProgram.path_actual M labels hA hd e)).trans
    (value_support ((M.withOrdinalSlots labels).bufferedPath hd e).val)

theorem routed_actual_length {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    (routed A B ((labels e).val,QuantumRoutingInputProgram.actualData M labels)).length =
      2*(M.withOrdinalSlots labels).coarseLength hd e+2 := by
  exact (congrArg List.length (routed_actual M labels hA hd e)).trans
    (by simp only [List.length_map,List.length_range])

end ContinuumCoulomb.QuantumPortChainProgram

end

end OAI
