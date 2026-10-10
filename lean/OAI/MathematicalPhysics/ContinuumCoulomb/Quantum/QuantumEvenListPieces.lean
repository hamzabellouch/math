import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumInflatedListProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPlanarRouteData

namespace OAI

/-! Literal reserved-leaf and tail arrays for an even route subdivision. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEvenListPieces
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

def leaf (xs : List Pair) : Pair := qmaRouteLeaf
  (QuantumForkGridProgram.lookup xs 0)
  (qmaGridNeighborIndex (QuantumForkGridProgram.lookup xs 0)
    (QuantumForkGridProgram.lookup xs 1))
def fresh (xs : List Pair) : List Pair :=
  [QuantumInflatedListProgram.point (1,xs),leaf xs]
def paths (xs : List Pair) : List (List Pair) :=
  [fresh xs,[QuantumInflatedListProgram.point (0,xs),
    QuantumInflatedListProgram.point (1,xs)],
    ((QuantumInflatedListProgram.value xs).drop 1).reverse]

noncomputable opaque leafProgram : Procedure (listCode pairCode) pairCode leaf := by
  let get (k : ℕ) := (Procedure.listGet pairCode (0,0)).comp
    ((Procedure.constant (listCode pairCode) Nat.bits k).pair
      (Procedure.identity (listCode pairCode)))
  exact QuantumRouteLeafCode.selectedLeafProgram.comp ((get 0).pair (get 1))

noncomputable def pointProgram (k : ℕ) : Procedure (listCode pairCode) pairCode
    (fun xs => QuantumInflatedListProgram.point (k,xs)) :=
  QuantumInflatedListProgram.pointProgram.comp
    ((Procedure.constant (listCode pairCode) Nat.bits k).pair
      (Procedure.identity (listCode pairCode)))

private noncomputable def pairList {α : Type} (ea : α → List Bool)
    {f g : α → Pair} (p : Procedure ea pairCode f) (q : Procedure ea pairCode g) :
    Procedure ea (listCode pairCode) (fun x => [f x,g x]) :=
  (Procedure.listCons pairCode).comp (p.pair
    ((Procedure.listCons pairCode).comp (q.pair (Procedure.constant ea (listCode pairCode) []))))

noncomputable opaque freshProgram : Procedure (listCode pairCode) (listCode pairCode) fresh :=
  pairList (listCode pairCode) (pointProgram 1) leafProgram

noncomputable opaque pathsProgram : Procedure (listCode pairCode)
    (listCode (listCode pairCode)) paths := by
  let second := pairList (listCode pairCode) (pointProgram 0) (pointProgram 1)
  let third := (Procedure.listReverse pairCode (0,0)).comp
    ((Procedure.listDrop pairCode).comp
      ((Procedure.constant (listCode pairCode) Nat.bits 1).pair
        QuantumInflatedListProgram.program))
  exact (Procedure.listCons (listCode pairCode)).comp (freshProgram.pair
    ((Procedure.listCons (listCode pairCode)).comp (second.pair
      ((Procedure.listCons (listCode pairCode)).comp
        (third.pair (Procedure.constant (listCode pairCode) (listCode (listCode pairCode)) []))))))

theorem tail_reverse (p : ℕ → Pair) (n : ℕ) :
    (((List.range (n+1)).map p).drop 1).reverse=
      (List.range n).map (fun k => p (n-k)) := by
  apply List.ext_getElem
  · simp only [List.length_reverse,List.length_drop,List.length_map,List.length_range]
    omega
  · intro i hi hj
    have hi' : i<n := by simpa only [List.length_map,List.length_range] using hj
    rw [List.getElem_reverse]
    simp only [List.getElem_drop,List.getElem_map,List.getElem_range,
      List.length_drop,List.length_map,List.length_range]
    congr 1
    omega

theorem leaf_range (p : ℕ → Pair) (L : ℕ) (hL : 0<L) :
    leaf ((List.range (L+1)).map p)=qmaRouteLeaf (p 0) (qmaGridNeighborIndex (p 0) (p 1)) := by
  unfold leaf
  rw [QuantumInflatedListProgram.lookup_range p (L+1) 0 (by omega),
    QuantumInflatedListProgram.lookup_range p (L+1) 1 (by omega)]

theorem fresh_range (p : ℕ → Pair) (L : ℕ) (hL : 0<L) :
    fresh ((List.range (L+1)).map p)=
      [qmaInflatedPoint p 1,qmaRouteLeaf (p 0) (qmaGridNeighborIndex (p 0) (p 1))] := by
  unfold fresh
  rw [QuantumInflatedListProgram.point_range p L 1 (by omega),leaf_range p L hL]

theorem paths_range (p : ℕ → Pair) (L : ℕ) (hL : 0<L) :
    paths ((List.range (L+1)).map p)=
      [[qmaInflatedPoint p 1,qmaRouteLeaf (p 0) (qmaGridNeighborIndex (p 0) (p 1))],
       [qmaInflatedPoint p 0,qmaInflatedPoint p 1],
       (List.range (8*L)).map (fun k => qmaInflatedPoint p (8*L-k))] := by
  unfold paths
  rw [fresh_range p L hL,QuantumInflatedListProgram.point_range p L 0 (by omega),
    QuantumInflatedListProgram.point_range p L 1 (by omega),
    QuantumInflatedListProgram.value_range,tail_reverse]

end ContinuumCoulomb.QuantumEvenListPieces

end

end OAI
