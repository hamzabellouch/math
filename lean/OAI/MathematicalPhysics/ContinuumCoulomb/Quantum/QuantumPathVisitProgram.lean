import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumComputedRoutingTable
import OAI.Computability.QuantumFactoring.BitStackListIndex

namespace OAI

/-! Encoded path lists determine the two directional ports of every internal
cell. The output contains both orientations, as required by the route table. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPathVisitProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumRoutingTable

def lookup (xs : List Pair) (i : ℕ) : Pair := (xs.drop i).headD (0,0)

def visit (xs : List Pair) (i : ℕ) : Visit :=
  let p := lookup xs (i+1)
  (p,((qmaGridNeighborIndex p (lookup xs i)).val,
      (qmaGridNeighborIndex p (lookup xs (i+2))).val))

def both (v : Visit) : List Visit := [v,(v.1,v.2.swap)]

def visits (xs : List Pair) : List Visit :=
  ((List.range (xs.length-2)).map (fun i => both (visit xs i))).flatten

noncomputable def neighborIndexProgram :
    Procedure (prodCode pairCode pairCode) Nat.bits
      (fun x => (qmaGridNeighborIndex x.1 x.2).val) := by
  let p := Procedure.first pairCode pairCode
  let q := Procedure.second pairCode pairCode
  let px := (Procedure.first Nat.bits Nat.bits).comp p
  let py := (Procedure.second Nat.bits Nat.bits).comp p
  let qx := (Procedure.first Nat.bits Nat.bits).comp q
  let qy := (Procedure.second Nat.bits Nat.bits).comp q
  let plus (v : Procedure (prodCode pairCode pairCode) Nat.bits (fun x => x.1.1)) :=
    Procedure.binaryAdd.comp (v.pair (Procedure.constant _ Nat.bits 1))
  let px1 := plus px
  let py1 := Procedure.binaryAdd.comp (py.pair (Procedure.constant _ Nat.bits 1))
  let qx1 := Procedure.binaryAdd.comp (qx.pair (Procedure.constant _ Nat.bits 1))
  exact (Procedure.conditional (Procedure.binaryEq.comp (qx.pair px1))
    (Procedure.constant _ Nat.bits 0)
    (Procedure.conditional (Procedure.binaryEq.comp (qy.pair py1))
      (Procedure.constant _ Nat.bits 1)
      (Procedure.conditional (Procedure.binaryEq.comp (qx1.pair px))
        (Procedure.constant _ Nat.bits 2) (Procedure.constant _ Nat.bits 3)))).congrFun (by
          intro x
          simp only [Function.comp_apply,qmaGridNeighborIndex,decide_eq_true_eq]
          split_ifs <;> rfl)

abbrev Input := ℕ × List Pair
def inputCode : Input → List Bool := prodCode unaryCode (listCode pairCode)

noncomputable def visitProgram : Procedure inputCode visitCode (fun x => visit x.2 x.1) := by
  let i := Procedure.unaryToBits.comp (Procedure.first unaryCode (listCode pairCode))
  let xs := Procedure.second unaryCode (listCode pairCode)
  let get (j : ℕ) := (Procedure.listGet pairCode (0,0)).comp
    ((Procedure.binaryAdd.comp (i.pair (Procedure.constant inputCode Nat.bits j))).pair xs)
  let center := get 1
  let left := neighborIndexProgram.comp (center.pair (get 0))
  let right := neighborIndexProgram.comp (center.pair (get 2))
  exact (center.pair (left.pair right)).congrFun (by
    intro x
    simp only [Function.comp_apply,id_eq,Nat.add_zero,visit,lookup])

noncomputable def bothProgram : Procedure visitCode (listCode visitCode) both := by
  let v := Procedure.identity visitCode
  let rev := (Procedure.first pairCode pairCode).pair
    ((Procedure.swap Nat.bits Nat.bits).comp (Procedure.second pairCode pairCode))
  exact (Procedure.listCons visitCode).comp (v.pair
    ((Procedure.listCons visitCode).comp
      (rev.pair (Procedure.constant visitCode (listCode visitCode) []))))

noncomputable def visitsProgram : Procedure (listCode pairCode) (listCode visitCode) visits := by
  let count := Procedure.unarySub.comp
    ((ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pairCode (0,0)).pair
      (Procedure.constant (listCode pairCode) unaryCode 2))
  let tab := (Procedure.tabulate (f := fun xs i => both (visit xs i)) []
    (bothProgram.comp visitProgram)).comp
    (count.pair (Procedure.identity (listCode pairCode)))
  exact (QuantumRawExchange.flattenProgram visitCode ((0,0),(0,0))).comp tab

end ContinuumCoulomb.QuantumPathVisitProgram

end

end OAI
