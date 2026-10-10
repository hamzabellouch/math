import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListCells
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListScale

namespace OAI

/-! The coarse-cell labels are emitted by literal polynomial finite-list
programs, using the same ordered pair catalog as the physical fork compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram

abbrev CellInput := State × List ℕ
def cellInputCode : CellInput → List Bool := prodCode stateCode (listCode Nat.bits)
def cellQueryCode : (ℕ × CellInput) → List Bool := prodCode Nat.bits cellInputCode

def cellAt (xs : List ℕ) (i : ℕ) : ℕ := (xs.drop i).headD 0

noncomputable def nextCellProgram : Procedure cellQueryCode Nat.bits
    (fun x => nextCell x.2.1 (cellAt x.2.2) x.1) := by
  let v := Procedure.first Nat.bits cellInputCode
  let env := Procedure.second Nat.bits cellInputCode
  let s := (Procedure.first stateCode (listCode Nat.bits)).comp env
  let xs := (Procedure.second stateCode (listCode Nat.bits)).comp env
  let n := Procedure.unaryToBits.comp (countProgram.comp s)
  let before := Procedure.binaryLt.comp (v.pair n)
  let pair := Procedure.binaryDiv.comp
    ((Procedure.binarySub.comp (v.pair n)).pair (Procedure.constant cellQueryCode Nat.bits 2))
  let ps := catalogProgram.comp (groupsProgram.comp s)
  let center := (Procedure.first Nat.bits pairCode).comp
    ((Procedure.listGet taggedCode (0,((0,0),(0,0)))).comp (pair.pair ps))
  let target := Procedure.conditional before v center
  exact ((Procedure.listGet Nat.bits 0).comp (target.pair xs)).congrFun (by
    intro x
    change cellAt x.2.2 (if decide (x.1<x.2.1.1) then x.1 else
      (((catalog x.2.1.2.2.2).drop ((x.1-x.2.1.1)/2)).headD (0,((0,0),(0,0)))).1) = _
    unfold nextCell
    by_cases h : x.1<x.2.1.1 <;> simp [h])

def nextCells (x : CellInput) : List ℕ :=
  (List.range (x.1.1+2*pairCount x.1.2.2.2)).map (nextCell x.1 (cellAt x.2))

noncomputable def nextCellsProgram : Procedure cellInputCode (listCode Nat.bits) nextCells := by
  let s := Procedure.first stateCode (listCode Nat.bits)
  let n := countProgram.comp s
  let pairs := pairCountProgram.comp (groupsProgram.comp s)
  let count := Procedure.unaryAdd.comp (n.pair (Procedure.unaryAdd.comp (pairs.pair pairs)))
  let query : Procedure (prodCode unaryCode cellInputCode) cellQueryCode
      (fun x => (x.1,x.2)) :=
    (Procedure.unaryToBits.comp (Procedure.first unaryCode cellInputCode)).pair
      (Procedure.second unaryCode cellInputCode)
  let entry := nextCellProgram.comp query
  exact ((Procedure.tabulate (f := fun x i => nextCell x.1 (cellAt x.2) i) 0 entry).comp
    (count.pair (Procedure.identity cellInputCode))).congrFun (by
      intro x
      change (List.range (x.1.1+(pairCount x.1.2.2.2+pairCount x.1.2.2.2))).map _=nextCells x
      simp only [nextCells,two_mul,id_eq])

end ContinuumCoulomb.QuantumForkList

end

end OAI
