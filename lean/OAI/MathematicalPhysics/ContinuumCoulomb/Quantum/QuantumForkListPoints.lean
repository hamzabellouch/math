import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListScale

namespace OAI

/-! Literal numbering of the new active ports. A prefix sum of pair counts
gives each center its contiguous block of fresh mediator indices. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram

noncomputable def takeGroupsProgram : Procedure (prodCode Nat.bits groupsCode) groupsCode
    (fun x => x.2.take x.1) := by
  let n := Procedure.first Nat.bits groupsCode
  let gs := Procedure.second Nat.bits groupsCode
  let len := (Procedure.listLength (listCode portCode) []).comp gs
  let count := Procedure.binarySub.comp (len.pair n)
  let reverse := (Procedure.listReverse (listCode portCode) []).comp gs
  exact ((Procedure.listReverse (listCode portCode) []).comp
    ((Procedure.listDrop (listCode portCode)).comp (count.pair reverse))).congrFun (by
      intro x
      simp only [Function.comp_apply,← List.reverse_take,List.reverse_reverse])

noncomputable def pairStartProgram : Procedure (prodCode Nat.bits groupsCode) unaryCode
    (fun x => pairStart x.2 x.1) := pairCountProgram.comp takeGroupsProgram

abbrev PointInput := (ℕ × ℕ) × ℚ
def pointCode : PointInput → List Bool := prodCode (prodCode Nat.bits Nat.bits) ratCode

def freshPoint (x : PointInput) (j : ℕ) : Port := (x.1.1+2*(x.1.2+j),x.2)

noncomputable def freshPointProgram :
    Procedure (prodCode unaryCode pointCode) portCode (fun x => freshPoint x.2 x.1) := by
  let j := Procedure.unaryToBits.comp (Procedure.first unaryCode pointCode)
  let env := Procedure.second unaryCode pointCode
  let ns := (Procedure.first (prodCode Nat.bits Nat.bits) ratCode).comp env
  let n := (Procedure.first Nat.bits Nat.bits).comp ns
  let start := (Procedure.second Nat.bits Nat.bits).comp ns
  let r := (Procedure.second (prodCode Nat.bits Nat.bits) ratCode).comp env
  let offset := Procedure.binaryMul.comp
    ((Procedure.constant (prodCode unaryCode pointCode) Nat.bits 2).pair
      (Procedure.binaryAdd.comp (start.pair j)))
  exact (Procedure.binaryAdd.comp (n.pair offset)).pair r

abbrev GroupInput := ℕ × (ℚ × Groups)
def groupCode : GroupInput → List Bool := prodCode Nat.bits (prodCode ratCode groupsCode)

noncomputable def nextGroupProgram : Procedure (prodCode unaryCode groupCode) (listCode portCode)
    (fun x => nextGroup x.2.1 x.2.2.1 x.2.2.2 x.1) := by
  let i := Procedure.first unaryCode groupCode
  let env := Procedure.second unaryCode groupCode
  let n := (Procedure.first Nat.bits (prodCode ratCode groupsCode)).comp env
  let tail := (Procedure.second Nat.bits (prodCode ratCode groupsCode)).comp env
  let r := (Procedure.first ratCode groupsCode).comp tail
  let gs := (Procedure.second ratCode groupsCode).comp tail
  let ps := groupAtProgram.comp (i.pair gs)
  let count := halfProgram.comp
    ((ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength portCode (0,0)).comp ps)
  let start := Procedure.unaryToBits.comp
    (pairStartProgram.comp ((Procedure.unaryToBits.comp i).pair gs))
  let points := (Procedure.tabulate (0,0) freshPointProgram).comp
    (count.pair ((n.pair start).pair r))
  exact (Procedure.listAppend portCode (0,0)).comp (points.pair (unpairedProgram.comp ps))

noncomputable def nextGroupsProgram : Procedure groupCode groupsCode
    (fun x => (List.range x.2.2.length).map (nextGroup x.1 x.2.1 x.2.2)) := by
  let gs := (Procedure.second ratCode groupsCode).comp
    (Procedure.second Nat.bits (prodCode ratCode groupsCode))
  let count := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength (listCode portCode) []).comp gs
  exact (Procedure.tabulate (f := fun x i => nextGroup x.1 x.2.1 x.2.2 i)
    [] nextGroupProgram).comp (count.pair (Procedure.identity groupCode))

end ContinuumCoulomb.QuantumForkList

end

end OAI
