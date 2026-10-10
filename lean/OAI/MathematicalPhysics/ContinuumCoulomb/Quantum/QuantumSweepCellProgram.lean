import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSweepCells
import OAI.Computability.QuantumFactoring.BitStackListMapWith

namespace OAI

/-! A polynomial program for the exact sweep tag list.  Only unary width
and the actual gate-list length control list generation. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSweepCells
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

def pairCode : (ℕ × ℕ) → List Bool := prodCode Nat.bits Nat.bits

noncomputable opaque repeatProgram : Procedure (listCode Nat.bits) (listCode Nat.bits)
    repeatColumns := by
  let n := Procedure.identity Nat.bits
  let nil := Procedure.constant Nat.bits (listCode Nat.bits) []
  let one := (Procedure.listCons Nat.bits).comp (n.pair nil)
  let two := (Procedure.listCons Nat.bits).comp (n.pair one)
  let three := (Procedure.listCons Nat.bits).comp (n.pair two)
  exact ((QuantumRawExchange.flattenProgram Nat.bits 0).comp
    (Procedure.listMap 0 [] three)).congrFun (by intro xs; rfl)

noncomputable opaque columnsProgram : Procedure (prodCode unaryCode Nat.bits)
    (listCode Nat.bits) (fun x => columns x.1 x.2) := by
  let width := Procedure.first unaryCode Nat.bits
  let context := (Procedure.unaryToBits.comp width).pair (Procedure.second unaryCode Nat.bits)
  let env := Procedure.second unaryCode pairCode
  let w := (Procedure.first Nat.bits Nat.bits).comp env
  let order := (Procedure.second Nat.bits Nat.bits).comp env
  let index := Procedure.unaryToBits.comp (Procedure.first unaryCode pairCode)
  let entry := sweepIndexProgram.comp (w.pair (order.pair index))
  exact ((Procedure.tabulate (f := fun x i => sweepIndex x.1 x.2 i) 0 entry).comp
    ((Procedure.unarySuccessor.comp width).pair context)).congrFun (by intro x; rfl)

private noncomputable def takeProgram : Procedure (prodCode Nat.bits (listCode Nat.bits))
    (listCode Nat.bits) (fun x => x.2.take x.1) := by
  let n := Procedure.first Nat.bits (listCode Nat.bits)
  let xs := Procedure.second Nat.bits (listCode Nat.bits)
  let len := (Procedure.listLength Nat.bits 0).comp xs
  let count := Procedure.binarySub.comp (len.pair n)
  let rev := (Procedure.listReverse Nat.bits 0).comp xs
  exact ((Procedure.listReverse Nat.bits 0).comp
    ((Procedure.listDrop Nat.bits).comp (count.pair rev))).congrFun (by
      intro x
      simp only [Function.comp_apply,← List.reverse_take,List.reverse_reverse])

noncomputable opaque rowColumnsProgram : Procedure stageInputCode (listCode Nat.bits)
    (fun x => rowColumns x.2.1 (x.1-1-x.2.2.1) x.2.2.2) := by
  let rows := Procedure.first Nat.bits (prodCode unaryCode (prodCode Nat.bits gateCode))
  let tail := Procedure.second Nat.bits (prodCode unaryCode (prodCode Nat.bits gateCode))
  let width := (Procedure.first unaryCode (prodCode Nat.bits gateCode)).comp tail
  let rest := (Procedure.second unaryCode (prodCode Nat.bits gateCode)).comp tail
  let start := (Procedure.first Nat.bits gateCode).comp rest
  let gate := (Procedure.second Nat.bits gateCode).comp rest
  let order := Procedure.binarySub.comp
    ((Procedure.binarySub.comp (rows.pair
      (Procedure.constant stageInputCode Nat.bits 1))).pair start)
  let wb := Procedure.unaryToBits.comp width
  let xs := columnsProgram.comp (width.pair order)
  let cut := rowCutProgram.comp (wb.pair (order.pair gate))
  let front := repeatProgram.comp (takeProgram.comp (cut.pair xs))
  let back := repeatProgram.comp ((Procedure.listDrop Nat.bits).comp (cut.pair xs))
  let arrival := sweepIndexProgram.comp (wb.pair (order.pair
    (Procedure.binarySub.comp (cut.pair (Procedure.constant stageInputCode Nat.bits 1)))))
  let center := (Procedure.listCons Nat.bits).comp
    (arrival.pair (Procedure.constant stageInputCode (listCode Nat.bits) []))
  let first := (Procedure.listAppend Nat.bits 0).comp (front.pair center)
  exact (Procedure.listAppend Nat.bits 0).comp (first.pair back)

noncomputable opaque rowCellsProgram : Procedure stageInputCode (listCode pairCode)
    (fun x => rowCells x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let tail := Procedure.second Nat.bits (prodCode unaryCode (prodCode Nat.bits gateCode))
  let rest := (Procedure.second unaryCode (prodCode Nat.bits gateCode)).comp tail
  let start := (Procedure.first Nat.bits gateCode).comp rest
  exact (Procedure.listMapWith (f := fun i j => (i,j)) 0 (0,0)
    (Procedure.identity pairCode)).comp (start.pair rowColumnsProgram)

noncomputable opaque sweepCellsProgram : Procedure sweepInputCode (listCode pairCode)
    (fun x => sweepCells x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let rest := Procedure.second Nat.bits (prodCode unaryCode (prodCode Nat.bits (listCode gateCode)))
  let tail := (Procedure.second unaryCode (prodCode Nat.bits (listCode gateCode))).comp rest
  let gates := (Procedure.second Nat.bits (listCode gateCode)).comp tail
  let env := Procedure.second unaryCode sweepInputCode
  let index := Procedure.unaryToBits.comp (Procedure.first unaryCode sweepInputCode)
  let rows := (Procedure.first Nat.bits (prodCode unaryCode
    (prodCode Nat.bits (listCode gateCode)))).comp env
  let er := (Procedure.second Nat.bits (prodCode unaryCode
    (prodCode Nat.bits (listCode gateCode)))).comp env
  let width := (Procedure.first unaryCode (prodCode Nat.bits (listCode gateCode))).comp er
  let et := (Procedure.second unaryCode (prodCode Nat.bits (listCode gateCode))).comp er
  let start := (Procedure.first Nat.bits (listCode gateCode)).comp et
  let gs := (Procedure.second Nat.bits (listCode gateCode)).comp et
  let gate := (Procedure.listGet gateCode (.hadamard 0)).comp (index.pair gs)
  let stage := rowCellsProgram.comp (rows.pair (width.pair
    ((Procedure.binaryAdd.comp (start.pair index)).pair gate)))
  let table := Procedure.tabulate (f := fun (x : SweepInput) i =>
    rowCells x.1 x.2.1 (x.2.2.1+i) (readGate x.2.2.2 i)) [] stage
  exact ((QuantumRawExchange.flattenProgram pairCode (0,0)).comp
    (table.comp ((gateLengthProgram.comp gates).pair
      (Procedure.identity sweepInputCode)))).congrFun (by
        intro x
        simp only [Function.comp_apply,id_eq,sweepCells,List.flatMap_def])

noncomputable opaque valueProgram : Procedure circuitCode (listCode pairCode) value := by
  let c := nearestCircuitProgram
  let gs := gatesProgram.comp c
  let rows := Procedure.unaryToBits.comp (gateLengthProgram.comp gs)
  exact sweepCellsProgram.comp (rows.pair (workProgram.pair
    ((Procedure.constant circuitCode Nat.bits 0).pair gs)))

noncomputable def certificate : Turing.TM2ComputableInPolyTime circuitCode
    (listCode pairCode) value := valueProgram.toTM2

end ContinuumCoulomb.QuantumSweepCells

end

end OAI
