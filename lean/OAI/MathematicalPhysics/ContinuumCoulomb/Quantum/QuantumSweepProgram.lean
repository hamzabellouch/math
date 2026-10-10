import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSweepIndex
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawFamilyProgram
import OAI.Computability.QuantumFactoring.BitStackTabulate
import OAI.Computability.QuantumFactoring.BitStackListIndex
import OAI.Computability.QuantumFactoring.BitStackListLength

namespace OAI

/-! Literal arithmetic and finite lists for the alternating row sweep. The
row width is supplied in unary exactly where a list is enumerated. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCircuitCode
open ExactQuantumFactoring.BitStackProgram

abbrev TripleNat := ℕ × (ℕ × ℕ)
def tripleNatCode : TripleNat → List Bool := prodCode Nat.bits (prodCode Nat.bits Nat.bits)

noncomputable def sweepIndexProgram : Procedure tripleNatCode Nat.bits
    (fun x => sweepIndex x.1 x.2.1 x.2.2) := by
  let w := Procedure.first Nat.bits (prodCode Nat.bits Nat.bits)
  let rest := Procedure.second Nat.bits (prodCode Nat.bits Nat.bits)
  let row := (Procedure.first Nat.bits Nat.bits).comp rest
  let k := (Procedure.second Nat.bits Nat.bits).comp rest
  let parity := Procedure.binaryZero.comp (Procedure.binaryMod.comp
    (row.pair (Procedure.constant tripleNatCode Nat.bits 2)))
  exact (Procedure.conditional parity k (Procedure.binarySub.comp (w.pair k))).congrFun
    (by intro x; simp only [Function.comp_apply,sweepIndex,decide_eq_true_eq])

abbrev RowGate := ℕ × (ℕ × QMAGate)
def rowGateCode : RowGate → List Bool := prodCode Nat.bits (prodCode Nat.bits gateCode)

noncomputable def rowCutProgram : Procedure rowGateCode Nat.bits
    (fun x => rowCut x.1 x.2.1 x.2.2) := by
  let w := Procedure.first Nat.bits (prodCode Nat.bits gateCode)
  let rest := Procedure.second Nat.bits (prodCode Nat.bits gateCode)
  let row := (Procedure.first Nat.bits gateCode).comp rest
  let gate := (Procedure.second Nat.bits gateCode).comp rest
  let modulus := Procedure.successor.comp w
  let left := Procedure.binaryMod.comp ((gateLeftProgram.comp gate).pair modulus)
  let right := Procedure.binaryMod.comp ((gateRightProgram.comp gate).pair modulus)
  let i := sweepIndexProgram.comp (w.pair (row.pair left))
  let j := sweepIndexProgram.comp (w.pair (row.pair right))
  let maximum := Procedure.conditional (Procedure.binaryLe.comp (i.pair j)) j i
  let tag := Procedure.binaryEq.comp ((gateTagProgram.comp gate).pair
    (Procedure.constant rowGateCode Nat.bits 2))
  exact (Procedure.successor.comp (Procedure.conditional tag maximum i)).congrFun (by
    intro x
    simp only [Function.comp_apply,decide_eq_true_eq,rowCut]
    split <;> simp only [max_def])

noncomputable def rowAddressProgram : Procedure tripleNatCode Nat.bits
    (fun x => rowAddress x.1 x.2.1 x.2.2) := by
  let w := Procedure.first Nat.bits (prodCode Nat.bits Nat.bits)
  let rest := Procedure.second Nat.bits (prodCode Nat.bits Nat.bits)
  let row := (Procedure.first Nat.bits Nat.bits).comp rest
  let i := (Procedure.second Nat.bits Nat.bits).comp rest
  let modulus := Procedure.successor.comp w
  exact Procedure.binaryAdd.comp ((Procedure.binaryMul.comp (row.pair modulus)).pair
    (Procedure.binaryMod.comp (i.pair modulus)))

noncomputable def mapToRowProgram : Procedure rowGateCode gateCode
    (fun x => mapToRow x.1 x.2.1 x.2.2) := by
  let w := Procedure.first Nat.bits (prodCode Nat.bits gateCode)
  let rest := Procedure.second Nat.bits (prodCode Nat.bits gateCode)
  let row := (Procedure.first Nat.bits gateCode).comp rest
  let gate := (Procedure.second Nat.bits gateCode).comp rest
  let left := rowAddressProgram.comp (w.pair (row.pair (gateLeftProgram.comp gate)))
  let right := rowAddressProgram.comp (w.pair (row.pair (gateRightProgram.comp gate)))
  let tag := gateTagProgram.comp gate
  let isH := Procedure.binaryZero.comp tag
  let isT := Procedure.binaryEq.comp (tag.pair (Procedure.constant rowGateCode Nat.bits 1))
  exact (Procedure.conditional isH (hadamardProgram.comp left)
    (Procedure.conditional isT (phaseProgram.comp left)
      (cnotProgram.comp (left.pair right)))).congrFun (by
        rintro ⟨w,row,g⟩
        cases g <;> rfl)

def wirePairCode : (ℕ × ℕ) → List Bool := prodCode Nat.bits Nat.bits
def rowPairsInputCode : TripleNat → List Bool :=
  prodCode unaryCode (prodCode Nat.bits Nat.bits)

noncomputable def rowPairsProgram : Procedure rowPairsInputCode (listCode wirePairCode)
    (fun x => rowPairs x.1 x.2.1 x.2.2) := by
  let w := Procedure.first unaryCode (prodCode Nat.bits Nat.bits)
  let rest := Procedure.second unaryCode (prodCode Nat.bits Nat.bits)
  let wb := Procedure.unaryToBits.comp w
  let context := wb.pair rest
  let pointContext := Procedure.second unaryCode tripleNatCode
  let k := Procedure.unaryToBits.comp (Procedure.first unaryCode tripleNatCode)
  let pw := (Procedure.first Nat.bits (prodCode Nat.bits Nat.bits)).comp pointContext
  let pr := (Procedure.second Nat.bits (prodCode Nat.bits Nat.bits)).comp pointContext
  let row := (Procedure.first Nat.bits Nat.bits).comp pr
  let order := (Procedure.second Nat.bits Nat.bits).comp pr
  let index := sweepIndexProgram.comp (pw.pair (order.pair k))
  let modulus := Procedure.successor.comp pw
  let left := Procedure.binaryAdd.comp
    ((Procedure.binaryMul.comp (row.pair modulus)).pair index)
  let right := Procedure.binaryAdd.comp
    ((Procedure.binaryMul.comp ((Procedure.successor.comp row).pair modulus)).pair index)
  let point := left.pair right
  exact ((Procedure.tabulate (f := fun x k =>
    (x.2.1*(x.1+1)+sweepIndex x.1 x.2.2 k,
      (x.2.1+1)*(x.1+1)+sweepIndex x.1 x.2.2 k)) (0,0) point).comp
        ((Procedure.unarySuccessor.comp w).pair context)).congrFun (by intro x; rfl)

noncomputable def transferListProgram : Procedure (listCode wirePairCode) (listCode gateCode)
    transferList := by
  let left := Procedure.first Nat.bits Nat.bits
  let right := Procedure.second Nat.bits Nat.bits
  let forward := cnotProgram
  let backward := cnotProgram.comp (right.pair left)
  let nil := Procedure.constant wirePairCode (listCode gateCode) []
  let one := (Procedure.listCons gateCode).comp (forward.pair nil)
  let two := (Procedure.listCons gateCode).comp (backward.pair one)
  let three := (Procedure.listCons gateCode).comp (forward.pair two)
  exact ((QuantumRawExchange.flattenProgram gateCode (.hadamard 0)).comp
    (Procedure.listMap (0,0) [] three)).congrFun (by intro ps; rfl)

private noncomputable def pairTakeProgram :
    Procedure (prodCode Nat.bits (listCode wirePairCode)) (listCode wirePairCode)
      (fun x => x.2.take x.1) := by
  let n := Procedure.first Nat.bits (listCode wirePairCode)
  let ps := Procedure.second Nat.bits (listCode wirePairCode)
  let len := (Procedure.listLength wirePairCode (0,0)).comp ps
  let count := Procedure.binarySub.comp (len.pair n)
  let reverse := (Procedure.listReverse wirePairCode (0,0)).comp ps
  exact ((Procedure.listReverse wirePairCode (0,0)).comp
    ((Procedure.listDrop wirePairCode).comp (count.pair reverse))).congrFun (by
      intro x
      simp only [Function.comp_apply,← List.reverse_take,List.reverse_reverse])

abbrev StageInput := ℕ × (ℕ × (ℕ × QMAGate))
def stageInputCode : StageInput → List Bool :=
  prodCode Nat.bits (prodCode unaryCode (prodCode Nat.bits gateCode))

noncomputable def rowStageProgram : Procedure stageInputCode (listCode gateCode)
    (fun x => rowStage x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let rows := Procedure.first Nat.bits (prodCode unaryCode (prodCode Nat.bits gateCode))
  let tail := Procedure.second Nat.bits (prodCode unaryCode (prodCode Nat.bits gateCode))
  let width := (Procedure.first unaryCode (prodCode Nat.bits gateCode)).comp tail
  let rest := (Procedure.second unaryCode (prodCode Nat.bits gateCode)).comp tail
  let start := (Procedure.first Nat.bits gateCode).comp rest
  let gate := (Procedure.second Nat.bits gateCode).comp rest
  let order := Procedure.binarySub.comp
    ((Procedure.binarySub.comp (rows.pair
      (Procedure.constant stageInputCode Nat.bits 1))).pair start)
  let ps := rowPairsProgram.comp (width.pair (start.pair order))
  let cut := rowCutProgram.comp
    ((Procedure.unaryToBits.comp width).pair (order.pair gate))
  let front := transferListProgram.comp (pairTakeProgram.comp (cut.pair ps))
  let back := transferListProgram.comp ((Procedure.listDrop wirePairCode).comp (cut.pair ps))
  let mapped := mapToRowProgram.comp ((Procedure.unaryToBits.comp width).pair
    ((Procedure.successor.comp start).pair gate))
  let center := (Procedure.listCons gateCode).comp
    (mapped.pair (Procedure.constant stageInputCode (listCode gateCode) []))
  let first := (Procedure.listAppend gateCode (.hadamard 0)).comp (front.pair center)
  exact (Procedure.listAppend gateCode (.hadamard 0)).comp (first.pair back)

end ContinuumCoulomb.QuantumCircuitCode

end

end OAI
