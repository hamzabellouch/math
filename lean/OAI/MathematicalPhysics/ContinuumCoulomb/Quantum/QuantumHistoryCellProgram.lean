import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryCells
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSweepCellProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryPrecisionProgram

namespace OAI

/-! Polynomial generation of the exact ordered history cell arrays.  All
list loops are bounded by unary circuit counts; coordinate arithmetic is
binary. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryCells
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumHistoryDescriptors
open QuantumOrderedCellProgram QuantumRouteCode

abbrev Input := QMACircuit × ℕ
abbrev inputCode := QuantumHistoryDescriptors.referenceCode

noncomputable opaque gateCellProgram : Procedure inputCode pairCode
    (fun x => gateCell x.1 x.2) :=
  (Procedure.listGet pairCode (0,0)).comp
    ((Procedure.second circuitCode Nat.bits).pair
      (QuantumSweepCells.valueProgram.comp (Procedure.first circuitCode Nat.bits)))

noncomputable opaque referenceCellProgram : Procedure inputCode pairCode
    (fun x => referenceCell x.1 x.2) := by
  let c := Procedure.first circuitCode Nat.bits
  let i := Procedure.second circuitCode Nat.bits
  let sparse := sparseCircuitProgram.comp c
  let descriptor := orderedAtProgram.comp (sparse.pair i)
  let time := timeValueProgram.comp (sparse.pair descriptor)
  exact gateCellProgram.comp (c.pair time)

noncomputable opaque qubitCellProgram : Procedure inputCode pairCode
    (fun x => qubitCell x.1 x.2) := by
  let c := Procedure.first circuitCode Nat.bits
  let j := Procedure.second circuitCode Nat.bits
  let sparse := sparseCircuitProgram.comp c
  let refs := Procedure.successor.comp (referenceWorkProgram.comp sparse)
  let time := Procedure.unaryToBits.comp (timeProgram.comp sparse)
  let two := Procedure.constant inputCode Nat.bits 2
  let one := Procedure.constant inputCode Nat.bits 1
  let cutoff := Procedure.binaryAdd.comp (time.pair two)
  let k := Procedure.binarySub.comp (j.pair refs)
  let before := Procedure.binarySub.comp (k.pair one)
  let last := Procedure.binarySub.comp (time.pair one)
  let clock := Procedure.conditional (Procedure.binaryLe.comp (before.pair last)) before last
  let work := Procedure.binarySub.comp (k.pair cutoff)
  let modulus := Procedure.successor.comp (Procedure.unaryToBits.comp (workProgram.comp c))
  let coords := (Procedure.binaryDiv.comp (work.pair modulus)).pair
    (Procedure.binaryMod.comp (work.pair modulus))
  exact (Procedure.conditional (Procedure.binaryLt.comp (j.pair refs)) referenceCellProgram
    (Procedure.conditional (Procedure.binaryLt.comp (k.pair cutoff))
      (gateCellProgram.comp (c.pair clock)) coords)).congrFun (by
        intro x
        simp only [qubitCell,Function.comp_apply,id_eq,decide_eq_true_eq,min_def])

noncomputable opaque termCellProgram : Procedure inputCode pairCode
    (fun x => termCell x.1 x.2) := by
  let c := Procedure.first circuitCode Nat.bits
  let i := Procedure.second circuitCode Nat.bits
  let refs := Procedure.successor.comp (referenceWorkProgram.comp (sparseCircuitProgram.comp c))
  let index := Procedure.conditional (Procedure.binaryLt.comp (i.pair refs)) i
    (Procedure.binarySub.comp (i.pair refs))
  exact (referenceCellProgram.comp (c.pair index)).congrFun (by
    intro x
    simp only [termCell,Function.comp_apply,decide_eq_true_eq])

private noncomputable def qubitEntryProgram :
    Procedure (prodCode unaryCode circuitCode) pairCode
      (fun x => qubitCell x.2 x.1) :=
  qubitCellProgram.comp ((Procedure.second unaryCode circuitCode).pair
    (Procedure.unaryToBits.comp (Procedure.first unaryCode circuitCode)))

private noncomputable def termEntryProgram :
    Procedure (prodCode unaryCode circuitCode) pairCode
      (fun x => termCell x.2 x.1) :=
  termCellProgram.comp ((Procedure.second unaryCode circuitCode).pair
    (Procedure.unaryToBits.comp (Procedure.first unaryCode circuitCode)))

noncomputable opaque qubitCellsProgram : Procedure circuitCode (listCode pairCode) qubitCells :=
  ((Procedure.tabulate (f := fun c i => qubitCell c i) (0,0) qubitEntryProgram).comp
    ((QuantumHistoryPrecisionProgram.sourceQubitsProgram.comp sparseCircuitProgram).pair
      (Procedure.identity circuitCode))).congrFun (by intro c; rfl)

noncomputable opaque referenceCellsProgram :
    Procedure circuitCode (listCode pairCode) referenceCells :=
  ((Procedure.tabulate (f := fun c i => termCell c i) (0,0) termEntryProgram).comp
    ((QuantumHistorySamplerProgram.countProgram.comp sparseCircuitProgram).pair
      (Procedure.identity circuitCode))).congrFun (by intro c; rfl)

noncomputable opaque valueProgram : Procedure circuitCode stateCode value :=
  (qubitCellsProgram.pair ((anchorsProgram 4096).comp referenceCellsProgram)).congrFun (by
    intro c
    simp only [value,Function.comp_apply,patternCount_eq])

noncomputable def certificate : Turing.TM2ComputableInPolyTime circuitCode stateCode value :=
  valueProgram.toTM2

end ContinuumCoulomb.QuantumHistoryCells

end

end OAI
