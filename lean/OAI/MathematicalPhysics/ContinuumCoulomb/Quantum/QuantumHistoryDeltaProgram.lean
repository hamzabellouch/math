import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryDelta
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryDiagonalProgram

namespace OAI

/-! A polynomial exact-arithmetic program for the propagation delta entry.
Only equality scans depend on circuit size; the matrix arity stays local. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDelta
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar
open QuantumHistoryDiagonal QuantumCircuitCode QuantumHistoryDescriptors

noncomputable opaque guardProgram : Procedure inputCode Procedure.boolCode
    (fun x : Input => guard x.1 x.2.1.2 x.2.2) := by
  let zero := Procedure.constant inputCode Nat.bits 0
  let one := Procedure.constant inputCode Nat.bits 1
  let two := Procedure.constant inputCode Nat.bits 2
  let left := Procedure.binaryEq.comp ((clockValueProgram indexProgram).pair one)
  let right := Procedure.binaryEq.comp
    ((clockValueProgram (Procedure.binaryAdd.comp (indexProgram.pair two))).pair zero)
  let middle := Procedure.binaryEq.comp
    ((clockValueProgram (Procedure.successor.comp indexProgram)).pair zero)
  exact (Procedure.boolAnd.comp (left.pair
    (Procedure.boolAnd.comp (right.pair middle)))).congrFun (by
      intro x
      apply Bool.eq_iff_iff.mpr
      simp only [guard,Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq,
        Nat.succ_eq_add_one,Fin.ext_iff,Fin.val_one,Fin.val_zero])

noncomputable opaque clockCountProgram : Procedure inputCode unaryCode
    (fun x : Input => x.1.gates.length+2) :=
  Procedure.unaryAdd.comp
    ((QuantumHistoryDescriptors.timeProgram.comp circuitProgram).pair
      (Procedure.constant inputCode unaryCode 2))

noncomputable opaque allCountProgram : Procedure inputCode unaryCode
    (fun x : Input => x.1.gates.length+2+(x.1.work+1)) :=
  Procedure.unaryAdd.comp (clockCountProgram.pair
    (Procedure.unarySuccessor.comp (workProgram.comp circuitProgram)))

noncomputable opaque flippedProgram : Procedure inputCode Procedure.boolCode
    (fun x : Input => flipped x.1 x.2.1.2 x.2.2) := by
  let target := Procedure.binaryAdd.comp
    (clockBaseProgram.pair (Procedure.successor.comp indexProgram))
  let args := allCountProgram.pair (clockBaseProgram.pair
    ((Procedure.constant inputCode Procedure.boolCode true).pair (target.pair dataProgram)))
  exact QuantumHistoryComparison.program.comp args

noncomputable opaque sameClockProgram : Procedure inputCode Procedure.boolCode
    (fun x : Input => sameClock x.1 x.2.2) :=
  QuantumHistoryComparison.program.comp
    (clockCountProgram.pair (clockBaseProgram.pair
      ((Procedure.constant inputCode Procedure.boolCode false).pair
        ((Procedure.constant inputCode Nat.bits 0).pair dataProgram))))

noncomputable opaque gateEntryProgram : Procedure inputCode scalarCode
    (fun x : Input => QuantumGateEntryProgram.entry
      (x.1.work,referenceWork x.1+1+(x.1.gates.length+2),
        QuantumHistorySiteProgram.gateAt (x.1,x.2.1.2),x.2.2)) :=
  QuantumGateEntryProgram.entryProgram.comp
    ((workProgram.comp circuitProgram).pair (workBaseProgram.pair
      ((QuantumHistorySiteProgram.gateAtProgram.comp
        (circuitProgram.pair indexProgram)).pair dataProgram)))

noncomputable opaque program : Procedure inputCode scalarCode
    (fun x : Input => entry x.1 x.2.1.2 x.2.2) := by
  let zero := Procedure.constant inputCode scalarCode (rat 0)
  let one := Procedure.constant inputCode scalarCode (rat 1)
  let first := Procedure.conditional flippedProgram one zero
  let second := mulProgram.comp
    ((Procedure.conditional sameClockProgram one zero).pair gateEntryProgram)
  exact (Procedure.conditional guardProgram
    (subProgram.comp (first.pair second)) zero).congrFun (by
      intro x
      simp only [entry,Function.comp_apply]
      simp only [apply_ite rat])

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode scalarCode
    (fun x : Input => entry x.1 x.2.1.2 x.2.2) := program.toTM2

end ContinuumCoulomb.QuantumHistoryDelta

end

end OAI
