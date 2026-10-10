import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.PoweringMachineGlobal

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringGlobalConfiguration

open Turing PoweringMachineGlobal

theorem placement_injective (n : Nat) : Function.Injective (placement n) :=
  PoweringMachineInitialize.commonPlacement_injective (PoweringMachineRowBody.capacity n)

theorem placement_ne_output (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    placement n tape ≠ outputTape n :=
  PoweringMachineInitialize.commonPlacement_ne_finalOutput
    (PoweringMachineRowBody.capacity n) tape

theorem output_ne_placement (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    outputTape n ≠ placement n tape := Ne.symm (placement_ne_output n tape)

theorem headerVertices_ne_placement (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    headerVertices n ≠ placement n tape :=
  Ne.symm (PoweringMachineInitialize.commonPlacement_ne_header
    (PoweringMachineRowBody.capacity n) tape .vertices (by decide))

theorem headerDarts_ne_placement (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    headerDarts n ≠ placement n tape :=
  Ne.symm (PoweringMachineInitialize.commonPlacement_ne_header
    (PoweringMachineRowBody.capacity n) tape .darts (by decide))

theorem placement_ne_headerVertices (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    placement n tape ≠ headerVertices n := Ne.symm (headerVertices_ne_placement n tape)

theorem placement_ne_headerDarts (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    placement n tape ≠ headerDarts n := Ne.symm (headerDarts_ne_placement n tape)

theorem headerVertices_ne_headerDarts (n : Nat) : headerVertices n ≠ headerDarts n := by
  simp [headerVertices, headerDarts]

theorem headerVertices_ne_output (n : Nat) : headerVertices n ≠ outputTape n := by
  simp [headerVertices, outputTape, PoweringMachineInitialize.finalOutput]

theorem headerDarts_ne_output (n : Nat) : headerDarts n ≠ outputTape n := by
  simp [headerDarts, outputTape, PoweringMachineInitialize.finalOutput]

theorem headerVertices_ne_scratch (n : Nat) :
    headerVertices n ≠
      placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)) :=
  headerVertices_ne_placement n _

theorem headerDarts_ne_scratch (n : Nat) :
    headerDarts n ≠
      placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)) :=
  headerDarts_ne_placement n _

theorem scratch_ne_output (n : Nat) :
    placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)) ≠
      outputTape n :=
  placement_ne_output n _

@[simp] theorem boolList_mpr_eq (h : List Bool = List Bool) (bits : List Bool) :
    h.mpr bits = bits := rfl

theorem haltList_tapes (d n : Nat) (output : List Bool) :
    (Turing.haltList (machine d n) output).stk =
      MachineDrainMany.haltTapes (outputTape n) output := by
  funext tape
  change Tape n at tape
  change (if tape = outputTape n then output else []) =
    (if tape = outputTape n then output else [])
  rfl

theorem haltList_eq (d n : Nat) (output : List Bool) :
    Turing.haltList (machine d n) output =
      (⟨none, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        MachineDrainMany.haltTapes (outputTape n) output⟩ : (machine d n).Cfg) := by
  change (⟨none, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
      (Turing.haltList (machine d n) output).stk⟩ : (machine d n).Cfg) = _
  exact congrArg
    (fun tapes => (⟨none, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
      tapes⟩ : (machine d n).Cfg)) (haltList_tapes d n output)

end IndependentSetsGames.Foundations.Complexity.PoweringGlobalConfiguration

end OAI
