import Mathlib
import OAI.Computability.MinUncut.Games.PoweringGlobalEnumeration
import OAI.Computability.MinUncut.Machines.PoweringMachineVertex

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.PoweringMachineGlobal

open Turing

abbrev Tape (n : Nat) :=
  PoweringMachineInitialize.GlobalTape (PoweringMachineRowBody.capacity n)

abbrev State (d n : Nat) :=
  PoweringMasterState.Master (PoweringMachineRowBody.bufferSize d n)

def placement (n : Nat) :
    PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → Tape n :=
  PoweringMachineInitialize.commonPlacement (PoweringMachineRowBody.capacity n)

def inputTape (n : Nat) : Tape n :=
  placement n (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))

def outputTape (n : Nat) : Tape n :=
  PoweringMachineInitialize.finalOutput (PoweringMachineRowBody.capacity n)

def headerVertices (n : Nat) : Tape n := .inl PoweringMachineLoop.HeaderTape.vertices
def headerDarts (n : Nat) : Tape n := .inl PoweringMachineLoop.HeaderTape.darts

def enumeration (n : Nat) :
    Fin (4 + (11 + PoweringMachineRowBody.capacity n + 1)) ≃ Tape n :=
  PoweringGlobalEnumeration.enumeration (PoweringMachineRowBody.capacity n)

abbrev FinishLabel (n : Nat) := PoweringMachineFinish.Label (enumeration n) (outputTape n)

abbrev Label (d n : Nat) := PoweringMachineInitialize.Label ⊕
  (Bool ⊕ (PoweringMachineVertex.Label d n ⊕ FinishLabel n))

instance labelFintype (d n : Nat) : Fintype (Label d n) :=
  inferInstanceAs (Fintype (PoweringMachineInitialize.Label ⊕
    (Bool ⊕ (PoweringMachineVertex.Label d n ⊕ FinishLabel n))))

def initLabels (d n : Nat) : PoweringMachineInitialize.Label → Label d n := Sum.inl
def guardLabel (d n : Nat) : Label d n := .inr (.inl false)
def bridgeLabel (d n : Nat) : Label d n := .inr (.inl true)

def vertexLabels (d n : Nat) (label : PoweringMachineVertex.Label d n) : Label d n :=
  .inr (.inr (.inl label))

def finishLabels (d n : Nat) (label : FinishLabel n) : Label d n :=
  .inr (.inr (.inr label))

def finishEntry (d n : Nat) : Label d n := finishLabels d n (.inl .seed)

def main (d n : Nat) : Label d n := initLabels d n (.inr .seed)

def program (d n : Nat) :
    Label d n → TM2.Stmt (fun _ : Tape n => Bool) (Label d n) (State d n)
  | .inl label => PoweringMachineInitialize.instruction
      (PoweringMachineRowBody.capacity n) (PoweringMachineRowBody.bufferSize d n)
      (PCP.PoweringTableLayout.blockSize d n) (initLabels d n) (some (guardLabel d n)) label
  | .inr (.inl false) => MachineUnaryCounter.guard
      (placement n (PoweringMachineTapes.start (PoweringMachineRowBody.capacity n)))
      (bridgeLabel d n) (finishEntry d n)
  | .inr (.inl true) => PoweringMachineOuterLoop.bridge d n (vertexLabels d n) (guardLabel d n)
  | .inr (.inr (.inl label)) => PoweringMachineVertex.instruction n (placement n) (outputTape n)
      (vertexLabels d n) (some (guardLabel d n)) label
  | .inr (.inr (.inr label)) => PoweringMachineFinish.instruction (enumeration n)
      (headerVertices n) (headerDarts n) (outputTape n)
      (placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)))
      (finishLabels d n) label

@[simp] theorem atInit (d n : Nat) (label : PoweringMachineInitialize.Label) :
    program d n (initLabels d n label) = PoweringMachineInitialize.instruction
      (PoweringMachineRowBody.capacity n) (PoweringMachineRowBody.bufferSize d n)
      (PCP.PoweringTableLayout.blockSize d n) (initLabels d n) (some (guardLabel d n)) label := rfl

@[simp] theorem atGuard (d n : Nat) :
    program d n (guardLabel d n) = MachineUnaryCounter.guard
      (placement n (PoweringMachineTapes.start (PoweringMachineRowBody.capacity n)))
      (bridgeLabel d n) (finishEntry d n) := rfl

@[simp] theorem atBridge (d n : Nat) :
    program d n (bridgeLabel d n) =
      PoweringMachineOuterLoop.bridge d n (vertexLabels d n) (guardLabel d n) := rfl

@[simp] theorem atVertex (d n : Nat) (label : PoweringMachineVertex.Label d n) :
    program d n (vertexLabels d n label) = PoweringMachineVertex.instruction n
      (placement n) (outputTape n) (vertexLabels d n) (some (guardLabel d n)) label := rfl

@[simp] theorem atFinish (d n : Nat) (label : FinishLabel n) :
    program d n (finishLabels d n label) = PoweringMachineFinish.instruction (enumeration n)
      (headerVertices n) (headerDarts n) (outputTape n)
      (placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)))
      (finishLabels d n) label := rfl

def machine (d n : Nat) : FinTM2 where
  K := Tape n
  k₀ := inputTape n
  k₁ := outputTape n
  Γ _ := Bool
  Λ := Label d n
  main := main d n
  σ := State d n
  initialState := PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n)
  m := program d n

@[simp] theorem machine_code (d n : Nat) (label : Label d n) :
    (machine d n).m label = program d n label := rfl

@[simp] theorem machine_main (d n : Nat) : (machine d n).main = main d n := rfl

@[simp] theorem machine_initialState (d n : Nat) :
    (machine d n).initialState = PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n) := rfl

theorem input_ne_output (n : Nat) : inputTape n ≠ outputTape n :=
  PoweringMachineInitialize.commonPlacement_ne_finalOutput (PoweringMachineRowBody.capacity n)
    (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))

end MinUncutGames.Foundations.Complexity.PoweringMachineGlobal

end

end OAI
