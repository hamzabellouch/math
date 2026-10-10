import OAI.Computability.BinPacking.Arithmetic.NatExpressionBounds
import OAI.Computability.BinPacking.Machines.PackingCountedProgram

namespace OAI

namespace BinPackingGap.PackingRegisterUpdate

open Turing
open BinPackingGames.Foundations.Complexity
open BinaryRegisterProgram
open FiniteTapeProgram PackingMachineBlocks

inductive Kind
  | add | multiply
  deriving DecidableEq

instance : Fintype Kind where
  elems := {.add, .multiply}
  complete k := by cases k <;> simp

def operation (kind : Kind) : Nat → Nat → Nat :=
  match kind with
  | .add => Nat.add
  | .multiply => Nat.mul

def operands : Operands (Fin 3) where
  destination := 2
  left := 0
  right := 1
  left_ne_right := by decide
  left_ne_destination := by decide
  right_ne_destination := by decide

def operator : Kind → Command (Fin 3)
  | .add => .add operands
  | .multiply => .mul operands

def commands (kind : Kind) : List (Command (Fin 3)) :=
  [operator kind, .clear 1, .copy 1 2 (by decide), .clear 2]

def values (a b : Nat) : Fin 3 → Nat := ![a, b, 0]

theorem commands_ready (kind : Kind) (a b : Nat) : Ready (commands kind) (values a b) := by
  cases kind <;>
    simp [commands, operator, Ready, commandReady, result, destination, value, operands, values]

theorem commands_result (kind : Kind) (a b : Nat) :
    resultOf (commands kind) (values a b) = values a (operation kind a b) := by
  funext r
  cases kind <;> fin_cases r <;>
    simp [commands, operator, resultOf_cons, result, destination, value, operands, values,
      operation]

theorem operation_size_le (kind : Kind) (a b : Nat) :
    (operation kind a b).size ≤ a.size + b.size + 1 := by
  cases kind with
  | add =>
      have h := BinaryArithmetic.size_add_le a b
      change (a + b).size ≤ a.size + b.size + 1
      omega
  | multiply =>
      exact (BinaryArithmetic.size_mul_le a b).trans (Nat.le_succ _)

theorem commands_budget (kind : Kind) (a b : Nat) :
    budget (commands kind) (values a b) =
      cost (operator kind) (values a b) + b.size + 3 * (operation kind a b).size + 4 := by
  cases kind <;>
    simp [commands, operator, budget, MachineFiniteSequence.steps, result, destination,
      value, operands, values, cost, operation] <;> omega

theorem commands_budget_le (kind : Kind) (a b : Nat) :
    budget (commands kind) (values a b) + 1 ≤ 64 * (a.size + b.size + 1) ^ 2 := by
  have hsize := operation_size_le kind a b
  have hw : 1 ≤ a.size + b.size + 1 := by omega
  have hsquare : a.size + b.size + 1 ≤ (a.size + b.size + 1) ^ 2 := by nlinarith
  rw [commands_budget]
  cases kind <;> simp [operator, cost, operands, values, operation] at * <;> nlinarith

def main (kind : Kind) : BinaryRegisterProgram.Label (commands kind) :=
  .inl (BinaryRegisterProgram.main (operator kind))

variable {K : Type} [DecidableEq K]

def code (slots : (Fin 3 ⊕ Fin 6) ↪ K) (kind : Kind) : Code (K := K) (S := State) :=
  invoke arithmeticControl (BinaryAddMachine.clean ()) (main kind)
    (BinaryRegisterProgram.program slots (commands kind))

theorem exec (slots : (Fin 3 ⊕ Fin 6) ↪ K) (kind : Kind)
    (base : K → List Bool) (a b : Nat) (state : State) :
    ∃ steps ≤ 64 * (a.size + b.size + 1) ^ 2,
      Exec (code slots kind) ⟨state, registerTapes slots base (values a b)⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          registerTapes slots base (values a (operation kind a b))⟩ := by
  have run := BinaryRegisterProgram.programInTime slots (commands kind) base
    (values a b) (commands_ready kind a b) ()
  rw [commands_result] at run
  have run' : StateTransition.EvalsToInTime
      (TM2.step (BinaryRegisterProgram.program (A := Unit) slots (commands kind)))
      ⟨some (main kind), BinaryAddMachine.clean (), registerTapes slots base (values a b)⟩
      (some ⟨none, BinaryAddMachine.clean (),
        registerTapes slots base (values a (operation kind a b))⟩)
      (budget (commands kind) (values a b)) := run
  obtain ⟨n, hn, hrun⟩ := invokeExecInTime arithmeticControl (BinaryAddMachine.clean ())
    (main kind) (BinaryRegisterProgram.program slots (commands kind))
    ⟨state, registerTapes slots base (values a b)⟩ (BinaryAddMachine.clean ())
    (registerTapes slots base (values a (operation kind a b))) _ run'
  exact ⟨n, hn.trans (commands_budget_le kind a b), hrun⟩

end BinPackingGap.PackingRegisterUpdate

end OAI
