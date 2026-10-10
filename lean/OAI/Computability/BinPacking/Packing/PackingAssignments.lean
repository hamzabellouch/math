import OAI.Computability.BinPacking.Arithmetic.BinaryToTallyMachine
import OAI.Computability.BinPacking.Machines.PackingCountedProgram

namespace OAI

noncomputable section

namespace BinPackingGap.PackingAssignments

open BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks

variable {Reg K : Type} [DecidableEq Reg] [DecidableEq K]

def code (slot : (Reg ⊕ Fin 6) ↪ K) (commands : List (Command Reg)) :
    Code (K := K) (S := State) :=
  PackingArithmeticProgram.code (BinaryRegisterStructured.code slot commands)

theorem exec (slot : (Reg ⊕ Fin 6) ↪ K) (commands : List (Command Reg))
    (base : K → List Bool) (values : Reg → Nat) (ready : Ready commands values)
    (state : State) (width : Nat) (bounded : ∀ r, (values r).size ≤ width) :
    ∃ steps ≤ (runtimePolynomial commands).eval width + 2,
      Exec (code slot commands) ⟨state, registerTapes slot base values⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          registerTapes slot base (resultOf commands values)⟩ := by
  simpa only [code, Nat.add_assoc, Nat.reduceAdd] using PackingArithmeticProgram.exec_in_time
    (BinaryRegisterStructured.code slot commands) _ _ _ state
    (BinaryRegisterStructured.exec_polynomial slot commands base values ready () width bounded)

def copyCommands (destination source : Reg) (different : destination ≠ source) :
    List (Command Reg) := [.clear destination, .copy destination source different]

theorem copy_ready (destination source : Reg) (different : destination ≠ source)
    (values : Reg → Nat) : Ready (copyCommands destination source different) values := by
  simp [copyCommands, Ready, commandReady, result, BinaryRegisterProgram.destination,
    BinaryRegisterProgram.value]

theorem copy_result (destination source : Reg) (different : destination ≠ source)
    (values : Reg → Nat) :
    resultOf (copyCommands destination source different) values =
      Function.update values destination (values source) := by
  simp [copyCommands, resultOf_cons, result, BinaryRegisterProgram.destination,
    BinaryRegisterProgram.value, Ne.symm different]

def copy (slot : (Reg ⊕ Fin 6) ↪ K) (destination source : Reg)
    (different : destination ≠ source) : Code (K := K) (S := State) :=
  code slot (copyCommands destination source different)

theorem copy_exec (slot : (Reg ⊕ Fin 6) ↪ K) (destination source : Reg)
    (different : destination ≠ source) (base : K → List Bool) (values : Reg → Nat)
    (state : State) (width : Nat) (bounded : ∀ r, (values r).size ≤ width) :
    ∃ steps ≤ (runtimePolynomial (copyCommands destination source different)).eval width + 2,
      Exec (copy slot destination source different)
        ⟨state, registerTapes slot base values⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          registerTapes slot base (Function.update values destination (values source))⟩ := by
  simpa only [copy, copy_result] using exec slot (copyCommands destination source different)
    base values (copy_ready destination source different values) state width bounded

def constantCommands (destination : Reg) (constant : Nat) : List (Command Reg) :=
  [.clear destination, .constant destination constant]

theorem constant_ready (destination : Reg) (constant : Nat) (values : Reg → Nat) :
    Ready (constantCommands destination constant) values := by
  simp [constantCommands, Ready, commandReady, result, BinaryRegisterProgram.destination,
    BinaryRegisterProgram.value]

theorem constant_result (destination : Reg) (constant : Nat) (values : Reg → Nat) :
    resultOf (constantCommands destination constant) values =
      Function.update values destination constant := by
  simp [constantCommands, resultOf_cons, result, BinaryRegisterProgram.destination,
    BinaryRegisterProgram.value]

def setConstant (slot : (Reg ⊕ Fin 6) ↪ K) (destination : Reg) (constant : Nat) :
    Code (K := K) (S := State) := code slot (constantCommands destination constant)

theorem constant_exec (slot : (Reg ⊕ Fin 6) ↪ K) (destination : Reg) (constant : Nat)
    (base : K → List Bool) (values : Reg → Nat) (state : State) (width : Nat)
    (bounded : ∀ r, (values r).size ≤ width) :
    ∃ steps ≤ (runtimePolynomial (constantCommands destination constant)).eval width + 2,
      Exec (setConstant slot destination constant)
        ⟨state, registerTapes slot base values⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          registerTapes slot base (Function.update values destination constant)⟩ := by
  simpa only [setConstant, constant_result] using exec slot (constantCommands destination constant)
    base values (constant_ready destination constant values) state width bounded

end BinPackingGap.PackingAssignments

end

end OAI
