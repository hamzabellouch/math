import Mathlib
import OAI.Computability.MaxCut.Machines.Runtime2
import OAI.Computability.MaxCut.Machines.PoweringMachineLoop

namespace OAI

/-! Explicit common-register layout for the powering machine. The header,
word and affine routines use the trailing optional-bit register directly.
Comparison reassociates the finite registers; row evaluation moves the fixed
buffer to the final component. The row adapter below proves an actual step
of the caller's mixed program, rather than requiring that the entire program
be a translated copy of the row routine. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMasterState

open Turing
open MachineFixedBlockMap

abbrev OtherRegisters (N : Nat) := Buffer N × (Bool × Option Bool)
abbrev Master (N : Nat) := OtherRegisters N × Option Bool
abbrev CompareState (N : Nat) := Buffer N × (Bool × (Option Bool × Option Bool))
abbrev RowState (N : Nat) := (Bool × (Option Bool × Option Bool)) × Buffer N

/-- This is definitionally the state already used by the equality-bit producer. -/
def compareEquiv (N : Nat) : Master N ≃ CompareState N :=
  (MachineUnaryEqualityBit.compareStateEquiv (Buffer N)).symm

/-- All four finite components are retained by this register permutation. -/
def rowEquiv (N : Nat) : Master N ≃ RowState N where
  toFun state := ((state.1.2.1, (state.1.2.2, state.2)), state.1.1)
  invFun state := ((state.2, (state.1.1, state.1.2.1)), state.1.2.2)
  left_inv := by rintro ⟨⟨buffer, ⟨flag, left⟩⟩, right⟩; rfl
  right_inv := by rintro ⟨⟨flag, ⟨left, right⟩⟩, buffer⟩; rfl

@[simp] theorem compareEquiv_apply (N : Nat) (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    compareEquiv N ((buffer, (flag, left)), right) = (buffer, (flag, (left, right))) := rfl

@[simp] theorem compareEquiv_symm_apply (N : Nat) (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    (compareEquiv N).symm (buffer, (flag, (left, right))) = ((buffer, (flag, left)), right) := rfl

@[simp] theorem rowEquiv_apply (N : Nat) (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    rowEquiv N ((buffer, (flag, left)), right) = ((flag, (left, right)), buffer) := rfl

@[simp] theorem rowEquiv_symm_apply (N : Nat) (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    (rowEquiv N).symm ((flag, (left, right)), buffer) = ((buffer, (flag, left)), right) := rfl

def withBuffer {N : Nat} (buffer : Buffer N) : Master N :=
  ((buffer, (false, none)), none)

def clean (N : Nat) : Master N := withBuffer (emptyBuffer N)

@[simp] theorem equalityBit_clean {N : Nat} (buffer : Buffer N) :
    MachineUnaryEqualityBit.clean buffer = withBuffer buffer := rfl

@[simp] theorem rowEquiv_withBuffer {N : Nat} (buffer : Buffer N) :
    rowEquiv N (withBuffer buffer) = ((false, (none, none)), buffer) := rfl

@[simp] theorem compareEquiv_withBuffer {N : Nat} (buffer : Buffer N) :
    compareEquiv N (withBuffer buffer) = (buffer, (false, (none, none))) := rfl

/-- The row primitive clears only its own buffer; other finite registers survive. -/
def clearBuffer {N : Nat} (state : Master N) : Master N :=
  (rowEquiv N).symm ((rowEquiv N state).1, emptyBuffer N)

@[simp] theorem clearBuffer_apply {N : Nat} (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    clearBuffer ((buffer, (flag, left)), right) =
      ((emptyBuffer N, (flag, left)), right) := rfl

@[simp] theorem clearBuffer_withBuffer {N : Nat} (buffer : Buffer N) :
    clearBuffer (withBuffer buffer) = clean N := rfl

section Row

variable {K Λ : Type} [DecidableEq K] {N M : Nat}

/-- Only this instruction block is translated into the common state. -/
def encodedBlockAt (src dst : K) (F : Buffer N → Buffer M) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (Master N) :=
  MachineStateEquiv.statement (rowEquiv N).symm
    (PoweringMachineRow.encodedBlockAt src dst F exit)

theorem stepAux_encodedBlockAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ) (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : Master N) (tapes : K → List Bool)
    (hinput : tapes src = PoweringMachineRow.encodeBits (List.ofFn bits) ++ suffix) :
    TM2.stepAux (encodedBlockAt src dst F exit) state tapes =
      { l := exit, var := clearBuffer state,
        stk := Function.update (Function.update tapes src suffix) dst
          (PoweringMachineRow.encodeBits (List.ofFn (F bits)) ++ tapes dst) } := by
  rw [encodedBlockAt, MachineStateEquiv.stepAux_transport_symm, Equiv.symm_symm]
  rw [PoweringMachineRow.stepAux_encodedBlockAt src dst F exit hne bits suffix
    (rowEquiv N state) tapes hinput]
  rfl

/-- Exact caller-program step, with no hypothesis about its other labels. -/
theorem step_encodedBlockAt (src dst : K) (F : Buffer N → Buffer M) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (Master N))
    (label : Λ) (atLabel : program label = encodedBlockAt src dst F exit)
    (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : Master N) (tapes : K → List Bool)
    (hinput : tapes src = PoweringMachineRow.encodeBits (List.ofFn bits) ++ suffix) :
    TM2.step program ⟨some label, state, tapes⟩ =
      some ⟨exit, clearBuffer state,
        Function.update (Function.update tapes src suffix) dst
          (PoweringMachineRow.encodeBits (List.ofFn (F bits)) ++ tapes dst)⟩ := by
  simp only [TM2.step, atLabel, stepAux_encodedBlockAt src dst F exit hne bits suffix state tapes hinput]

def rowAt {t S q : Nat} (src dst : K)
    (labelAt : Fin q → Fin S → PCP.GraphTables.Label) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (Master (PoweringMachineRow.inputSize t S)) :=
  encodedBlockAt src dst (PoweringMachineRow.rowBlock labelAt) exit

/-- The producer's clean finite controls and any previous buffer contents
become the completely clean master state after one genuine row transition. -/
theorem step_rowAt_clean {t S q : Nat} (src dst : K)
    (labelAt : Fin q → Fin S → PCP.GraphTables.Label) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ
      (Master (PoweringMachineRow.inputSize t S)))
    (label : Λ) (atLabel : program label = rowAt (t := t) src dst labelAt exit)
    (hne : src ≠ dst) (bits register : Buffer (PoweringMachineRow.inputSize t S))
    (suffix : List Bool) (tapes : K → List Bool)
    (hinput : tapes src = PoweringMachineRow.encodeBits (List.ofFn bits) ++ suffix) :
    TM2.step program ⟨some label, withBuffer register, tapes⟩ =
      some ⟨exit, clean (PoweringMachineRow.inputSize t S),
        Function.update (Function.update tapes src suffix) dst
          (PoweringMachineRow.encodeBits (List.ofFn (PoweringMachineRow.rowBlock labelAt bits)) ++
            tapes dst)⟩ := by
  simpa only [rowAt, clearBuffer_withBuffer] using
    step_encodedBlockAt src dst (PoweringMachineRow.rowBlock labelAt) exit
      program label atLabel hne bits suffix (withBuffer register) tapes hinput

def rowInTime {t S q : Nat} (src dst : K)
    (labelAt : Fin q → Fin S → PCP.GraphTables.Label) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ
      (Master (PoweringMachineRow.inputSize t S)))
    (label : Λ) (atLabel : program label = rowAt (t := t) src dst labelAt exit)
    (hne : src ≠ dst) (bits register : Buffer (PoweringMachineRow.inputSize t S))
    (suffix : List Bool) (tapes : K → List Bool)
    (hinput : tapes src = PoweringMachineRow.encodeBits (List.ofFn bits) ++ suffix) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some label, withBuffer register, tapes⟩
      (some ⟨exit, clean (PoweringMachineRow.inputSize t S),
        Function.update (Function.update tapes src suffix) dst
          (PoweringMachineRow.encodeBits (List.ofFn (PoweringMachineRow.rowBlock labelAt bits)) ++
            tapes dst)⟩) 1 where
  steps := 1
  evals_in_steps := by
    simpa only [Function.iterate_one, flip, bind, Option.bind] using
      step_rowAt_clean src dst labelAt exit program label atLabel hne bits register suffix tapes hinput
  steps_le_m := le_rfl

end Row

/-- Header preparation already has the common trailing-bit register layout. -/
def headerInTime (N B n : Nat) (suffix : List Bool) (state : Master N) :
    StateTransition.EvalsToInTime
      (TM2.step (PoweringMachineLoop.headerProgram (σ := OtherRegisters N) B))
      ⟨some .initialize, state, PoweringMachineLoop.initialTapes n suffix⟩
      (some (PoweringMachineLoop.finalConfiguration B n suffix state.1)) (n + 2) :=
  PoweringMachineLoop.headerInTime B n suffix state.1 state.2

end MaxCutGames.Foundations.Complexity.PoweringMasterState

end OAI
