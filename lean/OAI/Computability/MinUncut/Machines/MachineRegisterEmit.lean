import Mathlib
import OAI.Computability.MinUncut.Machines.MachineSubstitution

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegisterEmit

open Turing
open MinUncutGames.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def emitStatement (destination : K) (offset : Nat) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  pushWord destination (List.replicate offset true) (finish exit)

theorem emitStep (destination : K) (offset : Nat) (emitLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atEmit : program emitLabel = emitStatement destination offset exit)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some emitLabel, (ambient, register), base⟩ =
      some ⟨exit, (ambient, register),
        Function.update base destination (List.replicate offset true ++ base destination)⟩ := by
  change some (TM2.stepAux (program emitLabel) (ambient, register) base) = _
  rw [atEmit, emitStatement, stepAux_pushWord]
  cases exit <;> simp [finish, TM2.stepAux]

theorem prefix_encodeWord (offset n : Nat) :
    List.replicate offset true ++ encodeWord n = encodeWord (offset + n) := by
  simp only [encodeWord, List.replicate_add, List.append_assoc]

theorem registerEmitTrace (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch) (offset : Nat)
    (firstLabel secondLabel emitLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atFirst : program firstLabel =
      Reduction.MachineTransfer.loopAt source scratch id false firstLabel (some secondLabel))
    (atSecond : program secondLabel =
      MachineCopy.forkLoop scratch source destination false secondLabel (some emitLabel))
    (atEmit : program emitLabel = emitStatement destination offset exit)
    (base : K → List Bool) (n : Nat) (sourceWord : base source = encodeWord n)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * n + 5]
      (some ⟨some firstLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Function.update base destination (encodeWord (offset + n) ++ base destination)⟩ := by
  have copied := MachineCopy.copyTrace source destination scratch sourceDestination
    sourceScratch destinationScratch false firstLabel secondLabel (some emitLabel)
    program atFirst atSecond base scratchEmpty ambient register
  rw [sourceWord, encodeWord_length] at copied
  rw [show 2 * n + 5 = 1 + 2 * (n + 1 + 1) by omega,
    Function.iterate_add_apply, copied, Function.iterate_one]
  change TM2.step program
    ⟨some emitLabel, (ambient, none),
      Function.update base destination (encodeWord n ++ base destination)⟩ = _
  rw [emitStep destination offset emitLabel exit program atEmit]
  simp only [Function.update_self, Function.update_idem]
  rw [← List.append_assoc, prefix_encodeWord]

def registerEmitInTime (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch) (offset : Nat)
    (firstLabel secondLabel emitLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atFirst : program firstLabel =
      Reduction.MachineTransfer.loopAt source scratch id false firstLabel (some secondLabel))
    (atSecond : program secondLabel =
      MachineCopy.forkLoop scratch source destination false secondLabel (some emitLabel))
    (atEmit : program emitLabel = emitStatement destination offset exit)
    (base : K → List Bool) (n : Nat) (sourceWord : base source = encodeWord n)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some firstLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        Function.update base destination (encodeWord (offset + n) ++ base destination)⟩)
      (2 * n + 5) where
  steps := 2 * n + 5
  evals_in_steps := registerEmitTrace source destination scratch sourceDestination sourceScratch
    destinationScratch offset firstLabel secondLabel emitLabel exit program atFirst atSecond
    atEmit base n sourceWord scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

def program (source destination scratch : K) (offset : Nat) (exit : Option (Fin 3)) :
    Fin 3 → TM2.Stmt (Alphabet (K := K)) (Fin 3) (σ × Option Bool) :=
  fun label => if label = 0 then
    Reduction.MachineTransfer.loopAt source scratch id false 0 (some 1)
  else if label = 1 then
    MachineCopy.forkLoop scratch source destination false 1 (some 2)
  else emitStatement destination offset exit

def programInTime (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch) (offset : Nat) (exit : Option (Fin 3))
    (base : K → List Bool) (n : Nat) (sourceWord : base source = encodeWord n)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program source destination scratch offset exit))
      ⟨some 0, (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        Function.update base destination (encodeWord (offset + n) ++ base destination)⟩)
      (2 * n + 5) :=
  registerEmitInTime source destination scratch sourceDestination sourceScratch
    destinationScratch offset 0 1 2 exit (program source destination scratch offset exit)
    (by simp [program]) (by simp [program]) (by simp [program])
    base n sourceWord scratchEmpty ambient register

def machine (offset : Nat) : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Fin 3
  main := 0
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program 0 1 2 offset none

def machineInTime (offset : Nat) (base : Fin 3 → List Bool) (n : Nat)
    (sourceWord : base 0 = encodeWord n) (scratchEmpty : base 2 = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (machine offset).step
      ⟨some (0 : Fin 3), ((), register), base⟩
      (some ⟨none, ((), none),
        Function.update base (1 : Fin 3) (encodeWord (offset + n) ++ base 1)⟩)
      (2 * n + 5) :=
  programInTime (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    offset none base n sourceWord scratchEmpty () register

omit [DecidableEq K] in
theorem emitStatement_pushes (destination : K) (offset : Nat) (exit : Option Λ) :
    Runtime.statementPushBound (emitStatement (σ := σ) destination offset exit) = offset := by
  cases exit <;> simp [emitStatement, statementPushBound_pushWord, finish,
    Runtime.statementPushBound]

omit [DecidableEq K] in
theorem program_pushes_le (source destination scratch : K) (offset : Nat)
    (exit : Option (Fin 3)) (label : Fin 3) :
    Runtime.statementPushBound
      (program (σ := σ) source destination scratch offset exit label) ≤ max 2 offset := by
  unfold program
  split
  · simp [Reduction.MachineTransfer.loopAt, Reduction.MachineTransfer.exitAt,
      Runtime.statementPushBound]
  · split
    · simp [MachineCopy.forkLoop, Reduction.MachineTransfer.exitAt,
        Runtime.statementPushBound]
    · simpa only [emitStatement_pushes] using (Nat.le_max_right 2 offset)

theorem machine_pushes_le (offset : Nat) :
    Runtime.programPushBound (machine offset) ≤ max 2 offset := by
  have h : ∀ labels : List (Fin 3),
      Runtime.maxLabelPushes (machine offset).m labels ≤ max 2 offset := by
    intro labels
    change Runtime.maxLabelPushes (program (σ := Unit) (0 : Fin 3) 1 2 offset none)
      labels ≤ max 2 offset
    induction labels with
    | nil => exact Nat.zero_le _
    | cons label labels ih =>
      exact max_le (program_pushes_le (σ := Unit) (0 : Fin 3) 1 2 offset none label) ih
  exact h _

end MinUncutGames.Foundations.Complexity.MachineRegisterEmit

end

end OAI
