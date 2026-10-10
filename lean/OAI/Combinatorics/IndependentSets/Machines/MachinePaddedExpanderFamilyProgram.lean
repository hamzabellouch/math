import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineStateEquiv
import OAI.Combinatorics.IndependentSets.Machines.MachineCloudPadding
import OAI.Combinatorics.IndependentSets.Machines.MachineStateFrame
import OAI.Combinatorics.IndependentSets.Machines.MachineExpanderFamilyLoop

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachinePaddedExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

abbrev fixedDegree := PCP.Expanders.baseDegree
abbrev SmallTable := Table (cloudSize fixedDegree) fixedDegree
abbrev Tape := MachineExpanderFamily.Tape ⊕ MachineCeilingPower.Tape
abbrev Alphabet (_ : Tape) := Bool
abbrev Label := MachineExpanderFamily.Label fixedDegree ⊕ MachineCeilingPower.Label
abbrev State (ρ : Type) := MachineExpanderFamily.State ρ fixedDegree × (Bool × Option Bool)

def familyTape (tape : MachineExpanderFamily.Tape) : Tape := .inl tape

def familyView : Tape → Option MachineExpanderFamily.Tape
  | .inl tape => some tape
  | .inr _ => none

@[simp] theorem familyView_left (tape : MachineExpanderFamily.Tape) :
    familyView (familyTape tape) = some tape := rfl

theorem familyView_right (j : Tape) (tape : MachineExpanderFamily.Tape)
    (h : familyView j = some tape) : familyTape tape = j := by
  cases j with
  | inl j =>
    have hj : j = tape := Option.some.inj h
    subst tape
    rfl
  | inr j => simp [familyView] at h

def ceilingTape : MachineCeilingPower.Tape → Tape
  | .level => .inl (.inr .remainingLevel)
  | tape => .inr tape

def ceilingView : Tape → Option MachineCeilingPower.Tape
  | .inl (.inr .remainingLevel) => some .level
  | .inl _ => none
  | .inr .level => none
  | .inr tape => some tape

@[simp] theorem ceilingView_left (tape : MachineCeilingPower.Tape) :
    ceilingView (ceilingTape tape) = some tape := by
  cases tape <;> rfl

theorem ceilingView_right (j : Tape) (tape : MachineCeilingPower.Tape)
    (h : ceilingView j = some tape) : ceilingTape tape = j := by
  cases j with
  | inl j =>
    cases j with
    | inl j => simp [ceilingView] at h
    | inr tape =>
      cases tape <;> simp_all [ceilingView, ceilingTape]
      cases h
      rfl
  | inr j => cases j <;> simp_all [ceilingView, ceilingTape] <;> cases h <;> rfl

def familyLabel (label : MachineExpanderFamily.Label fixedDegree) : Label := .inl label
def ceilingLabel (label : MachineCeilingPower.Label) : Label := .inr label
def main : Label := .inr .init
def familyEntry : Label := .inl (.inr .initialize)

def ceilingStates (ρ : Type) :
    MachineCeilingPower.State (MachineExpanderFamily.State ρ fixedDegree) ≃ State ρ :=
  Equiv.prodAssoc _ _ _

@[simp] theorem ceilingStates_apply (ρ : Type)
    (state : MachineCeilingPower.State (MachineExpanderFamily.State ρ fixedDegree)) :
    ceilingStates ρ state = (state.1.1, (state.1.2, state.2)) := rfl

variable {ρ : Type} [Fintype ρ]

def familySource (H : SmallTable) : MachineExpanderFamily.Label fixedDegree →
    TM2.Stmt MachineExpanderFamily.BoolAlphabet
      (MachineExpanderFamily.Label fixedDegree) (State ρ) :=
  MachineStateFrame.frameProgram (τ := Bool × Option Bool)
    (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one)

def ceilingSource : MachineCeilingPower.Label →
    TM2.Stmt MachineCeilingPower.Alphabet MachineCeilingPower.Label (State ρ) :=
  MachineStateEquiv.program (ceilingStates ρ)
    (MachineCeilingPower.program PCP.ExpanderFamily.growth)

def program (H : SmallTable) : Label → TM2.Stmt Alphabet Label (State ρ)
  | .inl label =>
    MachineCloudPadding.Placement.statement familyTape familyLabel none (familySource H label)
  | .inr label =>
    MachineCloudPadding.Placement.statement ceilingTape ceilingLabel (some familyEntry)
      (ceilingSource (ρ := ρ) label)

@[simp] theorem program_family (H : SmallTable)
    (label : MachineExpanderFamily.Label fixedDegree) :
    program (ρ := ρ) H (familyLabel label) =
      MachineCloudPadding.Placement.statement familyTape familyLabel none
        (familySource H label) := rfl

@[simp] theorem program_ceiling (H : SmallTable) (label : MachineCeilingPower.Label) :
    program (ρ := ρ) H (ceilingLabel label) =
      MachineCloudPadding.Placement.statement ceilingTape ceilingLabel (some familyEntry)
        (ceilingSource (ρ := ρ) label) := rfl

def initialState (state : MachineExpanderFamily.State ρ fixedDegree)
    (register : Option Bool) : State ρ := (state, (false, register))

def finalState (H : SmallTable) (state : MachineExpanderFamily.State ρ fixedDegree) : State ρ :=
  (MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H
    (MachineExpanderFamily.caller state), (false, none))

def initialTapes (requested : Nat) : Tape → List Bool
  | .inr .input => encodeWord requested
  | _ => []

def retainedCeilingTapes (requested : Nat) : MachineCeilingPower.Tape → List Bool :=
  MachineCeilingPower.memory (encodeWord requested) []
    (encodeWord (PCP.PreprocessingLevels.paddedSize requested)) [] [] [] [] []

def handoffTapes (requested : Nat) : Tape → List Bool
  | .inl tape => MachineExpanderFamily.toBoolTapes
      (MachineExpanderFamily.initialTapes (PCP.PreprocessingLevels.boundedLevel requested) []) tape
  | .inr tape => retainedCeilingTapes requested tape

def finalTapes (H : SmallTable) (requested : Nat) : Tape → List Bool
  | .inl tape => MachineExpanderFamily.toBoolTapes
      (MachineExpanderFamily.familyTapes H (PCP.PreprocessingLevels.boundedLevel requested) []) tape
  | .inr tape => retainedCeilingTapes requested tape

@[simp] theorem initialTapes_input (requested : Nat) :
    initialTapes requested (.inr .input) = encodeWord requested := rfl

@[simp] theorem finalTapes_input (H : SmallTable) (requested : Nat) :
    finalTapes H requested (.inr .input) = encodeWord requested := rfl

@[simp] theorem finalTapes_power (H : SmallTable) (requested : Nat) :
    finalTapes H requested (.inr .power) =
      encodeWord (PCP.PreprocessingLevels.paddedSize requested) := rfl

end IndependentSetsGames.Foundations.Complexity.MachinePaddedExpanderFamily

end OAI
