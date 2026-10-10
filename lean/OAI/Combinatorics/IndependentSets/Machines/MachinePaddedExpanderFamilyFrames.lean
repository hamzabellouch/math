import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachinePaddedExpanderFamilyProgram

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachinePaddedExpanderFamily

open Turing
open MachineCloudPadding
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

def ceilingInput (requested : Nat) : MachineCeilingPower.Tape → List Bool :=
  MachineCeilingPower.memory (encodeWord requested) [] [] [] [] [] [] []

def ceilingOutput (requested : Nat) : MachineCeilingPower.Tape → List Bool :=
  MachineCeilingPower.memory (encodeWord requested) []
    (encodeWord (PCP.PreprocessingLevels.paddedSize requested)) []
    (encodeWord (PCP.PreprocessingLevels.boundedLevel requested)) [] [] []

def retainedFrame (requested : Nat) : Tape → List Bool
  | .inl _ => []
  | .inr tape => retainedCeilingTapes requested tape

theorem ceiling_initial_tapes (requested : Nat) :
    Placement.tapes ceilingView (ceilingInput requested) (fun _ => []) =
      initialTapes requested := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with tape | tape
    · rfl
    · cases tape <;> rfl
  · cases tape <;> rfl

theorem ceiling_handoff_tapes (requested : Nat) :
    Placement.tapes ceilingView (ceilingOutput requested) (fun _ => []) =
      handoffTapes requested := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with tape | tape
    · rcases tape with tape | tape
      · cases tape <;> rfl
      · cases tape <;> rfl
    · cases tape <;>
        simp [Placement.tapes, ceilingView, ceilingOutput, handoffTapes,
          MachineExpanderFamily.toBoolTapes, MachineExpanderFamily.toBoolWord,
          MachineExpanderFamily.initialTapes, MachineEmbedding.tapes,
          MachineCeilingPower.memory]
  · cases tape <;> rfl

theorem family_initial_tapes (requested : Nat) :
    Placement.tapes familyView
      (MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.initialTapes (PCP.PreprocessingLevels.boundedLevel requested) []))
      (retainedFrame requested) = handoffTapes requested := by
  funext tape
  cases tape <;> rfl

theorem family_final_tapes (H : SmallTable) (requested : Nat) :
    Placement.tapes familyView
      (MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.familyTapes H (PCP.PreprocessingLevels.boundedLevel requested) []))
      (retainedFrame requested) = finalTapes H requested := by
  funext tape
  cases tape <;> rfl

theorem ceiling_initial_configuration {ρ : Type} (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) (register : Option Bool) :
    Placement.configuration ceilingView ceilingLabel (some familyEntry) (fun _ => [])
      (MachineStateEquiv.configuration (ceilingStates ρ)
        ⟨some .init, ((state, false), register), ceilingInput requested⟩) =
      ⟨some main, initialState state register, initialTapes requested⟩ := by
  simp only [Placement.configuration, Placement.label, MachineStateEquiv.configuration,
    ceilingStates_apply, ceiling_initial_tapes, ceilingLabel, main, initialState]

theorem ceiling_handoff_configuration {ρ : Type} (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) :
    Placement.configuration ceilingView ceilingLabel (some familyEntry) (fun _ => [])
      (MachineStateEquiv.configuration (ceilingStates ρ)
        ⟨none, ((state, false), none), ceilingOutput requested⟩) =
      ⟨some familyEntry, (state, (false, none)), handoffTapes requested⟩ := by
  simp only [Placement.configuration, Placement.label, MachineStateEquiv.configuration,
    ceilingStates_apply, ceiling_handoff_tapes]

theorem family_initial_configuration {ρ : Type} (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) (metadata : Bool × Option Bool) :
    Placement.configuration familyView familyLabel none (retainedFrame requested)
      (MachineStateFrame.frameConfiguration metadata
        (MachineAlphabetTransport.configuration MachineExpanderFamily.alphabet_eq
          ⟨some (.inr .initialize), state,
            MachineExpanderFamily.initialTapes (PCP.PreprocessingLevels.boundedLevel requested) []⟩)) =
      ⟨some familyEntry, (state, metadata), handoffTapes requested⟩ := by
  rw [MachineExpanderFamily.configuration_toBool]
  simp only [MachineStateFrame.frameConfiguration, Placement.configuration, Placement.label,
    family_initial_tapes, familyEntry, familyLabel]

theorem family_final_configuration {ρ : Type} (H : SmallTable) (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) :
    Placement.configuration familyView familyLabel none (retainedFrame requested)
      (MachineStateFrame.frameConfiguration (false, none)
        (MachineAlphabetTransport.configuration MachineExpanderFamily.alphabet_eq
          ⟨none,
            MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H
              (MachineExpanderFamily.caller state),
            MachineExpanderFamily.familyTapes H (PCP.PreprocessingLevels.boundedLevel requested) []⟩)) =
      ⟨none, finalState H state, finalTapes H requested⟩ := by
  rw [MachineExpanderFamily.configuration_toBool]
  simp only [MachineStateFrame.frameConfiguration, Placement.configuration, Placement.label,
    family_final_tapes, finalState]

@[simp] theorem handoffTapes_level (requested : Nat) :
    handoffTapes requested (ceilingTape .level) =
      encodeWord (PCP.PreprocessingLevels.boundedLevel requested) := by
  simp [handoffTapes, ceilingTape, MachineExpanderFamily.toBoolTapes,
    MachineExpanderFamily.toBoolWord, MachineExpanderFamily.initialTapes,
    MachineEmbedding.tapes]

@[simp] theorem handoffTapes_level_shadow (requested : Nat) :
    handoffTapes requested (.inr .level) = [] := rfl

@[simp] theorem finalTapes_level_shadow (H : SmallTable) (requested : Nat) :
    finalTapes H requested (.inr .level) = [] := rfl

@[simp] theorem finalTapes_remainingLevel (H : SmallTable) (requested : Nat) :
    finalTapes H requested (ceilingTape .level) = encodeWord 0 := by
  simp [finalTapes, ceilingTape, MachineExpanderFamily.toBoolTapes,
    MachineExpanderFamily.toBoolWord, MachineExpanderFamily.familyTapes,
    MachineExpanderFamily.boundaryTapes, MachineExpanderFamily.extraFrame,
    MachineEmbedding.tapes]

theorem finalTapes_currentSize (H : SmallTable) (requested : Nat) :
    finalTapes H requested (familyTape (.inr .currentSize)) =
      encodeWord (PCP.PreprocessingLevels.paddedSize requested) := by
  change encodeWord (vertexCount (degree fixedDegree)
    (PCP.PreprocessingLevels.boundedLevel requested)) = _
  exact congrArg encodeWord (PCP.PreprocessingLevels.table_vertexCount_eq_paddedSize requested)

theorem finalTapes_table (H : SmallTable) (requested : Nat) :
    finalTapes H requested (familyTape MachineExpanderFamily.tableTape) =
      encodeWords (rotationWords (family H (PCP.PreprocessingLevels.boundedLevel requested))) := rfl

end IndependentSetsGames.Foundations.Complexity.MachinePaddedExpanderFamily

end OAI
