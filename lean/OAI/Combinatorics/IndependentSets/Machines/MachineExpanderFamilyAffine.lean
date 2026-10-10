import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineExpanderFamilyTransfer

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineExpanderFamily

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

theorem affine_source_ne_scratch (phase : AffinePhase) :
    affineSource phase ≠ .inr .unaryScratch := by cases phase <;> decide

theorem affine_source_ne_destination (phase : AffinePhase) :
    affineSource phase ≠ affineDestination phase := by cases phase <;> decide

theorem affine_scratch_ne_destination (phase : AffinePhase) :
    (.inr .unaryScratch : Tape) ≠ affineDestination phase := by cases phase <;> decide

def affineResultTapes (d : Nat) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) :
    (tape : Tape) → List (Alphabet tape) :=
  Function.update base (affineDestination phase)
    (boolWord (affineDestination phase)
      (encodeWord (affineCoefficient d phase * n) ++ toBoolTapes base (affineDestination phase)))

theorem affineResultTapes_other (d : Nat) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) (tape : Tape)
    (different : tape ≠ affineDestination phase) :
    affineResultTapes d phase base n tape = base tape := by
  simp [affineResultTapes, different]

theorem affineResultTapes_source (d : Nat) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) :
    affineResultTapes d phase base n (affineSource phase) = base (affineSource phase) :=
  affineResultTapes_other d phase base n _ (affine_source_ne_destination phase)

theorem affineResultTapes_scratch (d : Nat) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) :
    affineResultTapes d phase base n (.inr .unaryScratch) = base (.inr .unaryScratch) :=
  affineResultTapes_other d phase base n _ (affine_scratch_ne_destination phase)

theorem affineResultTapes_destination (d : Nat) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) :
    toBoolTapes (affineResultTapes d phase base n) (affineDestination phase) =
      encodeWord (affineCoefficient d phase * n) ++ toBoolTapes base (affineDestination phase) := by
  simp [affineResultTapes, toBoolTapes]

variable {ρ : Type} [Fintype ρ] {d : Nat}

theorem affinePhaseBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (phase : AffinePhase) (base : Tape → List Bool)
    (n : Nat) (suffix : List Bool)
    (sourceWord : base (affineSource phase) = encodeWord n ++ suffix)
    (scratchEmpty : base (.inr .unaryScratch) = []) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[2 * (n + 1) + 1]
      (some ⟨some (.inr (.affine phase .seed)), state, base⟩) =
      some ⟨some (affineExit d phase), clearRegister state,
        Function.update base (affineDestination phase)
          (encodeWord (affineCoefficient d phase * n) ++ base (affineDestination phase))⟩ := by
  let states := registerStates ρ d
  let target := boolView (ρ := ρ) positive H growth
  let sourceProgram := MachineControl.program (Equiv.refl (Label d)) states.symm target
  have atSeed : sourceProgram (.inr (.affine phase .seed)) =
      MachineUnaryAffineAt.seed (affineDestination phase) 0 (.inr (.affine phase .scan)) := by
    change MachineControl.statement id states.symm
      (boolView positive H growth (.inr (.affine phase .seed))) = _
    rw [boolView_outer]
    exact controlStatementInverse states _
  have atScan : sourceProgram (.inr (.affine phase .scan)) =
      MachineUnaryAffineAt.scan (affineSource phase) (.inr .unaryScratch)
        (affineDestination phase) (affineCoefficient d phase)
        (.inr (.affine phase .scan)) (.inr (.affine phase .restore)) := by
    change MachineControl.statement id states.symm
      (boolView positive H growth (.inr (.affine phase .scan))) = _
    rw [boolView_outer]
    exact controlStatementInverse states _
  have atRestore : sourceProgram (.inr (.affine phase .restore)) =
      Reduction.MachineTransfer.loopAt (.inr .unaryScratch) (affineSource phase) id false
        (.inr (.affine phase .restore)) (some (affineExit d phase)) := by
    change MachineControl.statement id states.symm
      (boolView positive H growth (.inr (.affine phase .restore))) = _
    rw [boolView_outer]
    exact controlStatementInverse states _
  have raw := MachineUnaryAffineAt.seededAffineTrace
    (affineSource phase) (.inr .unaryScratch) (affineDestination phase)
    (affine_source_ne_scratch phase) (affine_source_ne_destination phase)
    (affine_scratch_ne_destination phase) (affineCoefficient d phase) 0
    (.inr (.affine phase .seed)) (.inr (.affine phase .scan)) (.inr (.affine phase .restore))
    (some (affineExit d phase)) sourceProgram atSeed atScan atRestore base n suffix
    sourceWord scratchEmpty (states.symm state).1 (states.symm state).2
  have run := controlTrace states target (2 * (n + 1) + 1) _ _ raw
  simpa only [states, target, MachineControl.configuration, Option.map_some, id_eq, Prod.mk.eta,
    Equiv.apply_symm_apply, Nat.add_zero, registerStates_reset] using run

theorem affinePhaseTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) (suffix : List Bool)
    (sourceWord : toBoolTapes base (affineSource phase) = encodeWord n ++ suffix)
    (scratchEmpty : base (.inr .unaryScratch) = []) (state : State ρ d) :
    (advance (TM2.step (program positive H growth)))^[2 * (n + 1) + 1]
      (some ⟨some (.inr (.affine phase .seed)), state, base⟩) =
      some ⟨some (affineExit d phase), clearRegister state,
        affineResultTapes d phase base n⟩ := by
  have raw := affinePhaseBoolTrace positive H growth phase (toBoolTapes base) n suffix
    sourceWord scratchEmpty state
  have transported := boolTraceActual positive H growth (2 * (n + 1) + 1) _ _ raw
  simpa only [configuration_fromBool, fromBoolTapes_update, fromBool_toBool,
    affineResultTapes] using transported

def affinePhaseInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) (suffix : List Bool)
    (sourceWord : toBoolTapes base (affineSource phase) = encodeWord n ++ suffix)
    (scratchEmpty : base (.inr .unaryScratch) = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr (.affine phase .seed)), state, base⟩
      (some ⟨some (affineExit d phase), clearRegister state,
        affineResultTapes d phase base n⟩) (2 * (n + 1) + 1) where
  steps := 2 * (n + 1) + 1
  evals_in_steps := affinePhaseTrace positive H growth phase base n suffix sourceWord scratchEmpty state
  steps_le_m := Nat.le_refl _

def copyCountInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (n : Nat) (sourceWord : base (.inr .currentSize) = encodeWord n)
    (scratchEmpty : base (.inr .unaryScratch) = [])
    (destinationEmpty : base vertexCountTape = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr (.affine .copyCount .seed)), state, base⟩
      (some ⟨some (.inl (.inr .initialize)), clearRegister state,
        Function.update base vertexCountTape (encodeWord n)⟩) (2 * (n + 1) + 1) := by
  have run := affinePhaseInTime positive H growth .copyCount base n []
    (by simpa only [affineSource, toBoolTapes, toBoolWord, List.append_nil] using sourceWord)
    scratchEmpty state
  change base (.inl (.inr .vertexCount)) = [] at destinationEmpty
  simpa only [affineExit, affineResultTapes, affineDestination, affineCoefficient,
    Nat.one_mul, vertexCountTape, boolWord, toBoolTapes, toBoolWord,
    destinationEmpty, List.append_nil] using run

def multiplySizeInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (n : Nat) (sourceWord : base inputVertexTape = encodeWord n)
    (scratchEmpty : base (.inr .unaryScratch) = [])
    (destinationEmpty : base (.inr .currentSize) = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr (.affine .multiplySize .seed)), state, base⟩
      (some ⟨some (.inr .drainInputVertex), clearRegister state,
        Function.update base (.inr .currentSize) (encodeWord (cloudSize d * n))⟩)
      (2 * (n + 1) + 1) := by
  have run := affinePhaseInTime positive H growth .multiplySize base n []
    (by simpa only [affineSource, inputVertexTape, toBoolTapes, toBoolWord,
      List.append_nil] using sourceWord)
    scratchEmpty state
  simpa only [affineExit, affineResultTapes, affineDestination, affineCoefficient,
    boolWord, toBoolTapes, toBoolWord, destinationEmpty, List.append_nil] using run

end IndependentSetsGames.Foundations.Complexity.MachineExpanderFamily

end OAI
