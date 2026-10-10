import OAI.Computability.UniqueGames.Machines.MachineCeilingPower
import OAI.Computability.UniqueGames.Machines.MachineCloudPadding
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineExpanderFamily
import OAI.Computability.UniqueGames.Machines.MachineExpanderFamilyBoundsLemmas
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamilyBounds

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

def timeCoefficient : Nat :=
  MachineExpanderFamilyBounds.inputCoefficient + PCP.ExpanderFamily.growth + 29

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C timeCoefficient * Polynomial.X^5

theorem timePolynomial_encoding (k : Nat) :
    timePolynomial.eval (encodeWord k).length = timeCoefficient * (k + 1)^5 := by
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, encodeWord_length]

theorem ceilingCost_le (g k : Nat) :
    (MachineCeilingPower.timePolynomial g).eval (encodeWord k).length ≤
      (g + 29) * (k + 1)^5 := by
  rw [MachineCeilingPower.timePolynomial_encoding]
  have squareBound : (k + 1)^2 ≤ (k + 1)^5 :=
    Nat.pow_le_pow_right (Nat.succ_pos k) (by decide)
  have linearBound : k + 1 ≤ (k + 1)^5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (Nat.succ_pos k) (show 1 ≤ 5 by decide)
  have constantBound : 1 ≤ (k + 1)^5 := by omega
  have squareCost := Nat.mul_le_mul_left (g + 8) squareBound
  have linearCost := Nat.mul_le_mul_left 18 linearBound
  have constantCost := Nat.mul_le_mul_left 3 constantBound
  unfold MachineCeilingPower.timeBound
  nlinarith only [squareCost, linearCost, constantCost]

theorem combinedCost_le (k : Nat) :
    (MachineCeilingPower.timePolynomial PCP.ExpanderFamily.growth).eval
        (encodeWord k).length +
      MachineExpanderFamilyBounds.inputCoefficient * (k + 1)^5 ≤
        timePolynomial.eval (encodeWord k).length := by
  rw [timePolynomial_encoding]
  have h := ceilingCost_le PCP.ExpanderFamily.growth k
  unfold timeCoefficient
  nlinarith only [h]

theorem familyCost_le
    (H : Table (cloudSize PCP.Expanders.baseDegree) PCP.Expanders.baseDegree) (k : Nat) :
    (MachineCeilingPower.timePolynomial PCP.ExpanderFamily.growth).eval
        (encodeWord k).length +
      MachineExpanderFamilyBounds.familyBudget H (PCP.PreprocessingLevels.boundedLevel k) ≤
        timePolynomial.eval (encodeWord k).length := by
  exact (Nat.add_le_add_left
    (MachineExpanderFamilyBounds.familyBudget_at_boundedLevel_le H k) _).trans
      (combinedCost_le k)

def outputWord
    (H : Table (cloudSize PCP.Expanders.baseDegree) PCP.Expanders.baseDegree) (k : Nat) :
    List Bool :=
  encodeWords (rotationWords (family H (PCP.PreprocessingLevels.boundedLevel k)))

def outputCoefficient : Nat :=
  (PCP.ExpanderFamily.growth * degree PCP.Expanders.baseDegree + 1)^2

/-- Complete unary rotation-table output, including every delimiter. -/
theorem outputWord_length_le
    (H : Table (cloudSize PCP.Expanders.baseDegree) PCP.Expanders.baseDegree) (k : Nat) :
    (outputWord H k).length ≤ outputCoefficient * (k + 1)^2 := by
  let q := degree PCP.Expanders.baseDegree
  let N := vertexCount q (PCP.PreprocessingLevels.boundedLevel k)
  have sizeBound : N ≤ PCP.ExpanderFamily.growth * (k + 1) := by
    change vertexCount (PCP.Expanders.baseDegree * PCP.Expanders.baseDegree)
      (PCP.PreprocessingLevels.boundedLevel k) ≤ _
    rw [PCP.PreprocessingLevels.table_vertexCount_eq_paddedSize]
    exact MachineExpanderFamilyBounds.paddedSize_le_succ_input k
  have rowBound := Nat.mul_le_mul_right q sizeBound
  have rowSuccBound : N * q + 1 ≤ (PCP.ExpanderFamily.growth * q + 1) * (k + 1) := by
    nlinarith only [rowBound, Nat.zero_le k]
  have lengthBound : (outputWord H k).length ≤ (N * q) * (N * q + 1) :=
    encode_rotationWords_length_le (family H (PCP.PreprocessingLevels.boundedLevel k))
  calc
    _ ≤ (N * q + 1)^2 := by nlinarith only [lengthBound, Nat.zero_le (N * q)]
    _ ≤ ((PCP.ExpanderFamily.growth * q + 1) * (k + 1))^2 :=
      Nat.pow_le_pow_left rowSuccBound 2
    _ = _ := by unfold outputCoefficient; dsimp [q]; ring

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamilyBounds


namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily

open Turing

section TableCoordinates

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

/-- The only shared tape is the level: the first phase writes the exact word
that the second phase's unary guard consumes. -/
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
    | inr j =>
      cases j <;> simp_all [ceilingView, ceilingTape]
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

section Placement

variable {ρ : Type} [Fintype ρ]

/-- The family retains the completed ceiling machine's two finite registers. -/
def familySource (H : SmallTable) : MachineExpanderFamily.Label fixedDegree →
    TM2.Stmt MachineExpanderFamily.BoolAlphabet
      (MachineExpanderFamily.Label fixedDegree) (State ρ) :=
  MachineStateFrame.frameProgram (τ := Bool × Option Bool)
    (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one)

/-- The ceiling program preserves the family state as its ambient component. -/
def ceilingSource : MachineCeilingPower.Label →
    TM2.Stmt MachineCeilingPower.Alphabet MachineCeilingPower.Label (State ρ) :=
  MachineStateEquiv.program (ceilingStates ρ)
    (MachineCeilingPower.program PCP.ExpanderFamily.growth)

/-- Actual composition on shared Boolean tapes. No runtime bridge operation
is required, because both programs use the same physical level tape. -/
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

/-- Initial state for an arbitrary preserved family-state component. -/
def initialState (state : MachineExpanderFamily.State ρ fixedDegree)
    (register : Option Bool) : State ρ := (state, (false, register))

def finalState (H : SmallTable) (state : MachineExpanderFamily.State ρ fixedDegree) : State ρ :=
  (MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H
    (MachineExpanderFamily.caller state), (false, none))

/-- Only the unary request is initially present. -/
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

end Placement

open MachineCloudPadding PCP.ExpanderTableWords

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

/-- The produced unary level is already on the exact family input tape. -/
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

/-- Ceiling halt enters the family initializer with no intervening transition. -/
theorem ceiling_handoff_configuration {ρ : Type} (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) :
    Placement.configuration ceilingView ceilingLabel (some familyEntry) (fun _ => [])
      (MachineStateEquiv.configuration (ceilingStates ρ)
        ⟨none, ((state, false), none), ceilingOutput requested⟩) =
      ⟨some familyEntry, (state, (false, none)), handoffTapes requested⟩ := by
  simp only [Placement.configuration, Placement.label, MachineStateEquiv.configuration,
    ceilingStates_apply, ceiling_handoff_tapes]

/-- Static alphabet and state framing of the actual family initial endpoint. -/
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

/-- The family endpoint retains both external ceiling words and its original
normalized state; its remaining-level word is the consumed zero word. -/
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

end TableCoordinates


/-!
# Actual requested-size to expander-table computation

One finite program physically computes the padding level and then constructs
the complete corresponding rotation table. The level output of the first
phase is the input tape of the second phase. The actual execution preserves
the request, retains the padded size, and has a fixed polynomial time bound
in the unary request length.
-/

open MachineCloudPadding MachineComposition

variable {ρ : Type} [Fintype ρ]

/-- Actual geometric search, placed onto the eventual family-level tape. -/
noncomputable def ceilingInTime (H : SmallTable) (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some main, initialState state register, initialTapes requested⟩
      (some ⟨some familyEntry, (state, (false, none)), handoffTapes requested⟩)
      ((MachineCeilingPower.timePolynomial PCP.ExpanderFamily.growth).eval
        (encodeWord requested).length) := by
  let original := MachineCeilingPower.paddingInTime requested state register
  let renamed := MachineStateEquiv.execution (ceilingStates ρ)
    (MachineCeilingPower.program PCP.ExpanderFamily.growth) original
  let placed := liftExecutionInTime (TM2.step (ceilingSource (ρ := ρ)))
    (TM2.step (program H))
    (Placement.configuration ceilingView ceilingLabel (some familyEntry) (fun _ => []))
    (Placement.step_simulation ceilingTape ceilingView ceilingView_left ceilingView_right
      ceilingLabel (some familyEntry) (fun _ => []) (ceilingSource (ρ := ρ))
      (program H) (program_ceiling H)) renamed
  have initialEq := ceiling_initial_configuration requested state register
  have finalEq := ceiling_handoff_configuration requested state
  unfold ceilingInput at initialEq
  unfold ceilingOutput at finalEq
  simpa only [initialEq, finalEq] using placed

/-- Actual table materialization consumes the level produced by the preceding
phase while retaining the original request and its computed padded size. -/
noncomputable def materializeInTime (H : SmallTable) (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some familyEntry, (state, (false, none)), handoffTapes requested⟩
      (some ⟨none, finalState H state, finalTapes H requested⟩)
      (MachineExpanderFamilyBounds.inputCoefficient * (requested + 1)^5) := by
  let original := MachineExpanderFamily.paddedFamilyInTime H requested state []
  let boolean := MachineAlphabetTransport.executionInTime MachineExpanderFamily.alphabet_eq
    (MachineExpanderFamily.program MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one) original
  let framed := MachineStateFrame.frameExecution
    (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one) (false, (none : Option Bool)) boolean
  let placed := liftExecutionInTime (TM2.step (familySource H)) (TM2.step (program H))
    (Placement.configuration familyView familyLabel none (retainedFrame requested))
    (Placement.step_simulation familyTape familyView familyView_left familyView_right
      familyLabel none (retainedFrame requested) (familySource H) (program H)
      (program_family H)) framed
  simpa only [family_initial_configuration, family_final_configuration] using placed

/-- A single concrete finite program takes the original unary request all the
way to the exact forward family table. Both phase executions are supplied by
proved machines; there is no construction or runtime hypothesis. -/
noncomputable def paddedInTime (H : SmallTable) (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some main, initialState state register, initialTapes requested⟩
      (some ⟨none, finalState H state, finalTapes H requested⟩)
      (MachinePaddedExpanderFamilyBounds.timePolynomial.eval (encodeWord requested).length) := by
  let first := ceilingInTime H requested state register
  let second := materializeInTime H requested state
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program H))
    _ _ _ _ _ first second
  exact
    { toEvalsTo := all.toEvalsTo
      steps_le_m := all.steps_le_m.trans
        (by simpa only [Nat.add_comm] using
          MachinePaddedExpanderFamilyBounds.combinedCost_le requested) }

/-- Static placements of the complete computation into a larger caller
preserve every complement tape and consume exactly the same runtime budget. -/
noncomputable def placedInTime {K Λ : Type} [DecidableEq K]
    (tape : Tape → K) (view : K → Option Tape)
    (left : ∀ t, view (tape t) = some t)
    (right : ∀ j t, view j = some t → tape t = j)
    (labels : Label → Λ) (exit : Option Λ) (extra : K → List Bool)
    (H : SmallTable) (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ))
    (code : ∀ l, target (labels l) = Placement.statement tape labels exit (program H l))
    (requested : Nat) (state : MachineExpanderFamily.State ρ fixedDegree)
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step target)
      (Placement.configuration view labels exit extra
        ⟨some main, initialState state register, initialTapes requested⟩)
      (some (Placement.configuration view labels exit extra
        ⟨none, finalState H state, finalTapes H requested⟩))
      (MachinePaddedExpanderFamilyBounds.timePolynomial.eval (encodeWord requested).length) :=
  liftExecutionInTime (TM2.step (program H)) (TM2.step target)
    (Placement.configuration view labels exit extra)
    (Placement.step_simulation tape view left right labels exit extra (program H) target code)
    (paddedInTime H requested state register)

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily

end OAI
