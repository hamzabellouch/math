import OAI.Computability.UniqueGames.PCP.AlphabetReductionLemmas
import OAI.Computability.UniqueGames.PCP.AlphabetRetractionLemmas
import OAI.Computability.UniqueGames.PCP.AmplificationIteration
import OAI.Computability.UniqueGames.PCP.FinalBooleanVerifier
import OAI.Computability.UniqueGames.PCP.PreprocessingTablesLemmas
import OAI.Computability.UniqueGames.PCP.RoundSize
import OAI.Computability.UniqueGames.PCP.SourceAddressArithmeticLemmas
import OAI.Computability.UniqueGames.PCP.SourceHonestLemmas
import OAI.Computability.UniqueGames.PCP.SourceLoopInitLemmas
import OAI.Computability.UniqueGames.PCP.SourceNoiseParameterLemmas
import OAI.Computability.UniqueGames.PCP.SourceQueryLoopLemmas
import OAI.Computability.UniqueGames.PCP.SourceQueryOrderLemmas
import OAI.Computability.UniqueGames.PCP.SourceRuntimeSpace
import OAI.Computability.UniqueGames.PCP.SourceSignaturePrepareLemmas
import OAI.Computability.UniqueGames.PCP.SourceTupleBody
import OAI.Computability.UniqueGames.PCP.SourceTupleBound
import OAI.Computability.UniqueGames.Reduction.FinalParametersLemmas

namespace OAI


namespace UniqueGamesTheorem.Foundations.Hastad.SourceGap

section Repetition

open Target SourceContexts SourceOccurrences SourceGame
open UniqueGamesTheorem.Integration.SourceParameters
open UniqueGamesTheorem.Reduction

/-- A clause gap includes nonemptiness: a cross-multiplied inequality alone
would hold vacuously for a formula with no clauses. -/
def ClauseGap (F : Formula) (η : ℚ) : Prop :=
  F.clauses ≠ [] ∧ ∀ assignment : Fin F.variables → Bool,
    (η : ℝ) * F.clauses.length ≤
      (PCP.failureCount F assignment (PCP.allIndices F) : ℝ)

theorem third_pos {η : ℚ} (hη : 0 < η) : 0 < η / 3 := by positivity

theorem third_le_one {η : ℚ} (hη : η ≤ 1) : η / 3 ≤ 1 := by linarith

/-- The repetition count is computed once from the gap, target error, and
noise denominator, independently of the input formula. -/
def repetitionCount (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (D : ℕ) (hD : 0 < D) : ℕ :=
  repetitionLength (η / 3) ξ (third_pos hη) (third_le_one hη1) hξ D hD

theorem repetitionCount_pos (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hξ : 0 < ξ) (D : ℕ) (hD : 0 < D) :
    0 < repetitionCount η ξ hη hη1 hξ D hD :=
  (repetitionLength_spec (η / 3) ξ (third_pos hη) (third_le_one hη1) hξ D hD).1

theorem repeated_game_bound (F : Formula) (η ξ : ℚ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ) (D : ℕ) (hD : 0 < D)
    (hgap : ClauseGap F η) :
    ((baseGame F hgap.1).repetition
      (repetitionCount η ξ hη hη1 hξ D hD)).value ≤
        4 * (D : ℝ)⁻¹ * (ξ : ℝ)^2 := by
  have hb : (baseGame F hgap.1).value ≤ 1 - ((η / 3 : ℚ) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      base_value_le_of_clause_gap F hgap.1 (η : ℝ) hgap.2
  have hc : Fintype.card Bool * Fintype.card PCP.ClauseAnswer = 16 := by
    simp
  exact (game_repetition_rate (baseGame F hgap.1) (third_pos hη)
    (third_le_one hη1) hc hb _).trans
      (repetitionLength_real_bound (η / 3) ξ (third_pos hη)
        (third_le_one hη1) hξ D hD)

/-- The actual nonempty, numbered occurrence list at the fixed parameters. -/
def source (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (D : ℕ) (hD : 0 < D) (F : Formula) : SourceEncoding.Input :=
  sourceInput F (repetitionCount η ξ hη hη1 hξ D hD) D hD

theorem source_complete (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (D : ℕ) (hD : 0 < D) (hnoise : (D : ℚ)⁻¹ ≤ ξ)
    (F : Formula) (hF : F.Satisfiable) :
    ∃ bits : Fin (source η ξ hη hη1 hξ D hD F).variables → Bool,
      1 - ξ ≤ (((source η ξ hη hη1 hξ D hD F).equations.countP
        (fun e => CloneGap.satisfied e bits) : ℚ) /
          (source η ξ hη hη1 hξ D hD F).equations.length) := by
  obtain ⟨assignment, hs⟩ := hF
  refine ⟨SourceHonest.honestBits F _ assignment, ?_⟩
  have h := SourceHonest.sourceList_honest_acceptance_rat F
    (repetitionCount η ξ hη hη1 hξ D hD) D hD assignment hs
  exact (sub_le_sub_left hnoise 1).trans h

theorem source_sound (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (D : ℕ) (hD : 0 < D) (hDtwo : 2 ≤ D)
    (F : Formula) (hgap : ClauseGap F η)
    (bits : Fin (source η ξ hη hη1 hξ D hD F).variables → Bool) :
    ((source η ξ hη hη1 hξ D hD F).equations.countP
      (fun e => CloneGap.satisfied e bits) : ℚ) /
        (source η ξ hη hη1 hξ D hD F).equations.length ≤ (1 + ξ) / 2 :=
  SourceSoundness.sourceList_sound_rat F hgap.1
    (repetitionCount η ξ hη hη1 hξ D hD) D hD hDtwo ξ hξ.le
      (repeated_game_bound F η ξ hη hη1 hξ D hD hgap) bits

theorem source_size (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (D : ℕ) (hD : 0 < D) :
    ∃ p : Polynomial ℕ, ∀ F : Formula,
      (SourceEncoding.inputBits (source η ξ hη hη1 hξ D hD F)).length ≤
        p.eval (Complexity.formulaBits F).length :=
  SourceBounds.fixed_parameters_source_size (repetitionCount η ξ hη hη1 hξ D hD) D hD

end Repetition

open Target SourceNoiseParameter UniqueGamesTheorem.Reduction

def forError (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ) :
    Formula → SourceEncoding.Input :=
  source η ξ hη hη1 hξ (noiseDenominator ξ) (noiseDenominator_pos ξ)

theorem forError_complete (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (F : Formula) (hF : F.Satisfiable) :
    ∃ bits : Fin (forError η ξ hη hη1 hξ F).variables → Bool,
      1 - ξ ≤ ((forError η ξ hη hη1 hξ F).equations.countP
        (fun e => CloneGap.satisfied e bits) : ℚ) /
          (forError η ξ hη hη1 hξ F).equations.length :=
  source_complete η ξ hη hη1 hξ (noiseDenominator ξ) (noiseDenominator_pos ξ)
    (noiseDenominator_inv_le hξ) F hF

theorem forError_sound (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (F : Formula) (hgap : ClauseGap F η)
    (bits : Fin (forError η ξ hη hη1 hξ F).variables → Bool) :
    ((forError η ξ hη hη1 hξ F).equations.countP
      (fun e => CloneGap.satisfied e bits) : ℚ) /
        (forError η ξ hη hη1 hξ F).equations.length ≤ (1 + ξ) / 2 :=
  source_sound η ξ hη hη1 hξ (noiseDenominator ξ) (noiseDenominator_pos ξ)
    (noiseDenominator_ge_two ξ) F hgap bits

theorem forError_size (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ) :
    ∃ p : Polynomial ℕ, ∀ F : Formula,
      (SourceEncoding.inputBits (forError η ξ hη hη1 hξ F)).length ≤
        p.eval (Complexity.formulaBits F).length :=
  source_size η ξ hη hη1 hξ (noiseDenominator ξ) (noiseDenominator_pos ξ)

end UniqueGamesTheorem.Foundations.Hastad.SourceGap



namespace UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorContract

open Target Complexity

abbrev NonemptyFormula := { F : Formula // F.clauses ≠ [] }

def inputEncoding (F : NonemptyFormula) : List Bool := formulaBits F.val

def sourceMap (u D : Nat) (hD : 0 < D) (F : NonemptyFormula) :
    UniqueGamesTheorem.Reduction.SourceEncoding.Input :=
  SourceOccurrences.sourceInput F.val u D hD

def errorMap (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (F : NonemptyFormula) : UniqueGamesTheorem.Reduction.SourceEncoding.Input :=
  SourceGap.forError η ξ hη hη1 hξ F.val

theorem inputEncoding_mk (F : Formula) (hne : F.clauses ≠ []) :
    inputEncoding ⟨F, hne⟩ = formulaBits F := rfl

end UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorContract



namespace UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorProgram

open Turing Complexity SourceGeneratorModel

noncomputable section


abbrev Tape (u D : Nat) := SourceGeneratorModel.Tape u D
abbrev Ambient (u D : Nat) := SourceGeneratorModel.ControlAmbient u D
abbrev State (u D : Nat) := Ambient u D × Option Bool

local instance (u D : Nat) : DecidableEq (Extra u D) := Classical.decEq _

inductive Label (u D : Nat)
  | startup (label : SourceStartup.Label u D)
  | body (label : SourceTupleBody.Label u D (Extra u D))
  | check (coordinate : Fin u)
  | reset (coordinate : Fin u)
  | finishEnter
  | finish (label : SourceRuntimeFinish.Label (clearKeys u D))
  deriving DecidableEq, Fintype

def bodyEntry (u D : Nat) : Label u D := .body SourceTupleBody.main

def next (u D : Nat) (i : Nat) : Label u D :=
  if h : i < u then .check ⟨i, h⟩ else .finishEnter

def sourceStateEquiv (u D : Nat) : SourceRuntimeModel.State u D × Unit ≃ State u D where
  toFun x := (controlStateEquiv u D).symm x.1
  invFun x := (controlStateEquiv u D x, ())
  left_inv x := by cases x with | mk x y => cases y; simp
  right_inv x := by simp

def program (u D : Nat) (hD : 0 < D) :
    Label u D → TM2.Stmt (fun _ : Tape u D => Bool) (Label u D) (State u D)
  | .startup l => SourceTupleBody.framed (sourceStateEquiv u D) Label.startup
      (some (bodyEntry u D)) (SourceStartup.program l)
  | .body l => SourceTupleBody.framed (sourceStateEquiv u D) Label.body
      (some (next u D 0))
      (SourceTupleBody.program (initialQuery u D hD) none l)
  | .check i => MachineTupleOdometer.increment
      (.current i) (.remaining i) (bodyEntry u D) (.reset i)
  | .reset i => MachineTupleOdometer.reset
      (.current i) (.remaining i) (.reset i) (next u D (i.val + 1))
  | .finishEnter => Reduction.MachineTransfer.exitAt (accumulatorTape u D)
      (SourceRuntimeFinish.entry (clearKeys u D) Label.finish)
  | .finish l => SourceRuntimeFinish.statement (clearKeys u D)
      (accumulatorTape u D) (outputTape u D) (initialAmbient u D hD)
      Label.finish none l

def main (u D : Nat) : Label u D := .startup (.inl .inputCopyOut)

def machine (u D : Nat) (hD : 0 < D) : FinTM2 where
  K := Tape u D
  k₀ := .formula
  k₁ := outputTape u D
  Γ _ := Bool
  Λ := Label u D
  main := main u D
  σ := State u D
  initialState := (initialAmbient u D hD, none)
  m := program u D hD

theorem finite_work_alphabets (u D : Nat) (hD : 0 < D)
    (k : (machine u D hD).K) : Finite ((machine u D hD).Γ k) := by
  change Finite Bool
  infer_instance

theorem atCheck (u D : Nat) (hD : 0 < D) (i : Fin u) :
    program u D hD (.check i) = MachineTupleOdometer.increment
      (.current i) (.remaining i) (bodyEntry u D) (.reset i) := rfl

theorem atReset (u D : Nat) (hD : 0 < D) (i : Fin u) :
    program u D hD (.reset i) = MachineTupleOdometer.reset
      (.current i) (.remaining i) (.reset i) (next u D (i.val + 1)) := rfl

end

end UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorProgram



namespace UniqueGamesTheorem.Foundations.Hastad.SourceGenerator
open Turing Complexity Target
open SourceGeneratorModel SourceGeneratorProgram SourceGeneratorContract
noncomputable section
variable {u D : Nat}
local instance : DecidableEq (Extra u D) := Classical.decEq _

theorem source_initial (u D : Nat) (hD : 0 < D) :
    sourceStateEquiv u D (SourceGeneratorModel.initialState u D hD, ()) =
      (initialAmbient u D hD, none) := rfl

theorem initial_configuration (F : Formula) (hD : 0 < D) :
    initList (SourceGeneratorProgram.machine u D hD) (formulaBits F) =
      (⟨some (SourceGeneratorProgram.main u D), (initialAmbient u D hD, none),
        SourceStartup.initialTapes F⟩ : (SourceGeneratorProgram.machine u D hD).Cfg) := by
  simp only [initList, SourceGeneratorProgram.machine]
  congr 1
  funext k
  by_cases hk : k = SourceContextLoad.Tape.formula
  · subst k
    simp [SourceStartup.initialTapes]
    rfl
  · simp [SourceStartup.initialTapes, hk]

def startupInTime (F : Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    StateTransition.EvalsToInTime (SourceGeneratorProgram.machine u D hD).step
      (initList (SourceGeneratorProgram.machine u D hD) (formulaBits F))
      (some ⟨some (bodyEntry u D), (initialAmbient u D hD, none), SourceStartup.readyTapes F⟩)
      ((SourceStartup.timePolynomial u D).eval (formulaBits F).length) := by
  have run := SourceTupleBody.framedExecution (sourceStateEquiv u D)
    SourceGeneratorProgram.Label.startup (some (bodyEntry u D)) ()
    SourceStartup.program (SourceGeneratorProgram.program u D hD) (fun _ => rfl)
    (SourceStartup.startupInPolynomialTime (u := u) F hm hD)
  rw [initial_configuration F hD]
  simpa only [SourceTupleBody.framedConfiguration, MachineStateFrame.configuration,
    MachineControl.configuration, MachineSubroutine.configuration,
    MachineStateFrame.frameConfiguration, MachineSubroutine.label, source_initial,
    Option.map_some, Option.map_none, id_eq, SourceGeneratorProgram.main,
    FinTM2.step, FinTM2.Cfg, SourceGeneratorProgram.machine] using! run

end
end UniqueGamesTheorem.Foundations.Hastad.SourceGenerator



namespace UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorTraversal

open Turing Complexity SourceContexts SourceOccurrences SourceRuntimeModel
open SourceGeneratorModel SourceGeneratorProgram SourceOdometerSchedule


noncomputable section

variable {u D : Nat}

local instance (u D : Nat) : DecidableEq (SourceGeneratorModel.Extra u D) := Classical.decEq _

def accumulatorRole (u D : Nat) : BodyExtra (SourceGeneratorModel.Extra u D) :=
  .inr .accumulator

def leafTapes (F : Target.Formula) (c : ClauseContext F u) (output : List Bool) :
    SourceGeneratorModel.Tape u D → List Bool :=
  setDigits F.clauses.length (fun i => (c i).val)
    (setAcc (accumulatorRole u D) (SourceStartup.readyTapes F) output)

@[simp] theorem leaf_accumulator (F : Target.Formula) (c : ClauseContext F u) (output : List Bool) :
    leafTapes (D := D) F c output (accumulatorTape u D) = output := by
  exact setAcc_apply (accumulatorRole u D) (SourceStartup.readyTapes F) output

theorem leaf_work_blank (F : Target.Formula) (c : ClauseContext F u) (output : List Bool)
    (role : BodyWork (SourceGeneratorModel.Extra u D))
    (hl : role ≠ .leftBlock) (hd : role ≠ .dummy) (ha : role ≠ .accumulator) :
    leafTapes F c output (workTape role) = [] := by
  change (Function.update (SourceStartup.readyTapes F) (accumulatorTape u D) output)
    (workTape role) = []
  rw [Function.update_of_ne (by simpa [workTape, accumulatorTape] using ha)]
  exact SourceStartup.ready_work_blank F role hl hd ha

/-- Every concrete tuple and arbitrary accumulated prefix satisfies the actual
body's representation invariant after startup. -/
theorem leaf_ready (F : Target.Formula) (c : ClauseContext F u) (output : List Bool) :
    SourceTupleBody.Ready F c (leafTapes (D := D) F c output) := by
  constructor
  · simp [leafTapes, setDigits, setAcc, accumulatorRole]
  · intro i
    simp [leafTapes, setDigits]
  · change (SourceStartup.readyTapes (u := u) (D := D) F) .index = []
    exact SourceStartup.ready_sharedFrame F _ (Or.inl rfl)
  · change (SourceStartup.readyTapes (u := u) (D := D) F) .work = []
    exact SourceStartup.ready_sharedWork F
  · change (SourceStartup.readyTapes (u := u) (D := D) F) .scratch = []
    exact SourceStartup.ready_sharedFrame F _ (Or.inr (Or.inl rfl))
  · change (SourceStartup.readyTapes (u := u) (D := D) F) .copyScratch = []
    exact SourceStartup.ready_sharedFrame F _ (Or.inr (Or.inr rfl))
  · intro i s
    simp [leafTapes, setDigits, setAcc, accumulatorRole]
  · change (SourceStartup.readyTapes (u := u) (D := D) F) variableHeader = encodeWord F.variables
    exact SourceStartup.ready_variableHeader F
  · change (SourceStartup.readyTapes (u := u) (D := D) F) clauseHeader = encodeWord F.clauses.length
    exact SourceStartup.ready_clauseHeader F
  · change (SourceStartup.readyTapes (u := u) (D := D) F) (workTape .leftBlock) = _
    exact SourceStartup.ready_leftBlock F
  · change (SourceStartup.readyTapes (u := u) (D := D) F) (workTape .dummy) = _
    simpa only [SourceHeaderCounts.dummyValue, SourceHeaderCounts.leftValue,
      SourceHeaderCounts.rightValue, Nat.mul_comm] using SourceStartup.ready_dummy (u := u) (D := D) F
  all_goals apply leaf_work_blank F c output _ <;> simp

/-- The actual body's accumulator update has exactly the endpoint expected by
the nested odometer schedule. -/
theorem body_result_leaf (F : Target.Formula) (c : ClauseContext F u)
    (output bits : List Bool) :
    SourceTestAppend.resultTapes queryLayout (leafTapes (D := D) F c output) bits =
      leafTapes F c (bits.reverse ++ output) := by
  change setAcc (accumulatorRole u D) (leafTapes F c output)
    (bits.reverse ++ leafTapes F c output (accumulatorTape u D)) = _
  rw [leaf_accumulator]
  unfold leafTapes
  rw [setDigits_setAcc, setAcc_setAcc, ← setDigits_setAcc]

@[simp] theorem source_initial (hD : 0 < D) :
    sourceStateEquiv u D (canonicalState (initialQuery u D hD), ()) =
      (initialAmbient u D hD, none) := rfl

/-- The body-run premise of the odometer is discharged by the checked body
machine and its fixed polynomial bound, in this same final generator program. -/
theorem actual_bodies (F : Target.Formula) (hD : 0 < D) :
    BodyTrace (SourceGeneratorProgram.program u D hD) (bodyEntry u D) (next u D 0)
      (initialAmbient u D hD) (accumulatorRole u D) (SourceStartup.readyTapes F)
      (SourceQueryOrder.tupleBits F u D)
      ((SourceTupleBound.bodyPolynomial u D).eval (formulaBits F).length) := by
  intro c output
  obtain ⟨run⟩ := SourceTupleBound.bodyInPolynomialTime F c (initialQuery u D hD) none
    (leafTapes (D := D) F c output) (leaf_ready F c output)
  have lifted := SourceTupleBody.framedExecution (sourceStateEquiv u D)
    SourceGeneratorProgram.Label.body (some (next u D 0)) ()
    (SourceTupleBody.program (initialQuery u D hD) none)
    (SourceGeneratorProgram.program u D hD) (fun _ => rfl) run
  refine ⟨lifted.steps, lifted.steps_le_m, ?_⟩
  have ht := lifted.evals_in_steps
  change (MachineComposition.advance (TM2.step (SourceGeneratorProgram.program u D hD)))^[lifted.steps]
    _ = _ at ht
  simp only [body_result_leaf] at ht
  simpa only [SourceTupleBody.framedConfiguration, MachineControl.configuration,
    MachineStateFrame.configuration, MachineStateFrame.frameConfiguration,
    MachineSubroutine.configuration, MachineSubroutine.label, Option.map_some,
    Option.map_none, id_eq, source_initial, configuration,
    bodyEntry, leafTapes] using ht

/-- Startup already supplies exactly the reset odometer digits. -/
theorem resetDigits_ready (F : Target.Formula) :
    setDigits F.clauses.length (fun _ : Fin u => 0)
      (SourceStartup.readyTapes (u := u) (D := D) F) = SourceStartup.readyTapes F := by
  funext k
  cases k <;> simp [setDigits]

theorem allBits_eq_records (F : Target.Formula) (hne : F.clauses ≠ []) :
    allBits (SourceQueryOrder.tupleBits F u D) =
      (sourceList F u D).flatMap (fun e =>
        encodeWords (UniqueGamesTheorem.Reduction.SourceEncoding.equationWords e)) := by
  rw [sourceList_nonempty F u D hne]
  unfold allBits SourceQueryOrder.tupleBits SourceQueryOrder.slotBits
    SourceQueryOrder.occurrenceBits
  simp only [rawSourceList, occurrenceList,
    sourceIndexEncoding, Encoding.enumerate_prod, List.flatMap_map, List.flatMap_assoc,
    clauseEncoding, Encoding.enumerate_fin_function]

/-- Include the exact reversed header already emitted by startup. -/
theorem accumulated_eq_input (F : Target.Formula) (hD : 0 < D) (hne : F.clauses ≠ []) :
    (allBits (SourceQueryOrder.tupleBits F u D)).reverse ++
        SourceStartup.readyTapes F (accumulatorTape u D) =
      (UniqueGamesTheorem.Reduction.SourceEncoding.inputBits (sourceInput F u D hD)).reverse := by
  rw [allBits_eq_records F hne, SourceStartup.ready_accumulator]
  have hi := SourceLoopOrder.inputBits_eq_header_records (sourceInput F u D hD)
  change UniqueGamesTheorem.Reduction.SourceEncoding.inputBits (sourceInput F u D hD) =
    encodeWords [nBits F u, (sourceList F u D).length] ++
      (sourceList F u D).flatMap (fun e =>
        encodeWords (UniqueGamesTheorem.Reduction.SourceEncoding.equationWords e)) at hi
  rw [hi, List.reverse_append]

def traversalOutput (F : Target.Formula) (hD : 0 < D) : SourceGeneratorModel.Tape u D → List Bool :=
  Function.update (SourceStartup.readyTapes F) (accumulatorTape u D)
    (UniqueGamesTheorem.Reduction.SourceEncoding.inputBits (sourceInput F u D hD)).reverse

@[simp] theorem traversalOutput_accumulator (F : Target.Formula) (hD : 0 < D) :
    traversalOutput F hD (accumulatorTape u D) =
      (UniqueGamesTheorem.Reduction.SourceEncoding.inputBits (sourceInput F u D hD)).reverse := by
  simp [traversalOutput]

theorem traversalOutput_frame (F : Target.Formula) (hD : 0 < D)
    (k : SourceGeneratorModel.Tape u D) (hk : k ≠ accumulatorTape u D) :
    traversalOutput F hD k = SourceStartup.readyTapes F k := by
  simp [traversalOutput, hk]

def resetLabel (u D : Nat) (i : Nat) : SourceGeneratorProgram.Label u D :=
  if h : i < u then .reset ⟨i, h⟩ else .finishEnter

/-- Actual traversal of every clause tuple, with each digit physically reset.
All nonaccumulator tapes have exactly their startup-ready contents. -/
theorem traversalInTime (F : Target.Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step (SourceGeneratorProgram.program u D hD))
      ⟨some (bodyEntry u D), (initialAmbient u D hD, none), SourceStartup.readyTapes F⟩
      (some ⟨some .finishEnter, (initialAmbient u D hD, none), traversalOutput F hD⟩)
      (((SourceTupleBound.bodyPolynomial u D).eval (formulaBits F).length + 2 * u) *
        F.clauses.length ^ u)) := by
  have hne : F.clauses ≠ [] := List.length_pos_iff.mp hm
  obtain ⟨run⟩ := SourceOdometerSchedule.traversalInTime
    (SourceGeneratorProgram.program u D hD) (bodyEntry u D) (next u D) (resetLabel u D)
    (initialAmbient u D hD) (accumulatorRole u D) hm
    ((SourceTupleBound.bodyPolynomial u D).eval (formulaBits F).length)
    (SourceStartup.readyTapes F) (SourceQueryOrder.tupleBits F u D)
    (by intro i hi
        simp only [next, resetLabel, currentAt, remainingAt, hi, ↓reduceDIte]
        rfl)
    (by intro i hi
        simp only [resetLabel, currentAt, remainingAt, hi, ↓reduceDIte]
        rfl)
    (actual_bodies F hD)
  refine ⟨?_⟩
  have hs : initialConfiguration (m := F.clauses.length) u (bodyEntry u D)
      (initialAmbient u D hD) (SourceStartup.readyTapes F) =
      (⟨some (bodyEntry u D), (initialAmbient u D hD, none), SourceStartup.readyTapes F⟩ :
        TM2.Cfg (fun _ : SourceGeneratorModel.Tape u D => Bool)
          (SourceGeneratorProgram.Label u D) (SourceGeneratorProgram.State u D)) := by
    rw [initialConfiguration, configuration, resetDigits_ready]
  have hf : finalConfiguration (next u D u) (initialAmbient u D hD) (accumulatorRole u D)
      (SourceStartup.readyTapes F) (SourceQueryOrder.tupleBits F u D) =
      (⟨some .finishEnter, (initialAmbient u D hD, none), traversalOutput F hD⟩ :
        TM2.Cfg (fun _ : SourceGeneratorModel.Tape u D => Bool)
          (SourceGeneratorProgram.Label u D) (SourceGeneratorProgram.State u D)) := by
    unfold finalConfiguration configuration
    rw [setDigits_setAcc, resetDigits_ready]
    change (⟨some (next u D u), (initialAmbient u D hD, none),
      setAcc (accumulatorRole u D) (SourceStartup.readyTapes F)
        ((allBits (SourceQueryOrder.tupleBits F u D)).reverse ++
          SourceStartup.readyTapes F (accumulatorTape u D))⟩ :
        TM2.Cfg (fun _ : SourceGeneratorModel.Tape u D => Bool)
          (SourceGeneratorProgram.Label u D) (SourceGeneratorProgram.State u D)) = _
    rw [accumulated_eq_input F hD hne]
    simp only [next, Nat.lt_irrefl, ↓reduceDIte]
    rfl
  simpa only [hs, hf] using run

def timePolynomial (u D : Nat) : Polynomial Nat :=
  (SourceTupleBound.bodyPolynomial u D + Polynomial.C (2 * u)) * Polynomial.X ^ u

theorem traversalInPolynomialTime (F : Target.Formula)
    (hm : 0 < F.clauses.length) (hD : 0 < D) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step (SourceGeneratorProgram.program u D hD))
      ⟨some (bodyEntry u D), (initialAmbient u D hD, none), SourceStartup.readyTapes F⟩
      (some ⟨some .finishEnter, (initialAmbient u D hD, none), traversalOutput F hD⟩)
      ((timePolynomial u D).eval (formulaBits F).length)) := by
  obtain ⟨run⟩ := traversalInTime F hm hD
  refine ⟨{ toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }⟩
  apply run.steps_le_m.trans
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  exact Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (SourceBounds.formulaBits_length_ge_clauses F) u)

end

end UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorTraversal



namespace UniqueGamesTheorem.Foundations.Hastad.SourceGenerator

open Turing Complexity Target
open SourceGeneratorModel SourceGeneratorProgram SourceGeneratorContract

noncomputable section


variable {u D : Nat}
local instance : DecidableEq (Extra u D) := Classical.decEq _

def prefixPolynomial (u D : Nat) : Polynomial Nat :=
  SourceStartup.timePolynomial u D + SourceGeneratorTraversal.timePolynomial u D + 1

def timePolynomial (u D : Nat) (hD : 0 < D) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (SourceGeneratorProgram.machine u D hD)
    (clearKeys u D).length (prefixPolynomial u D)

def beforeFinish (F : Formula) (hD : 0 < D) : (SourceGeneratorProgram.machine u D hD).Cfg :=
  ⟨SourceRuntimeFinish.entry (clearKeys u D) SourceGeneratorProgram.Label.finish,
    (initialAmbient u D hD, none), SourceGeneratorTraversal.traversalOutput F hD⟩

def enterFinishInTime (F : Formula) (hD : 0 < D) :
    StateTransition.EvalsToInTime (SourceGeneratorProgram.machine u D hD).step
      ⟨some .finishEnter, (initialAmbient u D hD, none),
        SourceGeneratorTraversal.traversalOutput F hD⟩
      (some (beforeFinish F hD)) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux
      (Reduction.MachineTransfer.exitAt (accumulatorTape u D)
        (SourceRuntimeFinish.entry (clearKeys u D) SourceGeneratorProgram.Label.finish))
      _ _) = _
    cases h : SourceRuntimeFinish.entry (clearKeys u D) SourceGeneratorProgram.Label.finish <;>
      simp only [Reduction.MachineTransfer.exitAt, beforeFinish, TM2.stepAux] <;>
      erw [h] <;> rfl
  steps_le_m := Nat.le_refl _

def prefixInTime (F : Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    StateTransition.EvalsToInTime (SourceGeneratorProgram.machine u D hD).step
      (initList (SourceGeneratorProgram.machine u D hD) (formulaBits F))
      (some (beforeFinish F hD)) ((prefixPolynomial u D).eval (formulaBits F).length) := by
  have start := startupInTime (u := u) F hm hD
  let traversal := Classical.choice (SourceGeneratorTraversal.traversalInPolynomialTime
    (u := u) F hm hD)
  have first := StateTransition.EvalsToInTime.trans
    (SourceGeneratorProgram.machine u D hD).step _ _ _ _ _ start traversal
  have joined := StateTransition.EvalsToInTime.trans
    (SourceGeneratorProgram.machine u D hD).step _ _ _ _ _ first (enterFinishInTime F hD)
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  apply joined.steps_le_m.trans
  simp only [prefixPolynomial, Polynomial.eval_add, Polynomial.eval_one]
  omega

theorem output_empty (F : Formula) (hD : 0 < D) :
    SourceGeneratorTraversal.traversalOutput F hD (outputTape u D) = [] := by
  rw [SourceGeneratorTraversal.traversalOutput_frame F hD _
    (Ne.symm (accumulator_ne_output u D))]
  exact SourceStartup.ready_work_blank F (.extra (.inr ()))
    (by simp) (by simp) (by simp)

theorem halted_configuration (F : Formula) (hD : 0 < D) :
    (⟨none, (initialAmbient u D hD, none),
      SourceRuntimeFinish.canonicalTapes (outputTape u D)
        (SourceGeneratorTraversal.traversalOutput F hD (accumulatorTape u D)).reverse⟩ :
      (SourceGeneratorProgram.machine u D hD).Cfg) =
      haltList (SourceGeneratorProgram.machine u D hD)
        (UniqueGamesTheorem.Reduction.SourceEncoding.inputBits (SourceOccurrences.sourceInput F u D hD)) := by
  rw [SourceGeneratorTraversal.traversalOutput_accumulator, List.reverse_reverse]
  simp only [haltList, SourceGeneratorProgram.machine]
  congr 1
  funext k
  by_cases hk : k = outputTape u D
  · subst k
    simp [SourceRuntimeFinish.canonicalTapes]
    erw [Function.update_self]
    rfl
  · simp [SourceRuntimeFinish.canonicalTapes, hk]
    erw [Function.update_of_ne hk]

def outputInTime (F : NonemptyFormula) (hD : 0 < D) :
    TM2OutputsInTime (SourceGeneratorProgram.machine u D hD) (inputEncoding F)
      (some (UniqueGamesTheorem.Reduction.SourceEncoding.inputBits (sourceMap u D hD F)))
      ((timePolynomial u D hD).eval (inputEncoding F).length) := by
  have hm : 0 < F.val.clauses.length := List.length_pos_iff.mpr F.property
  have prefixRun := prefixInTime (u := u) F.val hm hD
  have keepAcc : accumulatorTape u D ∉ clearKeys u D := by
    simp [mem_clearKeys]
  have keepOut : outputTape u D ∉ clearKeys u D := by
    simp [mem_clearKeys]
  have covers : ∀ k, k ≠ accumulatorTape u D → k ≠ outputTape u D → k ∈ clearKeys u D :=
    fun k ha ho => (mem_clearKeys u D k).mpr ⟨ha, ho⟩
  have finish := SourceRuntimeFinish.finishInTime (clearKeys u D)
    (accumulatorTape u D) (outputTape u D) (accumulator_ne_output u D)
    keepAcc keepOut covers (initialAmbient u D hD) SourceGeneratorProgram.Label.finish none
    (SourceGeneratorProgram.program u D hD) (fun _ => rfl)
    (SourceGeneratorTraversal.traversalOutput F.val hD) (output_empty F.val hD)
    (initialAmbient u D hD) none
  erw [halted_configuration F.val hD] at finish
  have joined := SourceRuntimeSpace.prefixAndFinishInTime
    (SourceGeneratorProgram.machine u D hD) (formulaBits F.val) (prefixPolynomial u D)
    prefixRun (clearKeys u D) (accumulatorTape u D) (outputTape u D)
    keepAcc keepOut covers (SourceGeneratorTraversal.traversalOutput F.val hD)
    (output_empty F.val hD) (fun _ => rfl) finish
  exact joined

def computableInPolyTime (u D : Nat) (hD : 0 < D) :
    TM2ComputableInPolyTime inputEncoding UniqueGamesTheorem.Reduction.SourceEncoding.inputBits
      (sourceMap u D hD) where
  tm := SourceGeneratorProgram.machine u D hD
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial u D hD
  outputsFun F := by
    change TM2OutputsInTime (machine u D hD) ((inputEncoding F).map id)
      (some ((UniqueGamesTheorem.Reduction.SourceEncoding.inputBits (sourceMap u D hD F)).map id)) _
    have input_eq : @List.map ((machine u D hD).Γ (machine u D hD).k₀)
        ((machine u D hD).Γ (machine u D hD).k₀) id (inputEncoding F) =
        inputEncoding F := List.map_id _
    have output_eq : @List.map ((machine u D hD).Γ (machine u D hD).k₁)
        ((machine u D hD).Γ (machine u D hD).k₁) id
        (UniqueGamesTheorem.Reduction.SourceEncoding.inputBits (sourceMap u D hD F)) =
        UniqueGamesTheorem.Reduction.SourceEncoding.inputBits (sourceMap u D hD F) := List.map_id _
    simpa only [input_eq, output_eq] using outputInTime (u := u) F hD

theorem finite_work_alphabets (u D : Nat) (hD : 0 < D)
    (k : (computableInPolyTime u D hD).tm.K) :
    Finite ((computableInPolyTime u D hD).tm.Γ k) := by
  change Finite Bool
  infer_instance

def forErrorComputableInPolyTime (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ) :
    TM2ComputableInPolyTime inputEncoding UniqueGamesTheorem.Reduction.SourceEncoding.inputBits
      (errorMap η ξ hη hη1 hξ) := by
  let D := SourceNoiseParameter.noiseDenominator ξ
  let hD := SourceNoiseParameter.noiseDenominator_pos ξ
  let u := SourceGap.repetitionCount η ξ hη hη1 hξ D hD
  exact computableInPolyTime u D hD

theorem forError_finite_work_alphabets (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (k : (forErrorComputableInPolyTime η ξ hη hη1 hξ).tm.K) :
    Finite ((forErrorComputableInPolyTime η ξ hη hη1 hξ).tm.Γ k) := by
  change Finite Bool
  infer_instance

end

end UniqueGamesTheorem.Foundations.Hastad.SourceGenerator



namespace UniqueGamesTheorem.Foundations.Hastad.SourceNonempty

open Target PCP

/-- Convert an actual natural-number clause-count inequality to the real
inequality used by the clause-variable game. -/
theorem real_clause_gap_of_count (F : Formula) (a b : ℕ) (hb : 0 < b)
    (hgap : ∀ assignment : Fin F.variables → Bool,
      a * F.clauses.length ≤ b * NameCompaction.failedCount F assignment)
    (assignment : Fin F.variables → Bool) :
    (a : ℝ) / (b : ℝ) * F.clauses.length ≤
      (failureCount F assignment (allIndices F) : ℝ) := by
  rw [NameCompaction.verifier_failureCount]
  have hreal : (a : ℝ) * F.clauses.length ≤
      (b : ℝ) * (NameCompaction.failedCount F assignment : ℝ) := by
    exact_mod_cast hgap assignment
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hb)).mpr
  simpa only [mul_comm] using hreal

theorem clauseGap_of_count (F : Formula) (a b : ℕ) (hne : F.clauses ≠ [])
    (hb : 0 < b)
    (hgap : ∀ assignment : Fin F.variables → Bool,
      a * F.clauses.length ≤ b * NameCompaction.failedCount F assignment) :
    SourceGap.ClauseGap F ((a : ℚ) / (b : ℚ)) := by
  refine ⟨hne, fun assignment => ?_⟩
  simpa only [Rat.cast_div, Rat.cast_natCast] using
    real_clause_gap_of_count F a b hb hgap assignment

variable {V E : Type*} {n m : ℕ}

/-- The actual final graph bundle carries a nonempty dart type, so its
explicitly numbered Boolean CNF is nonempty even before using any gap. -/
theorem cnf_nonempty_of_nonempty_darts [Fintype E] [Nonempty E]
    (G : ConstraintGraph V E FinalBooleanVerifier.Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) :
    (FinalBooleanVerifier.cnf G vertices edges).clauses ≠ [] := by
  have hcard : Fintype.card E = m := by
    simpa only [Fintype.card_fin] using Fintype.card_congr edges
  have hm : 0 < m := hcard ▸ Fintype.card_pos
  exact FinalBooleanVerifier.cnf_nonempty G vertices edges hm

/-- The checked final Boolean-verifier count bound produces exactly the
nonempty clause-gap premise of SourceGap, with denominator `40960 * b`. -/
theorem cnf_clauseGap [Fintype E] [Nonempty E]
    (G : ConstraintGraph V E FinalBooleanVerifier.Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (a b : ℕ) (hb : 0 < b)
    (hgap : ∀ labeling : V → FinalBooleanVerifier.Label,
      a * Fintype.card E ≤ b * G.rejectionCount labeling) :
    SourceGap.ClauseGap (FinalBooleanVerifier.cnf G vertices edges)
      ((a : ℚ) / ((b : ℚ) * 40960)) := by
  have h := clauseGap_of_count (FinalBooleanVerifier.cnf G vertices edges) a (b * 40960)
    (cnf_nonempty_of_nonempty_darts G vertices edges)
    (Nat.mul_pos hb (by decide)) (FinalBooleanVerifier.cnf_gap G vertices edges a b hgap)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

/-- The unit-numerator gap supplied by the final powering stage has the
fixed rational clause gap `1 / (40960 * walkLength)`. -/
theorem cnf_clauseGap_unit [Fintype E] [Nonempty E]
    (G : ConstraintGraph V E FinalBooleanVerifier.Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (walkLength : ℕ)
    (hwalk : 0 < walkLength)
    (hgap : ∀ labeling : V → FinalBooleanVerifier.Label,
      Fintype.card E ≤ walkLength * G.rejectionCount labeling) :
    SourceGap.ClauseGap (FinalBooleanVerifier.cnf G vertices edges)
      (1 / (40960 * (walkLength : ℚ))) := by
  have h := cnf_clauseGap G vertices edges 1 walkLength hwalk
    (by simpa only [one_mul] using hgap)
  simpa only [Nat.cast_one, mul_comm] using h

end UniqueGamesTheorem.Foundations.Hastad.SourceNonempty


section

/-!
The actual finite graph iteration used by the mathematical PCP construction.
One fixed, explicitly supplied complete address list is shared by every round.
Each round constructs a new constraint graph. The scalar gap and size are the
actual minimum rejection fraction and actual finite cardinalities of that graph.

The final Boolean formula uses supplied vertex and dart numberings. These
theorems establish the finite objects and their size/gap properties, not a
machine running-time theorem or an independently encoded NP-hardness theorem.
-/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.PCPIteration

open FiniteGraph

abbrev Label := AlphabetRetraction.Label64
abbrev Graph := Bundle Label
abbrev Addresses := AmplificationRound.Addresses

def step (addresses : List Addresses) (complete : ∀ w, w ∈ addresses) (G : Graph) : Graph := by
  classical
  exact Bundle.ofGraph (AmplificationRound.graph addresses complete G.graph)

def run (addresses : List Addresses) (complete : ∀ w, w ∈ addresses) : Nat → Graph → Graph :=
  AmplificationIteration.run (step addresses complete)

def initial (F : Target.Formula) : Graph := Bundle.ofGraph (AlphabetRetraction.initial64 F)

def iterationCount (F : Target.Formula) : Nat := AmplificationIteration.rounds (initial F).size

def output (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (F : Target.Formula) : Graph := run addresses complete (iterationCount F) (initial F)

/-- Fixed exponent; the enormous fixed graph constants remain unevaluated. -/
def polynomialDegree : Nat := AmplificationIteration.rounds RoundSize.sizeFactor

def finalClauseGap : ℚ := 1 / (40960 * (FinalConstants.walkLength : ℚ))

theorem finalClauseGap_positive : 0 < finalClauseGap := by
  apply one_div_pos.mpr
  exact mul_pos (by norm_num) (by exact_mod_cast FinalConstants.walkLength_positive)

theorem sizeFactor_le_power : RoundSize.sizeFactor ≤ 2 ^ polynomialDegree :=
  (AmplificationIteration.rounds_large RoundSize.sizeFactor).le

theorem initial_satisfiable_iff (F : Target.Formula) :
    (initial F).Satisfiable ↔ F.Satisfiable :=
  AlphabetRetraction.initial64_satisfiable_iff F

theorem initial_size_positive (F : Target.Formula) : 0 < (initial F).size :=
  (initial F).size_positive

theorem initial_size_bound (F : Target.Formula) :
    (initial F).size ≤ 10 * F.clauses.length + 2 := by
  change Fintype.card (InitialGraph.CompactVertex F) +
    Fintype.card (InitialGraph.CompactDart F) ≤ _
  rw [InitialGraph.build_dart_count]
  have h := InitialGraph.build_vertex_bound F
  omega

theorem step_completeness (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (G : Graph) (satisfied : G.Satisfiable) : (step addresses complete G).Satisfiable :=
  AmplificationRound.completeness addresses complete G.graph satisfied

theorem step_gap (addresses : List Addresses) (complete : ∀ w, w ∈ addresses) (G : Graph) :
    min (2 * G.gap) FinalConstants.cap ≤ (step addresses complete G).gap :=
  RoundGap.amplifies addresses complete G.graph

theorem step_size (addresses : List Addresses) (complete : ∀ w, w ∈ addresses) (G : Graph) :
    (step addresses complete G).size ≤ RoundSize.sizeFactor * G.size :=
  RoundSize.output_total_le G.graph

theorem run_completeness (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (n : Nat) (G : Graph) (satisfied : G.Satisfiable) :
    (run addresses complete n G).Satisfiable :=
  AmplificationIteration.run_preserves (step addresses complete) Bundle.Satisfiable
    (step_completeness addresses complete) n G satisfied

theorem run_gap (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (n : Nat) (G : Graph) :
    min (2 ^ n * G.gap) FinalConstants.cap ≤ (run addresses complete n G).gap :=
  AmplificationIteration.run_gap (step addresses complete) Bundle.gap
    FinalConstants.cap FinalConstants.cap_positive.le (step_gap addresses complete) n G

theorem run_size (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (n : Nat) (G : Graph) :
    (run addresses complete n G).size ≤ RoundSize.sizeFactor ^ n * G.size :=
  AmplificationIteration.run_size (step addresses complete) Bundle.size RoundSize.sizeFactor
    (step_size addresses complete) n G

theorem output_completeness (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (F : Target.Formula) (satisfied : F.Satisfiable) :
    (output addresses complete F).Satisfiable :=
  run_completeness addresses complete (iterationCount F) (initial F)
    ((initial_satisfiable_iff F).mpr satisfied)

/-- The actual graph reaches the fixed positive gap after the concrete number
of rounds determined by its initial total size. -/
theorem output_gap (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (F : Target.Formula) (unsat : ¬ F.Satisfiable) :
    FinalConstants.cap ≤ (output addresses complete F).gap := by
  have hinitial : ¬ (initial F).Satisfiable :=
    fun h => unsat ((initial_satisfiable_iff F).mp h)
  exact AmplificationIteration.run_reaches_cap (step addresses complete) Bundle.gap
    FinalConstants.cap FinalConstants.cap_positive.le FinalConstants.cap_le_one
    (step_gap addresses complete) (initial F).size (initial F)
    (initial F).gap_nonnegative ((initial F).one_le_size_mul_gap hinitial)

theorem output_satisfiable_iff (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (F : Target.Formula) : (output addresses complete F).Satisfiable ↔ F.Satisfiable := by
  constructor
  · intro satisfied
    by_contra unsat
    have hgap := output_gap addresses complete F unsat
    rw [(output addresses complete F).gap_eq_zero_iff.mpr satisfied] at hgap
    exact (not_le_of_gt FinalConstants.cap_positive) hgap
  · exact output_completeness addresses complete F

theorem output_size_polynomial (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (F : Target.Formula) :
    (output addresses complete F).size ≤
      (2 * (initial F).size) ^ polynomialDegree * (initial F).size :=
  AmplificationIteration.run_size_polynomial (step addresses complete) Bundle.size
    (initial_size_positive F) sizeFactor_le_power (step_size addresses complete) (initial F)

theorem output_size_clause_bound (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (F : Target.Formula) :
    (output addresses complete F).size ≤
      (2 * (10 * F.clauses.length + 2)) ^ polynomialDegree * (10 * F.clauses.length + 2) := by
  have h := initial_size_bound F
  exact (output_size_polynomial addresses complete F).trans
    (Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 h) _) h)

theorem output_count_gap (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (F : Target.Formula) (unsat : ¬ F.Satisfiable)
    (labeling : (output addresses complete F).Vertex → Label) :
    Fintype.card (output addresses complete F).Dart ≤
      FinalConstants.walkLength * (output addresses complete F).rejectionCount labeling := by
  have h := ((output addresses complete F).le_gap_iff FinalConstants.cap).mp
    (output_gap addresses complete F unsat) labeling
  have ht : (0 : ℝ) < FinalConstants.walkLength := by
    exact_mod_cast FinalConstants.walkLength_positive
  have h' : (Fintype.card (output addresses complete F).Dart : ℝ) /
      FinalConstants.walkLength ≤
      ((output addresses complete F).rejectionCount labeling : ℝ) := by
    simpa only [FinalConstants.cap, one_div_mul_eq_div] using h
  have h'' := (div_le_iff₀ ht).mp h'
  exact_mod_cast (show (Fintype.card (output addresses complete F).Dart : ℝ) ≤
    (FinalConstants.walkLength : ℝ) *
      ((output addresses complete F).rejectionCount labeling : ℝ) by
        simpa only [mul_comm] using h'')

section FinalCNF

variable (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
  (F : Target.Formula) {n m : Nat}
  (vertices : (output addresses complete F).Vertex ≃ Fin n)
  (darts : (output addresses complete F).Dart ≃ Fin m)

def finalCNF : Target.Formula :=
  FinalBooleanVerifier.cnf (output addresses complete F).graph vertices darts

theorem finalCNF_satisfiable_iff :
    (finalCNF addresses complete F vertices darts).Satisfiable ↔ F.Satisfiable :=
  (FinalBooleanVerifier.cnf_satisfiable_iff _ vertices darts).trans
    (output_satisfiable_iff addresses complete F)

theorem finalCNF_clause_count :
    (finalCNF addresses complete F vertices darts).clauses.length = m * 40960 :=
  FinalBooleanVerifier.cnf_clause_count _ vertices darts

theorem finalCNF_variable_count :
    (finalCNF addresses complete F vertices darts).variables = n * 6 + m * 36864 :=
  FinalBooleanVerifier.cnf_variable_count _ vertices darts

theorem finalCNF_nonempty : (finalCNF addresses complete F vertices darts).clauses ≠ [] := by
  have hm : Fintype.card (output addresses complete F).Dart = m := by
    simpa only [Fintype.card_fin] using Fintype.card_congr darts
  have hpositive : 0 < m := hm ▸ (Fintype.card_pos :
    0 < Fintype.card (output addresses complete F).Dart)
  exact FinalBooleanVerifier.cnf_nonempty _ vertices darts hpositive

theorem finalCNF_gap (unsat : ¬ F.Satisfiable)
    (assignment : Fin (finalCNF addresses complete F vertices darts).variables → Bool) :
    (finalCNF addresses complete F vertices darts).clauses.length ≤
      (FinalConstants.walkLength * 40960) *
        NameCompaction.failedCount (finalCNF addresses complete F vertices darts) assignment := by
  have source (labeling : (output addresses complete F).Vertex → Label) :
      1 * Fintype.card (output addresses complete F).Dart ≤
        FinalConstants.walkLength * (output addresses complete F).graph.rejectionCount labeling := by
    simpa only [one_mul, Bundle.rejectionCount] using output_count_gap addresses complete F unsat labeling
  simpa only [one_mul, finalCNF] using FinalBooleanVerifier.cnf_gap
    (output addresses complete F).graph vertices darts 1 FinalConstants.walkLength source assignment

theorem finalCNF_clauseGap (unsat : ¬ F.Satisfiable) :
    Hastad.SourceGap.ClauseGap (finalCNF addresses complete F vertices darts) finalClauseGap :=
  Hastad.SourceNonempty.cnf_clauseGap_unit (output addresses complete F).graph
    vertices darts FinalConstants.walkLength FinalConstants.walkLength_positive
    (output_count_gap addresses complete F unsat)

theorem finalCNF_total_size :
    (finalCNF addresses complete F vertices darts).variables +
        (finalCNF addresses complete F vertices darts).clauses.length ≤
      77824 * (output addresses complete F).size := by
  have hn : Fintype.card (output addresses complete F).Vertex = n := by
    simpa only [Fintype.card_fin] using Fintype.card_congr vertices
  have hm : Fintype.card (output addresses complete F).Dart = m := by
    simpa only [Fintype.card_fin] using Fintype.card_congr darts
  have hsize : (output addresses complete F).size = n + m := congrArg₂ Nat.add hn hm
  calc
    _ = n * 6 + m * 36864 + m * 40960 :=
      congrArg₂ Nat.add (finalCNF_variable_count addresses complete F vertices darts)
        (finalCNF_clause_count addresses complete F vertices darts)
    _ ≤ 77824 * (n + m) := by omega
    _ = 77824 * (output addresses complete F).size :=
      congrArg (fun k => 77824 * k) hsize.symm

theorem finalCNF_polynomial_size :
    (finalCNF addresses complete F vertices darts).variables +
        (finalCNF addresses complete F vertices darts).clauses.length ≤
      77824 * ((2 * (10 * F.clauses.length + 2)) ^ polynomialDegree *
        (10 * F.clauses.length + 2)) :=
  (finalCNF_total_size addresses complete F vertices darts).trans
    (Nat.mul_le_mul_left _ (output_size_clause_bound addresses complete F))

end FinalCNF

end UniqueGamesTheorem.Foundations.PCP.PCPIteration

end

end

end OAI
