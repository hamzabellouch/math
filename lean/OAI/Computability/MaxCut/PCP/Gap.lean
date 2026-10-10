import Mathlib
import OAI.Computability.MaxCut.PCP.TupleBody
import OAI.Computability.MaxCut.Games.Parameters

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceGap

open Target SourceContexts SourceOccurrences SourceGame
open MaxCutGames.Integration.SourceParameters
open MaxCutGames.Reduction

/-- A clause gap includes nonemptiness: a cross-multiplied inequality alone
would hold vacuously for a formula with no clauses. -/
def ClauseGap (F : Formula) (η : ℚ) : Prop :=
  F.clauses ≠ [] ∧ ∀ assignment : Fin F.«variables» → Bool,
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
    ∃ bits : Fin (source η ξ hη hη1 hξ D hD F).«variables» → Bool,
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
    (bits : Fin (source η ξ hη hη1 hξ D hD F).«variables» → Bool) :
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

end MaxCutGames.Foundations.Hastad.SourceGap

/-!
An executable finite-noise denominator for a positive rational target error.
Using the stored rational denominator avoids rounding, searches, and choice.
-/

namespace MaxCutGames.Foundations.Hastad.SourceNoiseParameter

/-- A positive rational has numerator at least one, so its reciprocal
denominator is no larger than the rational itself. Adding two also ensures
the noise parameter is at most one half for every input. -/
def noiseDenominator (ξ : ℚ) : ℕ := ξ.den + 2

theorem noiseDenominator_ge_two (ξ : ℚ) : 2 ≤ noiseDenominator ξ := by
  unfold noiseDenominator
  omega

theorem noiseDenominator_pos (ξ : ℚ) : 0 < noiseDenominator ξ :=
  lt_of_lt_of_le (by decide) (noiseDenominator_ge_two ξ)

theorem noiseDenominator_inv_pos (ξ : ℚ) :
    0 < (noiseDenominator ξ : ℚ)⁻¹ := by
  apply inv_pos.mpr
  exact_mod_cast noiseDenominator_pos ξ

theorem noiseDenominator_inv_le_half (ξ : ℚ) :
    (noiseDenominator ξ : ℚ)⁻¹ ≤ (1 / 2 : ℚ) := by
  rw [inv_eq_one_div]
  apply one_div_le_one_div_of_le (by norm_num)
  exact_mod_cast noiseDenominator_ge_two ξ

/-- The actual computed reciprocal noise is below every positive target. -/
theorem noiseDenominator_inv_le {ξ : ℚ} (hξ : 0 < ξ) :
    (noiseDenominator ξ : ℚ)⁻¹ ≤ ξ := by
  have hn : (1 : ℤ) ≤ ξ.num := by
    have h := Rat.num_pos.mpr hξ
    omega
  have hnq : (1 : ℚ) ≤ (ξ.num : ℚ) := by exact_mod_cast hn
  have hd : (0 : ℚ) < (ξ.den : ℚ) := by exact_mod_cast ξ.den_pos
  calc
    (noiseDenominator ξ : ℚ)⁻¹ = 1 / (noiseDenominator ξ : ℚ) := inv_eq_one_div _
    _ ≤ 1 / (ξ.den : ℚ) := by
      apply one_div_le_one_div_of_le hd
      exact_mod_cast (show ξ.den ≤ noiseDenominator ξ by
        unfold noiseDenominator
        omega)
    _ ≤ (ξ.num : ℚ) / (ξ.den : ℚ) := div_le_div_of_nonneg_right hnq hd.le
    _ = ξ := ξ.num_div_den

end MaxCutGames.Foundations.Hastad.SourceNoiseParameter

namespace MaxCutGames.Foundations.Hastad.SourceGap

open Target SourceNoiseParameter MaxCutGames.Reduction

def forError (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ) :
    Formula → SourceEncoding.Input :=
  source η ξ hη hη1 hξ (noiseDenominator ξ) (noiseDenominator_pos ξ)

theorem forError_complete (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (F : Formula) (hF : F.Satisfiable) :
    ∃ bits : Fin (forError η ξ hη hη1 hξ F).«variables» → Bool,
      1 - ξ ≤ ((forError η ξ hη hη1 hξ F).equations.countP
        (fun e => CloneGap.satisfied e bits) : ℚ) /
          (forError η ξ hη hη1 hξ F).equations.length :=
  source_complete η ξ hη hη1 hξ (noiseDenominator ξ) (noiseDenominator_pos ξ)
    (noiseDenominator_inv_le hξ) F hF

theorem forError_sound (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (F : Formula) (hgap : ClauseGap F η)
    (bits : Fin (forError η ξ hη hη1 hξ F).«variables» → Bool) :
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

end MaxCutGames.Foundations.Hastad.SourceGap

namespace MaxCutGames.Foundations.Hastad.SourceGeneratorContract

open Target Complexity

abbrev NonemptyFormula := { F : Formula // F.clauses ≠ [] }

def inputEncoding (F : NonemptyFormula) : List Bool := formulaBits F.val

def sourceMap (u D : Nat) (hD : 0 < D) (F : NonemptyFormula) :
    MaxCutGames.Reduction.SourceEncoding.Input :=
  SourceOccurrences.sourceInput F.val u D hD

def errorMap (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (F : NonemptyFormula) : MaxCutGames.Reduction.SourceEncoding.Input :=
  SourceGap.forError η ξ hη hη1 hξ F.val

theorem inputEncoding_mk (F : Formula) (hne : F.clauses ≠ []) :
    inputEncoding ⟨F, hne⟩ = formulaBits F := rfl

end MaxCutGames.Foundations.Hastad.SourceGeneratorContract

namespace MaxCutGames.Foundations.Hastad.SourceGeneratorProgram

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

end MaxCutGames.Foundations.Hastad.SourceGeneratorProgram

namespace MaxCutGames.Foundations.Hastad.SourceGenerator
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
end MaxCutGames.Foundations.Hastad.SourceGenerator

/-! Uniform polynomial bounds for the actual tuple-body phase budgets.
The budget being bounded is the one used by the checked machine traces. -/

namespace MaxCutGames.Foundations.Hastad.SourceTupleBound

open Complexity SourceContexts SourceOccurrences SourceTupleBody
open Complexity.MachineComposition

variable {u D : Nat}

theorem clauseRank_le_power (F : Target.Formula) (c : ClauseContext F u) :
    ((clauseEncoding F u).code c).val ≤ (formulaBits F).length ^ u := by
  have hr := ((clauseEncoding F u).code c).isLt
  change _ < F.clauses.length ^ u at hr
  exact hr.le.trans (Nat.pow_le_pow_left (SourceBounds.formulaBits_length_ge_clauses F) u)

theorem variableRank_le_power (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) :
    variableRank F c index ≤ (formulaBits F).length ^ u := by
  have hr := ((variableEncoding F u).code (sampledVariables F c (selected index))).isLt
  change variableRank F c index < F.«variables» ^ u at hr
  exact hr.le.trans (Nat.pow_le_pow_left (SourceBounds.formulaBits_length_ge_variables F) u)

theorem leftValue_le_numberBound (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) :
    leftValue F c index ≤ SourceBounds.bitCoefficient u * (formulaBits F).length ^ u :=
  (SourceAddressDescriptors.baseValue_lt F u c (sampledVariables F c (selected index)) 0).le.trans
    (SourceBounds.nBits_le_input F u)

theorem rightValue_le_numberBound (F : Target.Formula) (c : ClauseContext F u) :
    rightValue F c ≤ SourceBounds.bitCoefficient u * (formulaBits F).length ^ u :=
  (SourceAddressDescriptors.baseValue_lt F u c (sampledVariables F c (fun _ => .first)) 1).le.trans
    (SourceBounds.nBits_le_input F u)

theorem leftBlock_le_numberBound (F : Target.Formula) :
    2 ^ (2 ^ u) * F.«variables» ^ u ≤
      SourceBounds.bitCoefficient u * (formulaBits F).length ^ u := by
  apply Nat.le_trans (m := nBits F u)
  · rw [Nat.mul_comm (2 ^ (2 ^ u)) (F.«variables» ^ u), nBits_eq]
    omega
  · exact SourceBounds.nBits_le_input F u

noncomputable def rankPolynomial (u : Nat) : Polynomial Nat := Polynomial.X ^ u
noncomputable def numberPolynomial (u : Nat) : Polynomial Nat :=
  Polynomial.C (SourceBounds.bitCoefficient u) * Polynomial.X ^ u

@[simp] theorem rankPolynomial_eval (u L : Nat) : (rankPolynomial u).eval L = L ^ u := by
  simp [rankPolynomial]
@[simp] theorem numberPolynomial_eval (u L : Nat) :
    (numberPolynomial u).eval L = SourceBounds.bitCoefficient u * L ^ u := by
  simp [numberPolynomial]

noncomputable def slotPolynomial (u D : Nat) : Polynomial Nat :=
  Polynomial.C 1 + MachineHorner.timePolynomial u +
    (SourceBasePhase.timePolynomial (2 ^ (2 ^ u))).comp (rankPolynomial u + Polynomial.C 2) +
    (Polynomial.C (QueryCount u D) * (Polynomial.C 9 * numberPolynomial u + Polynomial.C 21) +
      Polynomial.C 1) +
    (rankPolynomial u + Polynomial.C 2) + (numberPolynomial u + Polynomial.C 2)

theorem slotPolynomial_eval (u D L : Nat) :
    (slotPolynomial u D).eval L =
      1 + (MachineHorner.timePolynomial u).eval L +
        (SourceBasePhase.timePolynomial (2 ^ (2 ^ u))).eval (L ^ u + 2) +
        (QueryCount u D * (9 * (SourceBounds.bitCoefficient u * L ^ u) + 21) + 1) +
        (L ^ u + 2) + (SourceBounds.bitCoefficient u * L ^ u + 2) := by
  simp only [slotPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, rankPolynomial_eval, numberPolynomial_eval]

theorem slotBudget_le (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) :
    slotBudget (D := D) F c index ≤ (slotPolynomial u D).eval (formulaBits F).length := by
  have hr := variableRank_le_power F c index
  have hl := leftValue_le_numberBound F c index
  have hb := SourceBounds.nBits_le_input F u
  have hn := natPolynomial_eval_mono (MachineHorner.timePolynomial u)
    (SourceBounds.formulaBits_length_ge_variables F)
  have ho : SourceBasePhase.operandLength (variableRank F c index) 0 ≤
      (formulaBits F).length ^ u + 2 := by
    simp only [SourceBasePhase.operandLength, encodeWord_length]
    omega
  have ha := natPolynomial_eval_mono (SourceBasePhase.timePolynomial (2 ^ (2 ^ u))) ho
  have hq := Nat.mul_le_mul_left (QueryCount u D)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 9 hb) 21)
  rw [slotPolynomial_eval]
  unfold slotBudget
  omega

theorem prefixBudget_le (F : Target.Formula) (c : ClauseContext F u) (r : Nat) :
    prefixBudget (D := D) F c r ≤ r * (slotPolynomial u D).eval (formulaBits F).length := by
  induction r with
  | zero => simp [prefixBudget]
  | succ r ih =>
    rw [prefixBudget]
    split
    next h =>
      have hs := slotBudget_le (D := D) F c ⟨r, h⟩
      simpa only [Nat.succ_mul] using Nat.add_le_add ih hs
    next _ =>
      simpa only [Nat.add_zero] using ih.trans
        (Nat.mul_le_mul_right ((slotPolynomial u D).eval (formulaBits F).length) (Nat.le_succ r))

noncomputable def preparePolynomial (u : Nat) : Polynomial Nat :=
  Polynomial.C u * (Polynomial.C 10 * Polynomial.X + Polynomial.C 20) + Polynomial.C 1 +
    (Polynomial.C (SourceSignaturePrepare.Width u * SourceSignaturePrepare.Width u) *
      (Polynomial.C 5 * Polynomial.X + Polynomial.C 6) + Polynomial.C 2)

theorem preparePolynomial_eval (u L : Nat) :
    (preparePolynomial u).eval L =
      (u * (10 * L + 20) + 1) +
        (SourceSignaturePrepare.Width u * SourceSignaturePrepare.Width u * (5 * L + 6) + 2) := by
  simp only [preparePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

noncomputable def setupPolynomial (u : Nat) : Polynomial Nat :=
  preparePolynomial u + Polynomial.C 1 + MachineHorner.timePolynomial u +
    (SourceBasePhase.timePolynomial (2 ^ (8 ^ u))).comp
      (rankPolynomial u + numberPolynomial u + Polynomial.C 2) +
    (rankPolynomial u + Polynomial.C 2)

theorem setupPolynomial_eval (u L : Nat) :
    (setupPolynomial u).eval L =
      (preparePolynomial u).eval L + 1 + (MachineHorner.timePolynomial u).eval L +
        (SourceBasePhase.timePolynomial (2 ^ (8 ^ u))).eval
          (L ^ u + SourceBounds.bitCoefficient u * L ^ u + 2) + (L ^ u + 2) := by
  simp only [setupPolynomial, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_comp, rankPolynomial_eval, numberPolynomial_eval]

noncomputable def finishPolynomial (u : Nat) : Polynomial Nat :=
  Polynomial.C 1 + (numberPolynomial u + Polynomial.C 2) + Polynomial.C 2 +
    (Polynomial.C (6 * u) * (Polynomial.X + Polynomial.C 1) + Polynomial.C 1) + Polynomial.C 1

theorem finishPolynomial_eval (u L : Nat) :
    (finishPolynomial u).eval L =
      1 + (SourceBounds.bitCoefficient u * L ^ u + 2) + 2 + (6 * u * (L + 1) + 1) + 1 := by
  simp only [finishPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, numberPolynomial_eval]

noncomputable def bodyPolynomial (u D : Nat) : Polynomial Nat :=
  setupPolynomial u + Polynomial.C (SlotCount u) * slotPolynomial u D + finishPolynomial u

theorem setupBudget_le (F : Target.Formula) (c : ClauseContext F u) :
    setupBudget F c ≤ (setupPolynomial u).eval (formulaBits F).length := by
  have hr := clauseRank_le_power F c
  have hl := leftBlock_le_numberBound (u := u) F
  have hm := natPolynomial_eval_mono (MachineHorner.timePolynomial u)
    (SourceBounds.formulaBits_length_ge_clauses F)
  have ho : SourceBasePhase.operandLength (((clauseEncoding F u).code c).val)
      (2 ^ (2 ^ u) * F.«variables» ^ u) ≤
      (formulaBits F).length ^ u +
        SourceBounds.bitCoefficient u * (formulaBits F).length ^ u + 2 := by
    simp only [SourceBasePhase.operandLength, encodeWord_length]
    omega
  have ha := natPolynomial_eval_mono (SourceBasePhase.timePolynomial (2 ^ (8 ^ u))) ho
  rw [setupPolynomial_eval, preparePolynomial_eval]
  unfold setupBudget
  omega

theorem finishBudget_le (F : Target.Formula) (c : ClauseContext F u) :
    finishBudget F c ≤ (finishPolynomial u).eval (formulaBits F).length := by
  have hr := rightValue_le_numberBound F c
  rw [finishPolynomial_eval]
  unfold finishBudget
  omega

/-- One fixed polynomial bounds the actual tuple-body budget for every tuple. -/
theorem bodyBudget_le (F : Target.Formula) (c : ClauseContext F u) :
    bodyBudget (D := D) F c ≤ (bodyPolynomial u D).eval (formulaBits F).length := by
  have hs := setupBudget_le F c
  have hp := prefixBudget_le (D := D) F c (SlotCount u)
  have hf := finishBudget_le F c
  simp only [bodyPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  unfold bodyBudget
  omega

theorem fixed_parameters_body_bound (u D : Nat) :
    ∃ p : Polynomial Nat, ∀ (F : Target.Formula) (c : ClauseContext F u),
      bodyBudget (D := D) F c ≤ p.eval (formulaBits F).length :=
  ⟨bodyPolynomial u D, fun F c => bodyBudget_le F c⟩

/-- The actual body execution with the same fixed polynomial for every tuple. -/
theorem bodyInPolynomialTime {Extra : Type} [DecidableEq Extra]
    (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : SourceRuntimeModel.Arena u Extra → List Bool) (h : Ready F c base) :
    Nonempty (StateTransition.EvalsToInTime (Turing.TM2.step (program initialQuery exit))
      ⟨some main, SourceRuntimeModel.canonicalState initialQuery, base⟩
      (some ⟨exit, SourceRuntimeModel.canonicalState initialQuery,
        SourceTestAppend.resultTapes SourceRuntimeModel.queryLayout base
          (SourceQueryOrder.tupleBits F u D c)⟩)
      ((bodyPolynomial u D).eval (formulaBits F).length)) := by
  obtain ⟨run⟩ := bodyInTime F c initialQuery exit base h
  exact ⟨{
    toEvalsTo := run.toEvalsTo
    steps_le_m := run.steps_le_m.trans (bodyBudget_le F c)
  }⟩

end MaxCutGames.Foundations.Hastad.SourceTupleBound

namespace MaxCutGames.Foundations.Hastad.SourceGeneratorTraversal

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
  · change (SourceStartup.readyTapes (u := u) (D := D) F) variableHeader = encodeWord F.«variables»
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
        encodeWords (MaxCutGames.Reduction.SourceEncoding.equationWords e)) := by
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
      (MaxCutGames.Reduction.SourceEncoding.inputBits (sourceInput F u D hD)).reverse := by
  rw [allBits_eq_records F hne, SourceStartup.ready_accumulator]
  have hi := SourceLoopOrder.inputBits_eq_header_records (sourceInput F u D hD)
  change MaxCutGames.Reduction.SourceEncoding.inputBits (sourceInput F u D hD) =
    encodeWords [nBits F u, (sourceList F u D).length] ++
      (sourceList F u D).flatMap (fun e =>
        encodeWords (MaxCutGames.Reduction.SourceEncoding.equationWords e)) at hi
  rw [hi, List.reverse_append]

def traversalOutput (F : Target.Formula) (hD : 0 < D) : SourceGeneratorModel.Tape u D → List Bool :=
  Function.update (SourceStartup.readyTapes F) (accumulatorTape u D)
    (MaxCutGames.Reduction.SourceEncoding.inputBits (sourceInput F u D hD)).reverse

@[simp] theorem traversalOutput_accumulator (F : Target.Formula) (hD : 0 < D) :
    traversalOutput F hD (accumulatorTape u D) =
      (MaxCutGames.Reduction.SourceEncoding.inputBits (sourceInput F u D hD)).reverse := by
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

end MaxCutGames.Foundations.Hastad.SourceGeneratorTraversal

end OAI
