import Mathlib
import OAI.Computability.MinUncut.PCP.Gap

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceTupleBound

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

end MinUncutGames.Foundations.Hastad.SourceTupleBound

end
section
namespace MinUncutGames.Foundations.Hastad.SourceGeneratorTraversal

open Turing Complexity SourceContexts SourceOccurrences SourceRuntimeModel
open SourceGeneratorModel SourceGeneratorProgram SourceOdometerSchedule

noncomputable section

variable {u D : Nat}

local instance tupleBoundExtraDecidableEq (u D : Nat) :
    DecidableEq (SourceGeneratorModel.Extra u D) := Classical.decEq _

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

theorem resetDigits_ready (F : Target.Formula) :
    setDigits F.clauses.length (fun _ : Fin u => 0)
      (SourceStartup.readyTapes (u := u) (D := D) F) = SourceStartup.readyTapes F := by
  funext k
  cases k <;> simp [setDigits]

theorem allBits_eq_records (F : Target.Formula) (hne : F.clauses ≠ []) :
    allBits (SourceQueryOrder.tupleBits F u D) =
      (sourceList F u D).flatMap (fun e =>
        encodeWords (MinUncutGames.Reduction.SourceEncoding.equationWords e)) := by
  rw [sourceList_nonempty F u D hne]
  unfold allBits SourceQueryOrder.tupleBits SourceQueryOrder.slotBits
    SourceQueryOrder.occurrenceBits
  simp only [rawSourceList, occurrenceList,
    sourceIndexEncoding, Encoding.enumerate_prod, List.flatMap_map, List.flatMap_assoc,
    clauseEncoding, Encoding.enumerate_fin_function]

theorem accumulated_eq_input (F : Target.Formula) (hD : 0 < D) (hne : F.clauses ≠ []) :
    (allBits (SourceQueryOrder.tupleBits F u D)).reverse ++
        SourceStartup.readyTapes F (accumulatorTape u D) =
      (MinUncutGames.Reduction.SourceEncoding.inputBits (sourceInput F u D hD)).reverse := by
  rw [allBits_eq_records F hne, SourceStartup.ready_accumulator]
  have hi := SourceLoopOrder.inputBits_eq_header_records (sourceInput F u D hD)
  change MinUncutGames.Reduction.SourceEncoding.inputBits (sourceInput F u D hD) =
    encodeWords [nBits F u, (sourceList F u D).length] ++
      (sourceList F u D).flatMap (fun e =>
        encodeWords (MinUncutGames.Reduction.SourceEncoding.equationWords e)) at hi
  rw [hi, List.reverse_append]

def traversalOutput (F : Target.Formula) (hD : 0 < D) : SourceGeneratorModel.Tape u D → List Bool :=
  Function.update (SourceStartup.readyTapes F) (accumulatorTape u D)
    (MinUncutGames.Reduction.SourceEncoding.inputBits (sourceInput F u D hD)).reverse

@[simp] theorem traversalOutput_accumulator (F : Target.Formula) (hD : 0 < D) :
    traversalOutput F hD (accumulatorTape u D) =
      (MinUncutGames.Reduction.SourceEncoding.inputBits (sourceInput F u D hD)).reverse := by
  simp [traversalOutput]

theorem traversalOutput_frame (F : Target.Formula) (hD : 0 < D)
    (k : SourceGeneratorModel.Tape u D) (hk : k ≠ accumulatorTape u D) :
    traversalOutput F hD k = SourceStartup.readyTapes F k := by
  simp [traversalOutput, hk]

def resetLabel (u D : Nat) (i : Nat) : SourceGeneratorProgram.Label u D :=
  if h : i < u then .reset ⟨i, h⟩ else .finishEnter

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

end MinUncutGames.Foundations.Hastad.SourceGeneratorTraversal

end

end OAI
