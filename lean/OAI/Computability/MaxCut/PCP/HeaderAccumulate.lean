import Mathlib
import OAI.Computability.MaxCut.PCP.HeaderCounts

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceHeaderAccumulate

open Turing MaxCutGames.Foundations.Complexity
open MachineComposition
open MaxCutGames.Reduction.MachineTransfer

structure Layout (K : Type) where
  bits : K
  count : K
  accumulator : K
  bits_count : bits ≠ count
  bits_accumulator : bits ≠ accumulator
  count_accumulator : count ≠ accumulator

variable {K Λ σ : Type} [DecidableEq K]

def statement (layout : Layout K) (labels : Bool → Λ) (exit : Option Λ) :
    Bool → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | false => loopAt layout.bits layout.accumulator id false (labels false) (some (labels true))
  | true => loopAt layout.count layout.accumulator id false (labels true) exit

def resultTapes (layout : Layout K) (base : K → List Bool) (nBits count : Nat) : K → List Bool :=
  Function.update (Function.update (Function.update base layout.bits []) layout.count [])
    layout.accumulator ((encodeWords [nBits, count]).reverse ++ base layout.accumulator)

@[simp] theorem result_bits (layout : Layout K) (base : K → List Bool) (nBits count : Nat) :
    resultTapes layout base nBits count layout.bits = [] := by
  simp [resultTapes, layout.bits_count, layout.bits_accumulator]

@[simp] theorem result_count (layout : Layout K) (base : K → List Bool) (nBits count : Nat) :
    resultTapes layout base nBits count layout.count = [] := by
  simp [resultTapes, layout.count_accumulator]

@[simp] theorem result_accumulator (layout : Layout K) (base : K → List Bool) (nBits count : Nat) :
    resultTapes layout base nBits count layout.accumulator =
      (encodeWords [nBits, count]).reverse ++ base layout.accumulator := by
  simp [resultTapes]

theorem result_frame (layout : Layout K) (base : K → List Bool) (nBits count : Nat)
    (k : K) (hb : k ≠ layout.bits) (hc : k ≠ layout.count) (ha : k ≠ layout.accumulator) :
    resultTapes layout base nBits count k = base k := by
  simp [resultTapes, hb, hc, ha]

theorem trace (layout : Layout K) (labels : Bool → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = statement layout labels exit l)
    (base : K → List Bool) (nBits count : Nat)
    (hbits : base layout.bits = encodeWord nBits)
    (hcount : base layout.count = encodeWord count) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[nBits + count + 4]
      (some ⟨some (labels false), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), resultTapes layout base nBits count⟩ := by
  let middle := tapesAt layout.bits layout.accumulator base []
    ((encodeWord nBits).reverse ++ base layout.accumulator)
  have firstRun := transferAt_fromTapes layout.bits layout.accumulator layout.bits_accumulator
    id false (labels false) (some (labels true)) program (by simpa only [statement] using atLabels false) base ambient register
  change (advance (TM2.step program))^[(base layout.bits).length + 1]
    (some ⟨some (labels false), (ambient, register), base⟩) = _ at firstRun
  simp only [hbits, List.map_id, encodeWord_length] at firstRun
  have hc : middle layout.count = encodeWord count := by
    dsimp only [middle]
    rw [tapesAt_other _ _ _ layout.bits_count.symm layout.count_accumulator]
    exact hcount
  have ha : middle layout.accumulator =
      (encodeWord nBits).reverse ++ base layout.accumulator := by
    exact tapesAt_dst _ _ _ _ _
  have secondRun := transferAt_fromTapes layout.count layout.accumulator layout.count_accumulator
    id false (labels true) exit program (by simpa only [statement] using atLabels true) middle ambient none
  change (advance (TM2.step program))^[(middle layout.count).length + 1]
    (some ⟨some (labels true), (ambient, none), middle⟩) = _ at secondRun
  simp only [hc, ha, List.map_id, encodeWord_length] at secondRun
  have he : tapesAt layout.count layout.accumulator middle []
      ((encodeWord count).reverse ++ ((encodeWord nBits).reverse ++ base layout.accumulator)) =
      resultTapes layout base nBits count := by
    funext k
    by_cases hk : k = layout.accumulator
    · subst k
      simp [resultTapes, tapesAt, encodeWords, List.reverse_append, List.append_assoc]
    · by_cases hc : k = layout.count
      · subst k; simp [tapesAt, resultTapes, layout.count_accumulator]
      · by_cases hb : k = layout.bits
        · subst k
          simp [middle, tapesAt, resultTapes, layout.bits_count, layout.bits_accumulator]
        · simp [middle, tapesAt, resultTapes, hk, hc, hb]
  rw [he] at secondRun
  rw [show nBits + count + 4 = (count + 1 + 1) + (nBits + 1 + 1) by omega,
    Function.iterate_add_apply, firstRun]
  exact secondRun

def inTime (layout : Layout K) (labels : Bool → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = statement layout labels exit l)
    (base : K → List Bool) (nBits count : Nat)
    (hbits : base layout.bits = encodeWord nBits)
    (hcount : base layout.count = encodeWord count) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels false), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), resultTapes layout base nBits count⟩)
      (nBits + count + 4) where
  steps := nBits + count + 4
  evals_in_steps := trace layout labels exit program atLabels base nBits count hbits hcount ambient register
  steps_le_m := Nat.le_refl _

@[simp] theorem inTime_steps (layout : Layout K) (labels : Bool → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = statement layout labels exit l)
    (base : K → List Bool) (nBits count : Nat)
    (hbits : base layout.bits = encodeWord nBits)
    (hcount : base layout.count = encodeWord count) (ambient : σ) (register : Option Bool) :
    (inTime layout labels exit program atLabels base nBits count hbits hcount ambient register).steps =
      nBits + count + 4 := rfl

def machine [Fintype K] [Fintype σ] (layout : Layout K) (ambient : σ) : FinTM2 where
  K := K
  k₀ := layout.bits
  k₁ := layout.accumulator
  Γ _ := Bool
  Λ := Bool
  main := false
  σ := σ × Option Bool
  initialState := (ambient, none)
  m := statement layout id none

theorem source_inputBits_header (input : MaxCutGames.Reduction.SourceEncoding.Input) :
    MaxCutGames.Reduction.SourceEncoding.inputBits input =
      encodeWords [input.«variables», input.equations.length] ++
        encodeWords (input.equations.flatMap MaxCutGames.Reduction.SourceEncoding.equationWords) := by
  simp only [MaxCutGames.Reduction.SourceEncoding.inputBits,
    MaxCutGames.Reduction.SourceEncoding.inputWords, encodeWords_append]

end MaxCutGames.Foundations.Hastad.SourceHeaderAccumulate

namespace MaxCutGames.Foundations.Hastad.SourceStartup

open Turing Complexity SourceRuntimeModel SourceGeneratorModel
open MachineComposition

noncomputable section

variable {u D : Nat}

abbrev Tape (u D : Nat) := SourceGeneratorModel.Tape u D
abbrev State (u D : Nat) := SourceRuntimeModel.State u D
abbrev ArithmeticLabel (u D : Nat) := SourceHeaderCounts.Label u D ⊕ Bool
abbrev Label (u D : Nat) := SourceLoopInit.Label u ⊕ ArithmeticLabel u D

local instance (u D : Nat) : DecidableEq (SourceGeneratorModel.Extra u D) := Classical.decEq _

def headerLayout (u D : Nat) : SourceHeaderAccumulate.Layout (Tape u D) where
  bits := workTape .bitCount
  count := workTape .occurrenceCount
  accumulator := workTape .accumulator
  bits_count := by simp [workTape]
  bits_accumulator := by simp [workTape]
  count_accumulator := by simp [workTape]

def arithmeticEntry (u D : Nat) : ArithmeticLabel u D :=
  .inl (SourceHeaderCounts.evalStart .left)

def arithmeticProgram : ArithmeticLabel u D →
    TM2.Stmt (fun _ : Tape u D => Bool) (ArithmeticLabel u D) ArithmeticState
  | .inl l => SourceHeaderCounts.statement (headerSlots u D) Sum.inl (some (.inr false)) l
  | .inr l => SourceHeaderAccumulate.statement (headerLayout u D) Sum.inr none l

def program : Label u D → TM2.Stmt (fun _ : Tape u D => Bool) (Label u D) (State u D)
  | .inl l => MachineStateFrame.statement Sum.inl (some (.inr (arithmeticEntry u D)))
      (SourceLoopInit.program l)
  | .inr l => MachineControl.statement id (arithmeticStateEquiv u D)
      (MachineStateFrame.statement Sum.inr none (arithmeticProgram l))

def initialTapes (F : Target.Formula) : Tape u D → List Bool :=
  Function.update (fun _ => []) .formula (formulaBits F)

def initializedTapes (F : Target.Formula) : Tape u D → List Bool :=
  SourceLoopInit.outputTapes F (initialTapes F)

def countedTapes (F : Target.Formula) : Tape u D → List Bool :=
  SourceHeaderCounts.resultTapes (headerSlots u D) (initializedTapes F)
    F.«variables» F.clauses.length

def outputTapes (F : Target.Formula) : Tape u D → List Bool :=
  SourceHeaderAccumulate.resultTapes (headerLayout u D) (countedTapes F)
    (SourceHeaderCounts.bitValue u F.«variables» F.clauses.length)
    (SourceHeaderCounts.occurrenceValue u D F.clauses.length)

def readyTapes (F : Target.Formula) : Tape u D → List Bool
  | .extra (.inr .leftBlock) => encodeWord (SourceHeaderCounts.leftValue u F.«variables»)
  | .extra (.inr .dummy) => encodeWord (SourceHeaderCounts.dummyValue u F.«variables» F.clauses.length)
  | .extra (.inr .accumulator) =>
      (encodeWords [SourceOccurrences.nBits F u, (SourceOccurrences.sourceList F u D).length]).reverse
  | p => initializedTapes F p

@[simp] theorem initialized_formula (F : Target.Formula) :
    initializedTapes (u := u) (D := D) F .formula = formulaBits F := by
  simp [initializedTapes, initialTapes]

@[simp] theorem initialized_current (F : Target.Formula) (j : Fin u) :
    initializedTapes (D := D) F (.current j) = encodeWord 0 := by
  simp [initializedTapes]

@[simp] theorem initialized_remaining (F : Target.Formula) (j : Fin u) :
    initializedTapes (D := D) F (.remaining j) = encodeWord (F.clauses.length - 1) := by
  simp [initializedTapes]

@[simp] theorem initialized_variableHeader (F : Target.Formula) :
    initializedTapes (u := u) (D := D) F variableHeader = encodeWord F.«variables» := by
  change SourceLoopInit.outputTapes F (initialTapes F) SourceLoopInit.variableHeader = _
  rw [SourceLoopInit.output_variableHeader]
  simp [initialTapes, SourceLoopInit.variableHeader]

@[simp] theorem initialized_clauseHeader (F : Target.Formula) :
    initializedTapes (u := u) (D := D) F clauseHeader = encodeWord F.clauses.length := by
  change SourceLoopInit.outputTapes F (initialTapes F) SourceLoopInit.clauseHeader = _
  rw [SourceLoopInit.output_clauseHeader]
  simp [initialTapes, SourceLoopInit.clauseHeader]

@[simp] theorem initialized_work (F : Target.Formula) (role : BodyWork (SourceGeneratorModel.Extra u D)) :
    initializedTapes F (workTape role) = [] := by
  rw [initializedTapes, SourceLoopInit.output_frame F (initialTapes F) (workTape role)
    (by simp [workTape]) (by simp [workTape, SourceLoopInit.variableHeader])
    (by simp [workTape, SourceLoopInit.clauseHeader]) (by simp [workTape]) (by simp [workTape])]
  simp [initialTapes, workTape]

@[simp] theorem initialized_work_raw (F : Target.Formula)
    (role : BodyWork (SourceGeneratorModel.Extra u D)) :
    initializedTapes F (.extra (.inr role)) = [] := initialized_work F role

@[simp] theorem initialized_field (F : Target.Formula) (j : Fin u) (s : Fin 6) :
    initializedTapes (D := D) F (.field j s) = [] := by
  rw [initializedTapes, SourceLoopInit.output_frame F (initialTapes F) (.field j s)
    (by simp) (by simp [SourceLoopInit.variableHeader]) (by simp [SourceLoopInit.clauseHeader])
    (by simp) (by simp)]
  simp [initialTapes]

theorem initialized_clean (F : Target.Formula) :
    SourceHeaderCounts.Clean (headerSlots u D) (initializedTapes F) := by
  constructor
  · exact initialized_work F .leftBlock
  · exact initialized_work F .rank
  · exact initialized_work F .dummy
  · exact initialized_work F .bitCount
  · exact initialized_work F .occurrenceCount
  · exact initialized_work F .accA
  · exact initialized_work F .accB
  · exact initialized_work F .counter
  · exact initialized_work F .arithScratch
  · intro i; exact initialized_work F (.extra (.inl i))

def initialArithmeticMetadata (u D : Nat) (hD : 0 < D) : ArithmeticMetadata u D :=
  ((arithmeticStateEquiv u D).symm (SourceGeneratorModel.initialState u D hD)).2

theorem initial_arithmetic (hD : 0 < D) :
    arithmeticStateEquiv u D ((((), ()), none), initialArithmeticMetadata u D hD) =
      SourceGeneratorModel.initialState u D hD := rfl

theorem initial_loader (hD : 0 < D) :
    (((), none), (SourceGeneratorModel.initialState u D hD).2) =
      SourceGeneratorModel.initialState u D hD := rfl

def initializeInTime (F : Target.Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl .inputCopyOut), SourceGeneratorModel.initialState u D hD, initialTapes F⟩
      (some ⟨some (.inr (arithmeticEntry u D)), SourceGeneratorModel.initialState u D hD,
        initializedTapes F⟩)
      ((2 * u + 3) * (formulaBits F).length + 6 * u + 7) := by
  have run := SourceLoopInit.initializeInTime F hm (initialTapes (u := u) (D := D) F)
    (by simp [initialTapes]) (by simp [initialTapes]) (by simp [initialTapes])
    (by simp [initialTapes]) (by simp [initialTapes, SourceLoopInit.clauseHeader])
    (by intro j; simp [initialTapes]) (by intro j; simp [initialTapes])
  have lifted := MachineStateFrame.execution Sum.inl (some (.inr (arithmeticEntry u D)))
    (SourceGeneratorModel.initialState u D hD).2 SourceLoopInit.program program (fun _ => rfl) run
  simpa only [MachineStateFrame.configuration, MachineSubroutine.configuration,
    MachineStateFrame.frameConfiguration, MachineSubroutine.label, initial_loader,
    initializedTapes] using lifted

def arithmeticInTime (F : Target.Formula) :
    StateTransition.EvalsToInTime (TM2.step arithmeticProgram)
      ⟨some (arithmeticEntry u D), (((), ()), none), initializedTapes F⟩
      (some ⟨none, (((), ()), none), outputTapes F⟩)
      (SourceHeaderCounts.steps u D F.«variables» F.clauses.length +
        SourceHeaderCounts.bitValue u F.«variables» F.clauses.length +
        SourceHeaderCounts.occurrenceValue u D F.clauses.length + 4) := by
  have countRun := SourceHeaderCounts.inTime (headerSlots u D) Sum.inl (some (.inr false))
    arithmeticProgram (fun _ => rfl) (initializedTapes F) F.«variables» F.clauses.length
    (initialized_variableHeader F) (initialized_clauseHeader F) (initialized_clean F) () none
  have appendRun := SourceHeaderAccumulate.inTime (headerLayout u D) Sum.inr none
    arithmeticProgram (fun _ => rfl) (countedTapes F)
    (SourceHeaderCounts.bitValue u F.«variables» F.clauses.length)
    (SourceHeaderCounts.occurrenceValue u D F.clauses.length)
    (SourceHeaderCounts.result_bits (headerSlots u D) (initializedTapes F) _ _)
    (SourceHeaderCounts.result_occurrences (headerSlots u D) (initializedTapes F) _ _) ((), ()) none
  have joined := StateTransition.EvalsToInTime.trans (TM2.step arithmeticProgram) _ _ _ _ _
    countRun appendRun
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  have ht := joined.steps_le_m
  omega

def arithmeticConfiguration (metadata : ArithmeticMetadata u D)
    (c : TM2.Cfg (fun _ : Tape u D => Bool) (ArithmeticLabel u D) ArithmeticState) :
    TM2.Cfg (fun _ : Tape u D => Bool) (Label u D) (State u D) :=
  MachineControl.configuration id (arithmeticStateEquiv u D)
    (MachineStateFrame.configuration Sum.inr none metadata c)

theorem arithmetic_step (metadata : ArithmeticMetadata u D)
    (a b : TM2.Cfg (fun _ : Tape u D => Bool) (ArithmeticLabel u D) ArithmeticState)
    (h : TM2.step arithmeticProgram a = some b) :
    TM2.step program (arithmeticConfiguration metadata a) =
      some (arithmeticConfiguration metadata b) := by
  rcases a with ⟨label, state, tapes⟩
  cases label with
  | none => cases h
  | some l =>
    change some (TM2.stepAux (arithmeticProgram l) state tapes) = some b at h
    cases Option.some.inj h
    change some (TM2.stepAux
      (MachineControl.statement id (arithmeticStateEquiv u D)
        (MachineStateFrame.statement Sum.inr none (arithmeticProgram l)))
      ((arithmeticStateEquiv u D) (state, metadata)) tapes) = _
    rw [MachineControl.stepAux_simulation, MachineStateFrame.stepAux_simulation]
    rfl

def arithmeticPlacedInTime (F : Target.Formula) (hD : 0 < D) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr (arithmeticEntry u D)), SourceGeneratorModel.initialState u D hD, initializedTapes F⟩
      (some ⟨none, SourceGeneratorModel.initialState u D hD, outputTapes F⟩)
      (SourceHeaderCounts.steps u D F.«variables» F.clauses.length +
        SourceHeaderCounts.bitValue u F.«variables» F.clauses.length +
        SourceHeaderCounts.occurrenceValue u D F.clauses.length + 4) := by
  have lifted := liftExecutionInTime (TM2.step arithmeticProgram) (TM2.step program)
    (arithmeticConfiguration (initialArithmeticMetadata u D hD))
    (arithmetic_step (initialArithmeticMetadata u D hD)) (arithmeticInTime F)
  simpa only [arithmeticConfiguration, MachineControl.configuration,
    MachineStateFrame.configuration, MachineStateFrame.frameConfiguration,
    MachineSubroutine.configuration, MachineSubroutine.label, Option.map_some, Option.map_none,
    id_eq, initial_arithmetic] using lifted

def phaseBound (F : Target.Formula) (u D : Nat) : Nat :=
  ((2 * u + 3) * (formulaBits F).length + 6 * u + 7) +
    (SourceHeaderCounts.steps u D F.«variables» F.clauses.length +
      SourceHeaderCounts.bitValue u F.«variables» F.clauses.length +
      SourceHeaderCounts.occurrenceValue u D F.clauses.length + 4)

def phasesInTime (F : Target.Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl .inputCopyOut), SourceGeneratorModel.initialState u D hD, initialTapes F⟩
      (some ⟨none, SourceGeneratorModel.initialState u D hD, outputTapes F⟩)
      (phaseBound F u D) := by
  have run := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (initializeInTime (u := u) F hm hD) (arithmeticPlacedInTime (u := u) F hD)
  simpa only [phaseBound, Nat.add_comm] using run

theorem output_eq_ready (F : Target.Formula) (hm : 0 < F.clauses.length) :
    outputTapes (u := u) (D := D) F = readyTapes F := by
  funext k
  cases k <;> try simp [outputTapes, SourceHeaderAccumulate.resultTapes, headerLayout,
    countedTapes, SourceHeaderCounts.resultTapes, SourceHeaderCounts.control,
    headerSlots, headerControl, workTape, readyTapes]
  rename_i e
  cases e with
  | inl h =>
    cases h <;> simp
  | inr role =>
    cases role <;> simp [SourceHeaderCounts.bitValue_eq_nBits,
      SourceHeaderCounts.occurrenceValue_eq_length F u D hm]
    change Function.update (_ : Tape u D → List Bool) (.extra (.inr .bitCount)) _
      (.extra (.inr .accumulator)) = []
    simp

@[simp] theorem ready_formula (F : Target.Formula) :
    readyTapes (u := u) (D := D) F .formula = formulaBits F := initialized_formula F

@[simp] theorem ready_current (F : Target.Formula) (j : Fin u) :
    readyTapes (D := D) F (.current j) = encodeWord 0 := initialized_current F j

@[simp] theorem ready_remaining (F : Target.Formula) (j : Fin u) :
    readyTapes (D := D) F (.remaining j) = encodeWord (F.clauses.length - 1) := initialized_remaining F j

@[simp] theorem ready_variableHeader (F : Target.Formula) :
    readyTapes (u := u) (D := D) F variableHeader = encodeWord F.«variables» := initialized_variableHeader F

@[simp] theorem ready_clauseHeader (F : Target.Formula) :
    readyTapes (u := u) (D := D) F clauseHeader = encodeWord F.clauses.length := initialized_clauseHeader F

@[simp] theorem ready_leftBlock (F : Target.Formula) :
    readyTapes (u := u) (D := D) F (workTape .leftBlock) =
      encodeWord (SourceHeaderCounts.leftValue u F.«variables») := rfl

@[simp] theorem ready_dummy (F : Target.Formula) :
    readyTapes (u := u) (D := D) F (workTape .dummy) =
      encodeWord (SourceHeaderCounts.dummyValue u F.«variables» F.clauses.length) := rfl

@[simp] theorem ready_accumulator (F : Target.Formula) :
    readyTapes (u := u) (D := D) F (accumulatorTape u D) =
      (encodeWords [SourceOccurrences.nBits F u, (SourceOccurrences.sourceList F u D).length]).reverse := rfl

@[simp] theorem ready_field (F : Target.Formula) (j : Fin u) (s : Fin 6) :
    readyTapes (D := D) F (.field j s) = [] := initialized_field F j s

theorem ready_work_blank (F : Target.Formula) (role : BodyWork (SourceGeneratorModel.Extra u D))
    (hl : role ≠ .leftBlock) (hd : role ≠ .dummy) (ha : role ≠ .accumulator) :
    readyTapes F (workTape role) = [] := by
  cases role <;> try contradiction
  all_goals exact initialized_work F _

@[simp] theorem ready_sharedWork (F : Target.Formula) :
    readyTapes (u := u) (D := D) F .work = [] := by
  simp [readyTapes, initializedTapes]

theorem ready_sharedFrame (F : Target.Formula) (k : Tape u D)
    (hk : k = .index ∨ k = .scratch ∨ k = .copyScratch) : readyTapes F k = [] := by
  rcases hk with rfl | rfl | rfl <;>
    simp only [readyTapes, initializedTapes]
  all_goals
    rw [SourceLoopInit.output_frame F (initialTapes F) _
      (by simp) (by simp [SourceLoopInit.variableHeader]) (by simp [SourceLoopInit.clauseHeader])
      (by simp) (by simp)]
    simp [initialTapes]

def startupInTime (F : Target.Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl .inputCopyOut), SourceGeneratorModel.initialState u D hD, initialTapes F⟩
      (some ⟨none, SourceGeneratorModel.initialState u D hD, readyTapes F⟩)
      (phaseBound F u D) := by
  have run := phasesInTime (u := u) F hm hD
  simpa only [output_eq_ready F hm] using run

def timePolynomial (u D : Nat) : Polynomial Nat :=
  SourceLoopInit.timePolynomial u + SourceHeaderCounts.timePolynomial u D +
    SourceHeaderCounts.polynomial u D .left + SourceHeaderCounts.polynomial u D .right +
    SourceHeaderCounts.polynomial u D .occurrences + Polynomial.C 5

theorem phaseBound_le_polynomial (F : Target.Formula) (u D : Nat) :
    phaseBound F u D ≤ (timePolynomial u D).eval (formulaBits F).length := by
  have hn := SourceBounds.formulaBits_length_ge_variables F
  have hm := SourceBounds.formulaBits_length_ge_clauses F
  have hc := SourceHeaderCounts.steps_le_timePolynomial u D F.«variables» F.clauses.length
    (formulaBits F).length hn hm
  have hl : SourceHeaderCounts.leftValue u F.«variables» ≤
      SourceHeaderCounts.leftValue u (formulaBits F).length :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn u)
  have hr : SourceHeaderCounts.rightValue u F.clauses.length ≤
      SourceHeaderCounts.rightValue u (formulaBits F).length :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm u)
  have ho : SourceHeaderCounts.occurrenceValue u D F.clauses.length ≤
      SourceHeaderCounts.occurrenceValue u D (formulaBits F).length :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm u)
  simp only [phaseBound, timePolynomial, Polynomial.eval_add, Polynomial.eval_C,
    SourceLoopInit.timePolynomial_eval, SourceHeaderCounts.polynomial_left_eval,
    SourceHeaderCounts.polynomial_right_eval, SourceHeaderCounts.polynomial_occurrences_eval,
    SourceHeaderCounts.bitValue, SourceHeaderCounts.dummyValue]
  omega

def startupInPolynomialTime (F : Target.Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl .inputCopyOut), SourceGeneratorModel.initialState u D hD, initialTapes F⟩
      (some ⟨none, SourceGeneratorModel.initialState u D hD, readyTapes F⟩)
      ((timePolynomial u D).eval (formulaBits F).length) := by
  have run := startupInTime (u := u) F hm hD
  refine { steps := run.steps, evals_in_steps := run.evals_in_steps, steps_le_m := ?_ }
  exact Nat.le_trans run.steps_le_m (phaseBound_le_polynomial F u D)

def machine (u D : Nat) (hD : 0 < D) : FinTM2 where
  K := Tape u D
  k₀ := .formula
  k₁ := accumulatorTape u D
  Γ _ := Bool
  Λ := Label u D
  main := .inl .inputCopyOut
  σ := State u D
  initialState := SourceGeneratorModel.initialState u D hD
  m := program

end

end MaxCutGames.Foundations.Hastad.SourceStartup

/-! Actual fixed-coefficient affine address construction. A finite literal phase
loads the coefficient, the checked width-two Horner machine reads coefficient
and preserved offset with the rank as its radix, then the literal field is
actually consumed. All operands and work stacks are restored. -/

namespace MaxCutGames.Foundations.Hastad.SourceBasePhase

open Turing Complexity
open Target SourceContexts SourceOccurrences SourceAddressDescriptors
open MaxCutGames.Reduction.MachineSubstitution

inductive Label
  | seed
  | horner (label : MachineHorner.Label 2)
  | clear
  deriving DecidableEq, Fintype

abbrev Layout := MachineHorner.Layout 2

def digits (coefficient offset : Nat) (i : Nat) : Nat :=
  if i = 0 then coefficient else offset

theorem horner_value (coefficient rank offset : Nat) :
    MachineHorner.value rank (digits coefficient offset) 2 = coefficient * rank + offset := by
  simp [MachineHorner.value, digits, Nat.mul_comm]

def steps (coefficient rank offset : Nat) : Nat :=
  MachineHorner.steps rank (digits coefficient offset) 2 + coefficient + 2

def operandLength (rank offset : Nat) : Nat :=
  (encodeWord rank).length + (encodeWord offset).length

noncomputable def timePolynomial (coefficient : Nat) : Polynomial Nat :=
  (MachineHorner.timePolynomial 2).comp (Polynomial.X + Polynomial.C coefficient) +
    Polynomial.C (coefficient + 2)

theorem timePolynomial_eval (coefficient n : Nat) :
    (timePolynomial coefficient).eval n =
      (MachineHorner.timePolynomial 2).eval (n + coefficient) + coefficient + 2 := by
  simp [timePolynomial, Polynomial.eval_comp, Nat.add_assoc]

theorem steps_le_timePolynomial (coefficient rank offset : Nat) :
    steps coefficient rank offset ≤ (timePolynomial coefficient).eval (operandLength rank offset) := by
  have hr : rank ≤ operandLength rank offset + coefficient := by
    simp only [operandLength, encodeWord_length]
    omega
  have hd : ∀ i, i < 2 → digits coefficient offset i ≤ operandLength rank offset + coefficient := by
    intro i _
    simp only [digits, operandLength, encodeWord_length]
    split <;> omega
  have h := MachineHorner.steps_le_timePolynomial rank (digits coefficient offset) 2
    (operandLength rank offset + coefficient) hr hd
  rw [timePolynomial_eval]
  unfold steps
  omega

variable {K Λ σ : Type} [DecidableEq K]

def statement (slots : Layout ↪ K) (coefficient : Nat) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .seed => pushWord (slots (.inr 0)) (encodeWord coefficient).reverse
      (.goto fun _ => labels (.horner .start))
  | .horner label => MachineHorner.statement slots (fun l => labels (.horner l))
      (some (labels .clear)) label
  | .clear => MachineHorner.drainLoop (slots (.inr 0)) (labels .clear) exit

def program (slots : Layout ↪ K) (coefficient : Nat) :
    Label → TM2.Stmt (fun _ : K => Bool) Label (MachineHorner.State σ) :=
  statement slots coefficient id none

def coefficientTapes (slots : Layout ↪ K) (base : K → List Bool) (coefficient : Nat) : K → List Bool :=
  Function.update base (slots (.inr 0)) (encodeWord coefficient)

/-- Exact affine execution, including coefficient initialization and cleanup. -/
theorem affineTrace (slots : Layout ↪ K) (coefficient : Nat) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots coefficient labels exit label)
    (base : K → List Bool) (rank offset : Nat)
    (rankWord : base (slots (.inl 0)) = encodeWord rank)
    (offsetWord : base (slots (.inr 1)) = encodeWord offset)
    (coefficientEmpty : base (slots (.inr 0)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps coefficient rank offset]
      (some ⟨some (labels .seed), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        MachineHorner.resultTapes slots base (coefficient * rank + offset)⟩ := by
  have hc (i : Fin 6) : slots (.inl i) ≠ slots (.inr 0) := slots.injective.ne (by simp)
  have hd : slots (.inr 1) ≠ slots (.inr 0) := slots.injective.ne (by decide)
  let seeded := coefficientTapes slots base coefficient
  have hseed : (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .seed), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (.horner .start)), ((ambient, ()), register), seeded⟩ := by
    change some (TM2.stepAux (p (labels .seed)) ((ambient, ()), register) base) = _
    rw [atLabels .seed]
    simp only [statement, stepAux_pushWord, List.reverse_reverse, TM2.stepAux,
      coefficientEmpty, List.append_nil, seeded, coefficientTapes]
  have hradix : seeded (slots (.inl 0)) = encodeWord rank := by
    simp [seeded, coefficientTapes, hc, rankWord]
  have hdigits : ∀ i : Fin 2, seeded (slots (.inr i)) = encodeWord (digits coefficient offset i.val) := by
    intro i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · simp [seeded, coefficientTapes, digits]
    · simp [seeded, coefficientTapes, digits, hd, offsetWord]
  have hclean : MachineHorner.Clean slots seeded := {
    accA := by simpa only [seeded, coefficientTapes, Function.update_of_ne (hc 1)] using clean.accA
    accB := by simpa only [seeded, coefficientTapes, Function.update_of_ne (hc 2)] using clean.accB
    counter := by simpa only [seeded, coefficientTapes, Function.update_of_ne (hc 4)] using clean.counter
    scratch := by simpa only [seeded, coefficientTapes, Function.update_of_ne (hc 5)] using clean.scratch
  }
  have hhorner := MachineHorner.hornerTrace slots (fun l => labels (.horner l))
    (some (labels .clear)) p (fun l => atLabels (.horner l)) seeded rank
    (digits coefficient offset) hradix hdigits hclean ambient register
  rw [horner_value] at hhorner
  let after := MachineHorner.resultTapes slots seeded (coefficient * rank + offset)
  have hafter : after (slots (.inr 0)) = encodeWord coefficient := by
    simp [after, MachineHorner.resultTapes, Ne.symm (hc 3), seeded, coefficientTapes]
  have hstart : Function.update after (slots (.inr 0)) (encodeWord coefficient ++ []) = after := by
    rw [List.append_nil, ← hafter, Function.update_eq_self]
  have hfinish : Function.update after (slots (.inr 0)) [] =
      MachineHorner.resultTapes slots base (coefficient * rank + offset) := by
    funext k
    by_cases ho : k = slots (.inl 3)
    · subst k
      simp [after, MachineHorner.resultTapes, seeded, coefficientTapes, hc 3]
    · by_cases hk : k = slots (.inr 0)
      · subst k
        simp [MachineHorner.resultTapes, Ne.symm (hc 3), coefficientEmpty]
      · simp [after, MachineHorner.resultTapes, seeded, coefficientTapes, ho, hk]
  have hclear := MachineHorner.drainTrace (slots (.inr 0)) (labels .clear) exit p
    (atLabels .clear) after coefficient [] ambient none
  rw [hstart, hfinish] at hclear
  rw [show steps coefficient rank offset = (coefficient + 1) +
      (MachineHorner.steps rank (digits coefficient offset) 2 + 1) by unfold steps; omega,
    Function.iterate_add_apply, Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step p))^[coefficient + 1]
    ((MachineComposition.advance (TM2.step p))^[MachineHorner.steps rank (digits coefficient offset) 2]
      ((MachineComposition.advance (TM2.step p))^[1]
        (some ⟨some (labels .seed), ((ambient, ()), register), base⟩))) = _
  rw [hseed, hhorner]
  exact hclear

def affineInTime (slots : Layout ↪ K) (coefficient : Nat) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots coefficient labels exit label)
    (base : K → List Bool) (rank offset : Nat)
    (rankWord : base (slots (.inl 0)) = encodeWord rank)
    (offsetWord : base (slots (.inr 1)) = encodeWord offset)
    (coefficientEmpty : base (slots (.inr 0)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .seed), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (coefficient * rank + offset)⟩)
      (steps coefficient rank offset) where
  steps := steps coefficient rank offset
  evals_in_steps := affineTrace slots coefficient labels exit p atLabels base rank offset
    rankWord offsetWord coefficientEmpty clean ambient register
  steps_le_m := Nat.le_refl _

def affineInPolynomialTime (slots : Layout ↪ K) (coefficient : Nat) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots coefficient labels exit label)
    (base : K → List Bool) (rank offset : Nat)
    (rankWord : base (slots (.inl 0)) = encodeWord rank)
    (offsetWord : base (slots (.inr 1)) = encodeWord offset)
    (coefficientEmpty : base (slots (.inr 0)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .seed), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (coefficient * rank + offset)⟩)
      ((timePolynomial coefficient).eval (operandLength rank offset)) where
  steps := steps coefficient rank offset
  evals_in_steps := affineTrace slots coefficient labels exit p atLabels base rank offset
    rankWord offsetWord coefficientEmpty clean ambient register
  steps_le_m := steps_le_timePolynomial coefficient rank offset

def programInTime (slots : Layout ↪ K) (coefficient : Nat) (base : K → List Bool) (rank offset : Nat)
    (rankWord : base (slots (.inl 0)) = encodeWord rank)
    (offsetWord : base (slots (.inr 1)) = encodeWord offset)
    (coefficientEmpty : base (slots (.inr 0)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program (σ := σ) slots coefficient))
      ⟨some .seed, ((ambient, ()), register), base⟩
      (some ⟨none, ((ambient, ()), none), MachineHorner.resultTapes slots base (coefficient * rank + offset)⟩)
      ((timePolynomial coefficient).eval (operandLength rank offset)) :=
  affineInPolynomialTime slots coefficient id none (program slots coefficient) (fun _ => rfl)
    base rank offset rankWord offsetWord coefficientEmpty clean ambient register

/-- Left query-block base from the preserved variable tuple rank and a zero offset field. -/
def leftBaseInTime (F : Formula) (u : Nat) (c : ClauseContext F u) (v : VariableContext F u)
    (slots : Layout ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots (2 ^ (2 ^ u)) labels exit label)
    (base : K → List Bool)
    (rankWord : base (slots (.inl 0)) = encodeWord (((variableEncoding F u).code v).val))
    (zeroWord : base (slots (.inr 1)) = encodeWord 0)
    (coefficientEmpty : base (slots (.inr 0)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .seed), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (baseValue F u c v 0)⟩)
      ((timePolynomial (2 ^ (2 ^ u))).eval (operandLength (((variableEncoding F u).code v).val) 0)) := by
  have h := affineInPolynomialTime slots (2 ^ (2 ^ u)) labels exit p atLabels base
    (((variableEncoding F u).code v).val) 0 rankWord zeroWord coefficientEmpty clean ambient register
  have hv : 2 ^ (2 ^ u) * (((variableEncoding F u).code v).val) + 0 = baseValue F u c v 0 := by
    simp [baseValue]
  simpa only [hv] using h

/-- Right query-block base using the globally retained left-block size. -/
def rightBaseInTime (F : Formula) (u : Nat) (c : ClauseContext F u) (v : VariableContext F u)
    (slots : Layout ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots (2 ^ (8 ^ u)) labels exit label)
    (base : K → List Bool)
    (rankWord : base (slots (.inl 0)) = encodeWord (((clauseEncoding F u).code c).val))
    (leftBlockWord : base (slots (.inr 1)) = encodeWord (2 ^ (2 ^ u) * F.«variables» ^ u))
    (coefficientEmpty : base (slots (.inr 0)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .seed), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (baseValue F u c v 1)⟩)
      ((timePolynomial (2 ^ (8 ^ u))).eval
        (operandLength (((clauseEncoding F u).code c).val) (2 ^ (2 ^ u) * F.«variables» ^ u))) := by
  have h := affineInPolynomialTime slots (2 ^ (8 ^ u)) labels exit p atLabels base
    (((clauseEncoding F u).code c).val) (2 ^ (2 ^ u) * F.«variables» ^ u)
    rankWord leftBlockWord coefficientEmpty clean ambient register
  have hv : 2 ^ (8 ^ u) * (((clauseEncoding F u).code c).val) + 2 ^ (2 ^ u) * F.«variables» ^ u =
      baseValue F u c v 1 := by
    simp [baseValue, Nat.mul_comm, Nat.add_comm]
  simpa only [hv] using h

/-- The retained dummy register is among the unchanged external tapes. -/
theorem resultTapes_dummy (slots : Layout ↪ K) (base : K → List Bool) (value : Nat)
    (dummy : K) (distinct : dummy ≠ slots (.inl 3)) :
    MachineHorner.resultTapes slots base value dummy = base dummy :=
  MachineHorner.resultTapes_other slots base value dummy distinct

def machine (coefficient : Nat) : FinTM2 where
  K := Layout
  k₀ := .inl 0
  k₁ := .inl 3
  Γ _ := Bool
  Λ := Label
  main := .seed
  σ := MachineHorner.State Unit
  initialState := (((), ()), none)
  m := program (Function.Embedding.refl Layout) coefficient

def machineInTime (coefficient rank offset : Nat) (base : Layout → List Bool)
    (rankWord : base (.inl 0) = encodeWord rank) (offsetWord : base (.inr 1) = encodeWord offset)
    (coefficientEmpty : base (.inr 0) = [])
    (clean : MachineHorner.Clean (Function.Embedding.refl _) base) (register : Option Bool) :
    StateTransition.EvalsToInTime (machine coefficient).step
      ⟨some Label.seed, (((), ()), register), base⟩
      (some ⟨none, (((), ()), none),
        MachineHorner.resultTapes (Function.Embedding.refl _) base (coefficient * rank + offset)⟩)
      ((timePolynomial coefficient).eval (operandLength rank offset)) :=
  programInTime (Function.Embedding.refl _) coefficient base rank offset rankWord offsetWord
    coefficientEmpty clean () register

end MaxCutGames.Foundations.Hastad.SourceBasePhase

end OAI
