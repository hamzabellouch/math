import OAI.Computability.UniqueGames.PCP.SourceContextClear
import OAI.Computability.UniqueGames.PCP.SourceDescriptorEmissionLemmas
import OAI.Computability.UniqueGames.PCP.SourceHeaderAccumulate
import OAI.Computability.UniqueGames.PCP.SourceHeaderCounts
import OAI.Computability.UniqueGames.PCP.SourceLoopInitLemmas
import OAI.Computability.UniqueGames.PCP.SourceQueryLoopLemmas
import OAI.Computability.UniqueGames.PCP.SourceSignaturePrepareLemmas

namespace OAI


namespace UniqueGamesTheorem.Foundations.Hastad.SourceQueryOrder

open Turing Complexity Target SourceContexts SourceOccurrences
open SourceLocalSignature SourceAddressDescriptors SourceLoopOrder


def occurrenceBits (F : Formula) (u D : Nat) (p : SourceIndex F u D) : List Bool :=
  encodeWords (UniqueGamesTheorem.Reduction.SourceEncoding.equationWords (sourceEquation F u D p))

def slotBits (F : Formula) (u D : Nat) (c : ClauseContext F u) (s : SlotContext u) :
    List Bool :=
  (testTapeEncoding u D).enumerate.flatMap (fun t => occurrenceBits F u D ((c, s), t))

def tupleBits (F : Formula) (u D : Nat) (c : ClauseContext F u) : List Bool :=
  (slotContextEncoding u).enumerate.flatMap (slotBits F u D c)

theorem equationBits_eq (F : Formula) (u D : Nat) (c : ClauseContext F u)
    (s : SlotContext u) (t : SourceQueryLoop.Query u D) :
    SourceTestAppend.equationBits u D (baseValue F u c (sampledVariables F c s))
      (ofContext F c s, t) = occurrenceBits F u D ((c, s), t) := by
  rw [occurrenceBits, sourceEquation_words]
  rfl

theorem prefixBits_eq_slotBits (F : Formula) (u D : Nat) (c : ClauseContext F u)
    (s : SlotContext u) (fallback : SourceQueryLoop.Query u D) :
    SourceQueryLoop.prefixBits u D (rankedQuery u D fallback)
      (baseValue F u c (sampledVariables F c s)) (ofContext F c s)
      (testTapeEncoding u D).size = slotBits F u D c s := by
  rw [query_prefixBits_eq_enumerate]
  unfold slotBits
  congr 1
  funext t
  exact equationBits_eq F u D c s t

variable {K Λ : Type} [DecidableEq K]

theorem sourceLoopInTime (F : Formula) (u D : Nat) (c : ClauseContext F u)
    (s : SlotContext u) (fallback initialQuery : SourceQueryLoop.Query u D)
    (layout : SourceTestAppend.Layout K)
    (labels : SourceQueryLoop.Label u D (testTapeEncoding u D).size → Λ)
    (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (SourceQueryLoop.State u D))
    (atLabels : ∀ l, p (labels l) = SourceQueryLoop.statement u D
      (testTapeEncoding u D).size (rankedQuery u D fallback) layout labels exit l)
    (base : K → List Bool)
    (sourceWords : ∀ side, base (layout.sources side) =
      encodeWord (baseValue F u c (sampledVariables F c s) side))
    (scratchEmpty : base layout.scratch = [])
    (temporaryEmpty : base layout.temporary = []) :
    ∃ lastQuery : SourceQueryLoop.Query u D,
      Nonempty (StateTransition.EvalsToInTime (TM2.step p)
        ⟨some (labels (.load ⟨0, Nat.zero_lt_succ _⟩)),
          ((ofContext F c s, initialQuery), none), base⟩
        (some ⟨exit, ((ofContext F c s, lastQuery), none),
          SourceTestAppend.resultTapes layout base (slotBits F u D c s)⟩)
        ((testTapeEncoding u D).size * (9 * nBits F u + 21) + 1)) := by
  have hbound : ∀ i, i < (testTapeEncoding u D).size →
      SourceTestAppend.steps u D (baseValue F u c (sampledVariables F c s))
        (ofContext F c s, rankedQuery u D fallback i) ≤ 9 * nBits F u + 20 := by
    intro i hi
    let run := SourceTestAppend.sourceAppendInTime F u D
      ((c, s), rankedQuery u D fallback i) layout
      (fun l => labels (.emit ⟨i, hi⟩ l))
      (some (labels (.load ⟨i + 1, by omega⟩))) p
      (fun l => atLabels (.emit ⟨i, hi⟩ l)) base sourceWords
      scratchEmpty temporaryEmpty none
    exact run.steps_le_m
  have h := SourceQueryLoop.loopInTime u D (testTapeEncoding u D).size
    (9 * nBits F u + 20) (rankedQuery u D fallback) layout labels exit p atLabels
    (ofContext F c s) initialQuery base (baseValue F u c (sampledVariables F c s))
    sourceWords scratchEmpty temporaryEmpty hbound
  rw [prefixBits_eq_slotBits] at h
  exact h

end UniqueGamesTheorem.Foundations.Hastad.SourceQueryOrder



namespace UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeModel

open Turing Complexity SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge


inductive BodyWork (Extra : Type)
  | leftBlock | dummy | bitCount | occurrenceCount
  | zero | rank | rightBase | leftBase
  | accA | accB | counter | arithScratch | coefficient
  | queryTemporary | queryScratch | accumulator
  | extra (value : Extra)
  deriving DecidableEq, Fintype

abbrev BodyExtra (Extra : Type) := SourceLoopInit.HeaderTape ⊕ BodyWork Extra
abbrev Arena (u : Nat) (Extra : Type) := SourceContextLoad.Tape u (BodyExtra Extra)
abbrev QueryState (u D : Nat) := SourceQueryLoop.State u D
abbrev ArithmeticState := MachineHorner.State Unit
abbrev State (u D : Nat) := SourceContextPrepare.State u (QueryState u D × ArithmeticState)
abbrev QueryMetadata (u : Nat) := SourceContextPrepare.LoadState ×
  (SourceSignaturePrepare.ProfileState u × (Signature u × ArithmeticState))
abbrev ArithmeticMetadata (u D : Nat) := SourceContextPrepare.LoadState ×
  (SourceSignaturePrepare.ProfileState u × (Signature u × QueryState u D))

variable {u D : Nat} {Extra : Type}

def workTape (role : BodyWork Extra) : Arena u Extra := .extra (.inr role)
def variableHeader : Arena u Extra := SourceLoopInit.variableHeader
def clauseHeader : Arena u Extra := SourceLoopInit.clauseHeader

def canonicalSignature (u : Nat) : Signature u :=
  ⟨fun _ => false, fun _ _ => false, fun _ => .first⟩

def canonicalState (initialQuery : SourceQueryLoop.Query u D) : State u D :=
  SourceContextPrepare.initialState (fun _ _ => false) (canonicalSignature u)
    (((canonicalSignature u, initialQuery), none), (((), ()), none))

def queryStateEquiv (u D : Nat) : QueryState u D × QueryMetadata u ≃ State u D where
  toFun x := (x.2.1, (x.2.2.1, (x.2.2.2.1, (x.1, x.2.2.2.2))))
  invFun x := (x.2.2.2.1, (x.1, (x.2.1, (x.2.2.1, x.2.2.2.2))))
  left_inv _ := rfl
  right_inv _ := rfl

def arithmeticStateEquiv (u D : Nat) : ArithmeticState × ArithmeticMetadata u D ≃ State u D where
  toFun x := (x.2.1, (x.2.2.1, (x.2.2.2.1, (x.2.2.2.2, x.1))))
  invFun x := (x.2.2.2.2, (x.1, (x.2.1, (x.2.2.1, x.2.2.2.1))))
  left_inv _ := rfl
  right_inv _ := rfl

def rankControls (header : SourceLoopInit.HeaderTape) : Fin 6 ↪ BodyExtra Extra where
  toFun
    | 0 => .inl header
    | 1 => .inr .accA
    | 2 => .inr .accB
    | 3 => .inr .rank
    | 4 => .inr .counter
    | 5 => .inr .arithScratch
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def clauseRankSlots : MachineHorner.Layout u ↪ Arena u Extra :=
  SourceRankPhase.clauseSlots (rankControls .clauseCount)

def variableRankSlots (selected : SlotContext u) : MachineHorner.Layout u ↪ Arena u Extra :=
  SourceRankPhase.variableSlots (rankControls .variableCount) selected

/-- Both address-base phases use the same clean arithmetic work tapes. The
right side adds the retained left block; the left side adds a seeded zero. -/
def baseSlots (right : Bool) : MachineHorner.Layout 2 ↪ Arena u Extra where
  toFun
    | .inl 0 => workTape .rank
    | .inl 1 => workTape .accA
    | .inl 2 => workTape .accB
    | .inl 3 => workTape (if right then .rightBase else .leftBase)
    | .inl 4 => workTape .counter
    | .inl 5 => workTape .arithScratch
    | .inr 0 => workTape .coefficient
    | .inr 1 => workTape (if right then .leftBlock else .zero)
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => cases right <;> fin_cases a <;> fin_cases b <;> simp_all [workTape]
      | inr b => cases right <;> fin_cases a <;> fin_cases b <;> simp_all [workTape]
    | inr a =>
      cases b with
      | inl b => cases right <;> fin_cases a <;> fin_cases b <;> simp_all [workTape]
      | inr b => cases right <;> fin_cases a <;> fin_cases b <;> simp_all [workTape]

def querySources : Fin 3 → Arena u Extra
  | 0 => workTape .leftBase
  | 1 => workTape .rightBase
  | 2 => workTape .dummy

def queryLayout : SourceTestAppend.Layout (Arena u Extra) where
  sources := querySources
  temporary := workTape .queryTemporary
  scratch := workTape .queryScratch
  accumulator := workTape .accumulator
  sourceTemporary side := by fin_cases side <;> simp [querySources, workTape]
  sourceScratch side := by fin_cases side <;> simp [querySources, workTape]
  sourceAccumulator side := by fin_cases side <;> simp [querySources, workTape]
  temporaryScratch := by simp [workTape]
  temporaryAccumulator := by simp [workTape]
  scratchAccumulator := by simp [workTape]

/-- Retained global headers are excluded from cleanup. -/
def perSlotCleanup : List (Arena u Extra) := [workTape .rank, workTape .leftBase]
def finalBaseCleanup : List (Arena u Extra) := [workTape .rank, workTape .rightBase, workTape .zero]

@[simp] theorem initializer_arena :
    SourceLoopInit.Tape u (BodyWork Extra) = Arena u Extra := rfl

end UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeModel



namespace UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorModel

open Turing Complexity SourceRuntimeModel


abbrev Extra (u D : Nat) := SourceHeaderCounts.Coefficients u D ⊕ Unit
abbrev Tape (u D : Nat) := SourceRuntimeModel.Arena u (Extra u D)
abbrev State (u D : Nat) := SourceRuntimeModel.State u D

def outputTape (u D : Nat) : Tape u D := workTape (.extra (.inr ()))
def accumulatorTape (u D : Nat) : Tape u D := workTape .accumulator

def headerControl (u D : Nat) : SourceHeaderCounts.Control ↪ Tape u D where
  toFun
    | .variableCount => variableHeader
    | .clauseCount => clauseHeader
    | .leftBlockSize => workTape .leftBlock
    | .rightTemporary => workTape .rank
    | .dummyIndex => workTape .dummy
    | .bitCount => workTape .bitCount
    | .occurrenceCount => workTape .occurrenceCount
    | .accA => workTape .accA
    | .accB => workTape .accB
    | .counter => workTape .counter
    | .scratch => workTape .arithScratch
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all [variableHeader, clauseHeader,
      SourceLoopInit.variableHeader, SourceLoopInit.clauseHeader, workTape]

def headerSlots (u D : Nat) : SourceHeaderCounts.Layout u D ↪ Tape u D where
  toFun
    | .inl c => headerControl u D c
    | .inr i => workTape (.extra (.inl i))
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl ((headerControl u D).injective h)
      | inr b => cases a <;> cases h
    | inr a =>
      cases b with
      | inl b => cases b <;> cases h
      | inr b => simpa [workTape] using h

abbrev ControlAmbient (u D : Nat) := (Unit × Unit) × ArithmeticMetadata u D

/-- Expose the existing arithmetic head register to the odometer and final
cleanup. This is a static finite-state equivalence, with no machine steps. -/
def controlStateEquiv (u D : Nat) :
    ControlAmbient u D × Option Bool ≃ State u D where
  toFun x := arithmeticStateEquiv u D ((x.1.1, x.2), x.1.2)
  invFun x :=
    let y := (arithmeticStateEquiv u D).symm x
    ((y.1.1, y.2), y.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def initialQuery (u D : Nat) (hD : 0 < D) : SourceQueryLoop.Query u D :=
  (fun _ => false, fun _ => ⟨0, hD⟩, fun _ => false)

def initialState (u D : Nat) (hD : 0 < D) : State u D :=
  canonicalState (initialQuery u D hD)

def initialAmbient (u D : Nat) (hD : 0 < D) : ControlAmbient u D :=
  ((controlStateEquiv u D).symm (initialState u D hD)).1

theorem control_initial (u D : Nat) (hD : 0 < D) :
    controlStateEquiv u D (initialAmbient u D hD, none) = initialState u D hD := rfl

noncomputable def coefficientKeys (u D : Nat) : List (SourceHeaderCounts.Coefficients u D) :=
  (List.finRange (CookLevin.PolynomialMachine.width
    (SourceHeaderCounts.polynomial u D .left))).map Sum.inl ++
  (List.finRange (CookLevin.PolynomialMachine.width
    (SourceHeaderCounts.polynomial u D .right))).map (fun i => Sum.inr (Sum.inl i)) ++
  (List.finRange (CookLevin.PolynomialMachine.width
    (SourceHeaderCounts.polynomial u D .occurrences))).map (fun i => Sum.inr (Sum.inr i))

theorem mem_coefficientKeys (u D : Nat) (i : SourceHeaderCounts.Coefficients u D) :
    i ∈ coefficientKeys u D := by
  cases i with
  | inl i => simp [coefficientKeys]
  | inr i => cases i <;> simp [coefficientKeys]

noncomputable def workKeys (u D : Nat) : List (BodyWork (Extra u D)) :=
  [.leftBlock, .dummy, .bitCount, .occurrenceCount, .zero, .rank, .rightBase, .leftBase,
    .accA, .accB, .counter, .arithScratch, .coefficient, .queryTemporary,
    .queryScratch, .accumulator] ++
  (coefficientKeys u D).map (fun i => .extra (.inl i)) ++ [.extra (.inr ())]

theorem mem_workKeys (u D : Nat) (i : BodyWork (Extra u D)) : i ∈ workKeys u D := by
  cases i
  case extra e =>
    cases e with
    | inl i =>
      exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨i, mem_coefficientKeys u D i, rfl⟩))
    | inr i => cases i; simp [workKeys]
  all_goals simp [workKeys]

/-- An explicit tape enumeration, fixed before the input is supplied. It uses
constructor lists and increasing finite coefficient indices. -/
noncomputable def allTapes (u D : Nat) : List (Tape u D) :=
  [.formula, .index, .work, .scratch, .copyScratch] ++
  (List.finRange u).map SourceContextLoad.Tape.current ++
  (List.finRange u).map SourceContextLoad.Tape.remaining ++
  (List.finRange u).flatMap (fun i =>
    (List.finRange 6).map (SourceContextLoad.Tape.field i)) ++
  [variableHeader, clauseHeader] ++ (workKeys u D).map workTape

theorem mem_allTapes (u D : Nat) (k : Tape u D) : k ∈ allTapes u D := by
  cases k with
  | formula => simp [allTapes]
  | index => simp [allTapes]
  | work => simp [allTapes]
  | scratch => simp [allTapes]
  | copyScratch => simp [allTapes]
  | current i => simp [allTapes]
  | remaining i => simp [allTapes]
  | field i j => simp [allTapes]
  | extra e =>
    cases e with
    | inl h => cases h <;> simp [allTapes, variableHeader, clauseHeader,
        SourceLoopInit.variableHeader, SourceLoopInit.clauseHeader]
    | inr w =>
      have h : workTape (u := u) w ∈ (workKeys u D).map (workTape (u := u)) :=
        List.mem_map.mpr ⟨w, mem_workKeys u D w, rfl⟩
      simp only [allTapes, List.mem_append]
      tauto

noncomputable def clearKeys (u D : Nat) : List (Tape u D) := by
  classical
  exact (allTapes u D).filter
    (fun k => decide (k ≠ accumulatorTape u D ∧ k ≠ outputTape u D))

theorem mem_clearKeys (u D : Nat) (k : Tape u D) :
    k ∈ clearKeys u D ↔ k ≠ accumulatorTape u D ∧ k ≠ outputTape u D := by
  classical
  simp [clearKeys, mem_allTapes]

theorem accumulator_ne_output (u D : Nat) : accumulatorTape u D ≠ outputTape u D := by
  simp [accumulatorTape, outputTape, workTape]

end UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorModel



namespace UniqueGamesTheorem.Foundations.Hastad.SourceStartup

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
    F.variables F.clauses.length

def outputTapes (F : Target.Formula) : Tape u D → List Bool :=
  SourceHeaderAccumulate.resultTapes (headerLayout u D) (countedTapes F)
    (SourceHeaderCounts.bitValue u F.variables F.clauses.length)
    (SourceHeaderCounts.occurrenceValue u D F.clauses.length)

def readyTapes (F : Target.Formula) : Tape u D → List Bool
  | .extra (.inr .leftBlock) => encodeWord (SourceHeaderCounts.leftValue u F.variables)
  | .extra (.inr .dummy) => encodeWord (SourceHeaderCounts.dummyValue u F.variables F.clauses.length)
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
    initializedTapes (u := u) (D := D) F variableHeader = encodeWord F.variables := by
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
      (SourceHeaderCounts.steps u D F.variables F.clauses.length +
        SourceHeaderCounts.bitValue u F.variables F.clauses.length +
        SourceHeaderCounts.occurrenceValue u D F.clauses.length + 4) := by
  have countRun := SourceHeaderCounts.inTime (headerSlots u D) Sum.inl (some (.inr false))
    arithmeticProgram (fun _ => rfl) (initializedTapes F) F.variables F.clauses.length
    (initialized_variableHeader F) (initialized_clauseHeader F) (initialized_clean F) () none
  have appendRun := SourceHeaderAccumulate.inTime (headerLayout u D) Sum.inr none
    arithmeticProgram (fun _ => rfl) (countedTapes F)
    (SourceHeaderCounts.bitValue u F.variables F.clauses.length)
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
      (SourceHeaderCounts.steps u D F.variables F.clauses.length +
        SourceHeaderCounts.bitValue u F.variables F.clauses.length +
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
    (SourceHeaderCounts.steps u D F.variables F.clauses.length +
      SourceHeaderCounts.bitValue u F.variables F.clauses.length +
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
    readyTapes (u := u) (D := D) F variableHeader = encodeWord F.variables := initialized_variableHeader F

@[simp] theorem ready_clauseHeader (F : Target.Formula) :
    readyTapes (u := u) (D := D) F clauseHeader = encodeWord F.clauses.length := initialized_clauseHeader F

@[simp] theorem ready_leftBlock (F : Target.Formula) :
    readyTapes (u := u) (D := D) F (workTape .leftBlock) =
      encodeWord (SourceHeaderCounts.leftValue u F.variables) := rfl

@[simp] theorem ready_dummy (F : Target.Formula) :
    readyTapes (u := u) (D := D) F (workTape .dummy) =
      encodeWord (SourceHeaderCounts.dummyValue u F.variables F.clauses.length) := rfl

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
  have hc := SourceHeaderCounts.steps_le_timePolynomial u D F.variables F.clauses.length
    (formulaBits F).length hn hm
  have hl : SourceHeaderCounts.leftValue u F.variables ≤
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

end UniqueGamesTheorem.Foundations.Hastad.SourceStartup



namespace UniqueGamesTheorem.Foundations.Hastad.SourceTupleTape

open Turing Complexity SourceContexts SourceRuntimeModel


structure Snapshot where
  rank : List Bool := []
  rightBase : List Bool := []
  leftBase : List Bool := []
  zero : List Bool := []
  emitted : List Bool := []
  deriving DecidableEq, Inhabited

variable {u : Nat} {Extra : Type}

def tapes (base : Arena u Extra → List Bool) (s : Snapshot) : Arena u Extra → List Bool
  | .extra (.inr .rank) => s.rank
  | .extra (.inr .rightBase) => s.rightBase
  | .extra (.inr .leftBase) => s.leftBase
  | .extra (.inr .zero) => s.zero
  | .extra (.inr .accumulator) => s.emitted.reverse ++ base (workTape .accumulator)
  | k => base k

@[simp] theorem tapes_rank (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .rank) = s.rank := rfl
@[simp] theorem tapes_rightBase (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .rightBase) = s.rightBase := rfl
@[simp] theorem tapes_leftBase (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .leftBase) = s.leftBase := rfl
@[simp] theorem tapes_zero (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .zero) = s.zero := rfl
@[simp] theorem tapes_accumulator (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .accumulator) = s.emitted.reverse ++ base (workTape .accumulator) := rfl
@[simp] theorem tapes_coefficient (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .coefficient) = base (workTape .coefficient) := rfl
@[simp] theorem tapes_dummy (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .dummy) = base (workTape .dummy) := rfl
@[simp] theorem tapes_leftBlock (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .leftBlock) = base (workTape .leftBlock) := rfl
@[simp] theorem tapes_queryTemporary (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .queryTemporary) = base (workTape .queryTemporary) := rfl
@[simp] theorem tapes_queryScratch (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .queryScratch) = base (workTape .queryScratch) := rfl
@[simp] theorem tapes_field (base : Arena u Extra → List Bool) (s : Snapshot) (j : Fin u) (k : Fin 6) :
    tapes base s (.field j k) = base (.field j k) := rfl
@[simp] theorem tapes_current (base : Arena u Extra → List Bool) (s : Snapshot) (j : Fin u) :
    tapes base s (.current j) = base (.current j) := rfl
@[simp] theorem tapes_formula (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s .formula = base .formula := rfl
@[simp] theorem tapes_index (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s .index = base .index := rfl
@[simp] theorem tapes_work (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s .work = base .work := rfl
@[simp] theorem tapes_variableHeader (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s variableHeader = base variableHeader := rfl
@[simp] theorem tapes_clauseHeader (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s clauseHeader = base clauseHeader := rfl

variable [DecidableEq Extra]

theorem update_rank (base : Arena u Extra → List Bool) (s : Snapshot) (value : List Bool) :
    Function.update (tapes base s) (workTape .rank) value = tapes base {s with rank := value} := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role => cases role <;> simp [tapes, workTape]

theorem update_rightBase (base : Arena u Extra → List Bool) (s : Snapshot) (value : List Bool) :
    Function.update (tapes base s) (workTape .rightBase) value = tapes base {s with rightBase := value} := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role => cases role <;> simp [tapes, workTape]

theorem update_leftBase (base : Arena u Extra → List Bool) (s : Snapshot) (value : List Bool) :
    Function.update (tapes base s) (workTape .leftBase) value = tapes base {s with leftBase := value} := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role => cases role <;> simp [tapes, workTape]

theorem update_zero (base : Arena u Extra → List Bool) (s : Snapshot) (value : List Bool) :
    Function.update (tapes base s) (workTape .zero) value = tapes base {s with zero := value} := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role => cases role <;> simp [tapes, workTape]

theorem update_emitted (base : Arena u Extra → List Bool) (s : Snapshot) (value : List Bool) :
    Function.update (tapes base s) (workTape .accumulator)
      (value.reverse ++ base (workTape .accumulator)) = tapes base {s with emitted := value} := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role => cases role <;> simp [tapes, workTape]

theorem query_result (base : Arena u Extra → List Bool) (s : Snapshot) (bits : List Bool) :
    SourceTestAppend.resultTapes queryLayout (tapes base s) bits =
      tapes base {s with emitted := s.emitted ++ bits} := by
  change Function.update (tapes base s) (workTape .accumulator)
    (bits.reverse ++ tapes base s (workTape .accumulator)) = _
  rw [tapes_accumulator]
  have h := update_emitted base s (s.emitted ++ bits)
  simpa only [List.reverse_append, List.append_assoc] using h

theorem horner_clause_result (base : Arena u Extra → List Bool) (s : Snapshot) (value : Nat) :
    MachineHorner.resultTapes clauseRankSlots (tapes base s) value =
      tapes base {s with rank := encodeWord value ++ s.rank} := by
  change Function.update (tapes base s) (workTape .rank)
    (encodeWord value ++ tapes base s (workTape .rank)) = _
  rw [tapes_rank, update_rank]

theorem horner_variable_result (base : Arena u Extra → List Bool) (s : Snapshot)
    (selected : SlotContext u) (value : Nat) :
    MachineHorner.resultTapes (variableRankSlots selected) (tapes base s) value =
      tapes base {s with rank := encodeWord value ++ s.rank} := by
  change Function.update (tapes base s) (workTape .rank)
    (encodeWord value ++ tapes base s (workTape .rank)) = _
  rw [tapes_rank, update_rank]

theorem horner_right_result (base : Arena u Extra → List Bool) (s : Snapshot) (value : Nat) :
    MachineHorner.resultTapes (baseSlots true) (tapes base s) value =
      tapes base {s with rightBase := encodeWord value ++ s.rightBase} := by
  change Function.update (tapes base s) (workTape .rightBase)
    (encodeWord value ++ tapes base s (workTape .rightBase)) = _
  rw [tapes_rightBase, update_rightBase]

theorem horner_left_result (base : Arena u Extra → List Bool) (s : Snapshot) (value : Nat) :
    MachineHorner.resultTapes (baseSlots false) (tapes base s) value =
      tapes base {s with leftBase := encodeWord value ++ s.leftBase} := by
  change Function.update (tapes base s) (workTape .leftBase)
    (encodeWord value ++ tapes base s (workTape .leftBase)) = _
  rw [tapes_leftBase, update_leftBase]

structure WorkClean (base : Arena u Extra → List Bool) : Prop where
  accA : base (workTape .accA) = []
  accB : base (workTape .accB) = []
  counter : base (workTape .counter) = []
  scratch : base (workTape .arithScratch) = []

omit [DecidableEq Extra] in
theorem clean_clause (base : Arena u Extra → List Bool) (s : Snapshot) (clean : WorkClean base) :
    MachineHorner.Clean clauseRankSlots (tapes base s) where
  accA := clean.accA
  accB := clean.accB
  counter := clean.counter
  scratch := clean.scratch

omit [DecidableEq Extra] in
theorem clean_variable (base : Arena u Extra → List Bool) (s : Snapshot) (selected : SlotContext u)
    (clean : WorkClean base) : MachineHorner.Clean (variableRankSlots selected) (tapes base s) where
  accA := clean.accA
  accB := clean.accB
  counter := clean.counter
  scratch := clean.scratch

omit [DecidableEq Extra] in
theorem clean_base (base : Arena u Extra → List Bool) (s : Snapshot) (right : Bool)
    (clean : WorkClean base) : MachineHorner.Clean (baseSlots right) (tapes base s) where
  accA := clean.accA
  accB := clean.accB
  counter := clean.counter
  scratch := clean.scratch

omit [DecidableEq Extra] in
theorem tapes_coordinateOutput {n : Nat} (j : Fin u) (clause : Target.Clause n)
    (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes (SourceContextLoad.coordinateOutput j clause base) s =
      SourceContextLoad.coordinateOutput j clause (tapes base s) := by
  funext k
  cases k <;> simp [tapes, SourceContextLoad.coordinateOutput, workTape]
  rename_i extra
  cases extra with
  | inl header => rfl
  | inr role => cases role <;> rfl

omit [DecidableEq Extra] in

theorem tapes_stageTapes (F : Target.Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool) (s : Snapshot) (r : Nat) :
    tapes (SourceContextLoad.stageTapes F c base r) s =
      SourceContextLoad.stageTapes F c (tapes base s) r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [SourceContextLoad.stageTapes]
    split
    · rw [tapes_coordinateOutput, ih]
    · exact ih

theorem final_tapes (base : Arena u Extra → List Bool) (emitted : List Bool)
    (hrank : base (workTape .rank) = []) (hright : base (workTape .rightBase) = [])
    (hleft : base (workTape .leftBase) = []) (hzero : base (workTape .zero) = []) :
    tapes base {emitted := emitted} =
      Function.update base (workTape .accumulator) (emitted.reverse ++ base (workTape .accumulator)) := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role =>
    cases role <;> simp_all [tapes, workTape]

theorem empty_tapes (base : Arena u Extra → List Bool)
    (hrank : base (workTape .rank) = []) (hright : base (workTape .rightBase) = [])
    (hleft : base (workTape .leftBase) = []) (hzero : base (workTape .zero) = []) :
    tapes base {} = base := by
  simpa using final_tapes base [] hrank hright hleft hzero

omit [DecidableEq Extra] in
theorem clear_loaded (F : Target.Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool) (s : Snapshot)
    (hfields : ∀ j k, base (.field j k) = []) (hindex : base .index = []) (hwork : base .work = []) :
    SourceContextClear.outputTapes (tapes (SourceContextLoad.stageTapes F c base u) s) = tapes base s := by
  rw [tapes_stageTapes]
  exact SourceContextClear.output_loaded_eq_base F c (tapes base s) hfields hindex hwork

/-- Apply the checked actual field cleanup directly to an overlaid loaded context. -/
def clearLoadedSnapshotInTime (F : Target.Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool) (s : Snapshot)
    (hfields : ∀ j k, base (.field j k) = []) (hindex : base .index = []) (hwork : base .work = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step SourceContextClear.program)
      ⟨some SourceContextClear.main, ((), register), tapes (SourceContextLoad.stageTapes F c base u) s⟩
      (some ⟨none, ((), none), tapes base s⟩)
      (6 * u * ((formulaBits F).length + 1) + 1) := by
  rw [tapes_stageTapes]
  exact SourceContextClear.clearLoadedToBaseInTime F c (tapes base s) hfields hindex hwork register

end UniqueGamesTheorem.Foundations.Hastad.SourceTupleTape

end OAI
