import Mathlib
import OAI.Computability.MaxCut.Machines.MachineExpanderTableProgram

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

theorem affine_source_ne_scratch (phase : AffinePhase) :
    affineSource phase ≠ .inr .unaryScratch := by cases phase <;> decide

theorem affine_source_ne_destination (phase : AffinePhase) :
    affineSource phase ≠ affineDestination phase := by cases phase <;> decide

theorem affine_scratch_ne_destination (phase : AffinePhase) :
    (.inr .unaryScratch : Tape) ≠ affineDestination phase := by cases phase <;> decide

/-- Exact final dependent tape family, with all other tape contents retained. -/
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

/-- The concrete Boolean view is pulled into unary-affine state coordinates,
executed from its actual statements, and transported back without extra steps. -/
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

/-- Actual family-program execution. Alphabet conversion is static equality
transport; the transition count is exactly the checked unary-affine count. -/
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

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

namespace MaxCutGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.AlphabetTable

/-- One scaled scan/restore, one bounded offset, the delimiter, and final jump. -/
def emitSteps (n : Nat) : Nat := 3 * (n + 1) + 6

theorem affinePlan_bits {σ : Type} {bound : Nat} (coefficient : Nat)
    (offset : σ → Fin bound) (n : Nat) (ambient : σ) :
    Emitter.prefixBits (affinePlan coefficient offset) (fun _ : Fin 1 => n) ambient 3 =
      encodeWord (coefficient * n + (offset ambient).val) := by
  change Emitter.prefixBits
    (Emitter.listCommands (Emitter.affineCommands [((0 : Fin 1), coefficient)] offset))
    (fun _ : Fin 1 => n) ambient
    (Emitter.affineCommands [((0 : Fin 1), coefficient)] offset).length = _
  rw [Emitter.bits_listCommands, Emitter.affineCommands_bits]
  simp [Emitter.affineValue]

theorem affinePlan_steps {σ : Type} {bound : Nat} (coefficient : Nat)
    (offset : σ → Fin bound) (n : Nat) :
    Emitter.prefixSteps (affinePlan coefficient offset) (fun _ : Fin 1 => n) 3 + 1 =
      emitSteps n := by
  simp [affinePlan, Emitter.prefixSteps, Emitter.commandAt, Emitter.listCommands,
    Emitter.affineCommands, Emitter.commandSteps, emitSteps]

/-- Every tape except the accumulator is literally retained. -/
def emittedWord {K : Type} [DecidableEq K]
    (target : K) (base : K → List Bool) (value : Nat) : K → List Bool :=
  Function.update base target ((encodeWord value).reverse ++ base target)

@[simp] theorem emittedWord_target {K : Type} [DecidableEq K]
    (target : K) (base : K → List Bool) (value : Nat) :
    emittedWord target base value target = (encodeWord value).reverse ++ base target := by
  simp [emittedWord]

theorem emittedWord_other {K : Type} [DecidableEq K]
    (target : K) (base : K → List Bool) (value : Nat)
    (tape : K) (different : tape ≠ target) :
    emittedWord target base value tape = base tape := by
  simp [emittedWord, different]

variable {ρ : Type} [Fintype ρ] {d : Nat}

@[simp] theorem program_firstEmit (positive : 0 < d) (H : Table (cloudSize d) d)
    (label : Emitter.Label 3 (degree d)) :
    program (ρ := ρ) positive H (.firstEmit label) =
      Emitter.statement (firstPlan ρ d) (fun _ : Fin 1 => Tape.inputVertex)
        .emitScratch .queryReverse Label.firstEmit (some Label.firstReverse) label := rfl

@[simp] theorem program_secondEmit (positive : 0 < d) (H : Table (cloudSize d) d)
    (label : Emitter.Label 3 (degree d)) :
    program (ρ := ρ) positive H (.secondEmit label) =
      Emitter.statement (secondPlan ρ d) (fun _ : Fin 1 => Tape.quotientFirst)
        .emitScratch .queryReverse Label.secondEmit (some Label.secondReverse) label := rfl

@[simp] theorem program_outputEmit (positive : 0 < d) (H : Table (cloudSize d) d)
    (label : Emitter.Label 3 (rowFactor d)) :
    program (ρ := ρ) positive H (.outputEmit label) =
      Emitter.statement (outputPlan ρ d) (fun _ : Fin 1 => Tape.quotientSecond)
        .emitScratch .output Label.outputEmit (some (Label.cleanup 0)) label := rfl

section Embedded

variable {K Λ : Type} [DecidableEq K]

/-- The code premise identifies concrete statements in a caller's program;
it does not assume any phase execution. -/
theorem firstEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .inputVertex) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.firstEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels .firstReverse), ((ambient, ()), none),
        emittedWord (ports .queryReverse) base (firstAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.firstEmit l)) =
      Emitter.statement (firstPlan ρ d) (fun _ : Fin 1 => ports .inputVertex)
        (ports .emitScratch) (ports .queryReverse) (fun k => labels (.firstEmit k))
        (some (labels .firstReverse)) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (firstPlan ρ d) (fun _ : Fin 1 => ports .inputVertex)
    (ports .emitScratch) (ports .queryReverse)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.firstEmit k)) (some (labels .firstReverse)) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [firstPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, firstAddress] using run

theorem secondEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .quotientFirst) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.secondEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels .secondReverse), ((ambient, ()), none),
        emittedWord (ports .queryReverse) base (secondAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.secondEmit l)) =
      Emitter.statement (secondPlan ρ d) (fun _ : Fin 1 => ports .quotientFirst)
        (ports .emitScratch) (ports .queryReverse) (fun k => labels (.secondEmit k))
        (some (labels .secondReverse)) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (secondPlan ρ d) (fun _ : Fin 1 => ports .quotientFirst)
    (ports .emitScratch) (ports .queryReverse)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.secondEmit k)) (some (labels .secondReverse)) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [secondPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, secondAddress] using run

theorem outputEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .quotientSecond) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.outputEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels (.cleanup 0)), ((ambient, ()), none),
        emittedWord (ports .output) base (outputAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.outputEmit l)) =
      Emitter.statement (outputPlan ρ d) (fun _ : Fin 1 => ports .quotientSecond)
        (ports .emitScratch) (ports .output) (fun k => labels (.outputEmit k))
        (some (labels (.cleanup 0))) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (outputPlan ρ d) (fun _ : Fin 1 => ports .quotientSecond)
    (ports .emitScratch) (ports .output)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.outputEmit k)) (some (labels (.cleanup 0))) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [outputPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, outputAddress] using run

def firstEmitInTimeAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .inputVertex) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (.firstEmit (Emitter.labelAt 3 _ 0 .entry))), ((ambient, ()), none), base⟩
      (some ⟨some (labels .firstReverse), ((ambient, ()), none),
        emittedWord (ports .queryReverse) base (firstAddress n ambient.1.2)⟩) (emitSteps n) where
  steps := emitSteps n
  evals_in_steps := firstEmitTraceAt positive H ports portsInjective labels exit target atLabels
    n base source scratch ambient
  steps_le_m := Nat.le_refl _

def secondEmitInTimeAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .quotientFirst) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (.secondEmit (Emitter.labelAt 3 _ 0 .entry))), ((ambient, ()), none), base⟩
      (some ⟨some (labels .secondReverse), ((ambient, ()), none),
        emittedWord (ports .queryReverse) base (secondAddress n ambient.1.2)⟩) (emitSteps n) where
  steps := emitSteps n
  evals_in_steps := secondEmitTraceAt positive H ports portsInjective labels exit target atLabels
    n base source scratch ambient
  steps_le_m := Nat.le_refl _

def outputEmitInTimeAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .quotientSecond) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (.outputEmit (Emitter.labelAt 3 _ 0 .entry))), ((ambient, ()), none), base⟩
      (some ⟨some (labels (.cleanup 0)), ((ambient, ()), none),
        emittedWord (ports .output) base (outputAddress n ambient.1.2)⟩) (emitSteps n) where
  steps := emitSteps n
  evals_in_steps := outputEmitTraceAt positive H ports portsInjective labels exit target atLabels
    n base source scratch ambient
  steps_le_m := Nat.le_refl _

end Embedded

theorem firstEmitTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (n : Nat) (base : Tape → List Bool)
    (source : base .inputVertex = encodeWord n) (scratch : base .emitScratch = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step (program positive H)))^[emitSteps n]
      (some ⟨some (.firstEmit (Emitter.labelAt 3 _ 0 .entry)),
        ((ambient, ()), none), base⟩) =
      some ⟨some .firstReverse, ((ambient, ()), none),
        emittedWord .queryReverse base (firstAddress n ambient.1.2)⟩ := by
  exact firstEmitTraceAt positive H id Function.injective_id id none (program positive H)
    (fun _ => rfl) n base source scratch ambient

theorem secondEmitTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (n : Nat) (base : Tape → List Bool)
    (source : base .quotientFirst = encodeWord n) (scratch : base .emitScratch = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step (program positive H)))^[emitSteps n]
      (some ⟨some (.secondEmit (Emitter.labelAt 3 _ 0 .entry)),
        ((ambient, ()), none), base⟩) =
      some ⟨some .secondReverse, ((ambient, ()), none),
        emittedWord .queryReverse base (secondAddress n ambient.1.2)⟩ := by
  exact secondEmitTraceAt positive H id Function.injective_id id none (program positive H)
    (fun _ => rfl) n base source scratch ambient

theorem outputEmitTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (n : Nat) (base : Tape → List Bool)
    (source : base .quotientSecond = encodeWord n) (scratch : base .emitScratch = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step (program positive H)))^[emitSteps n]
      (some ⟨some (.outputEmit (Emitter.labelAt 3 _ 0 .entry)),
        ((ambient, ()), none), base⟩) =
      some ⟨some (.cleanup 0), ((ambient, ()), none),
        emittedWord .output base (outputAddress n ambient.1.2)⟩ := by
  exact outputEmitTraceAt positive H id Function.injective_id id none (program positive H)
    (fun _ => rfl) n base source scratch ambient

def firstEmitInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (n : Nat) (base : Tape → List Bool)
    (source : base .inputVertex = encodeWord n) (scratch : base .emitScratch = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.firstEmit (Emitter.labelAt 3 _ 0 .entry)), ((ambient, ()), none), base⟩
      (some ⟨some .firstReverse, ((ambient, ()), none),
        emittedWord .queryReverse base (firstAddress n ambient.1.2)⟩) (emitSteps n) where
  steps := emitSteps n
  evals_in_steps := firstEmitTrace positive H n base source scratch ambient
  steps_le_m := Nat.le_refl _

def secondEmitInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (n : Nat) (base : Tape → List Bool)
    (source : base .quotientFirst = encodeWord n) (scratch : base .emitScratch = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.secondEmit (Emitter.labelAt 3 _ 0 .entry)), ((ambient, ()), none), base⟩
      (some ⟨some .secondReverse, ((ambient, ()), none),
        emittedWord .queryReverse base (secondAddress n ambient.1.2)⟩) (emitSteps n) where
  steps := emitSteps n
  evals_in_steps := secondEmitTrace positive H n base source scratch ambient
  steps_le_m := Nat.le_refl _

def outputEmitInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (n : Nat) (base : Tape → List Bool)
    (source : base .quotientSecond = encodeWord n) (scratch : base .emitScratch = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.outputEmit (Emitter.labelAt 3 _ 0 .entry)), ((ambient, ()), none), base⟩
      (some ⟨some (.cleanup 0), ((ambient, ()), none),
        emittedWord .output base (outputAddress n ambient.1.2)⟩) (emitSteps n) where
  steps := emitSteps n
  evals_in_steps := outputEmitTrace positive H n base source scratch ambient
  steps_le_m := Nat.le_refl _

end MaxCutGames.Foundations.Complexity.MachineExpanderRow

/-!
# Actual lookup and reversal phases of the expander row program

The Boolean phase selector chooses the first or second occurrence of the same
preserving lookup. The selected word is proved to be the actual stored reverse
index of the supplied graph row. All execution facts follow from the concrete
program statements; no phase execution is assumed.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineComposition

def lookupPhaseLabel {d : Nat} (second : Bool)
    (l : MachinePreservingLookupClean.Label) : Label d :=
  if second then .secondLookup l else .firstLookup l

def scanPhaseLabel {d : Nat} (second : Bool) : Label d :=
  if second then .secondScan else .firstScan

def reversePhaseLabel {d : Nat} (second : Bool) : Label d :=
  if second then .secondReverse else .firstReverse

def lookupPhasePort {d : Nat} (second : Bool) (control : Control d) : Fin (degree d) :=
  if second then secondOffset control else firstOffset control

def lookupPhaseAddress {d : Nat} (second : Bool) (vertex : Nat) (control : Control d) : Nat :=
  if second then secondAddress vertex control else firstAddress vertex control

theorem lookupPhaseAddress_eq_rowIndex {v d : Nat} (second : Bool)
    (vertex : Fin v) (control : Control d) :
    lookupPhaseAddress second vertex.val control =
      (rowIndex v (degree d) (vertex, lookupPhasePort second control)).val := by
  cases second
  · exact firstAddress_eq_rowIndex vertex control
  · exact secondAddress_eq_rowIndex vertex control

theorem lookupTape_injective : Function.Injective lookupTape := by decide

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

/-- The exact cleaned tape state produced by either lookup. -/
def lookupResultTapes (ports : Tape → K) (base : K → List Bool)
    (value : Nat) (indexSuffix : List Bool) : K → List Bool :=
  MachinePreservingLookup.initialTapes (ports ∘ lookupTape) base 0 indexSuffix []
    (encodeWord value ++ base (ports .lookupOutput))

theorem lookupResultTapes_index (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) (value : Nat) (indexSuffix : List Bool) :
    lookupResultTapes ports base value indexSuffix (ports .queryIndex) =
      encodeWord 0 ++ indexSuffix := by
  apply MachineLookup.tapes_index
  · exact fun h => (by decide : Tape.queryIndex ≠ .lookupWork) (distinct h)
  · exact fun h => (by decide : Tape.queryIndex ≠ .lookupOutput) (distinct h)

theorem lookupResultTapes_work (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) (value : Nat) (indexSuffix : List Bool) :
    lookupResultTapes ports base value indexSuffix (ports .lookupWork) = [] := by
  apply MachineLookup.tapes_source
  exact fun h => (by decide : Tape.lookupWork ≠ .lookupOutput) (distinct h)

theorem lookupResultTapes_output (ports : Tape → K)
    (base : K → List Bool) (value : Nat) (indexSuffix : List Bool) :
    lookupResultTapes ports base value indexSuffix (ports .lookupOutput) =
      encodeWord value ++ base (ports .lookupOutput) := by
  apply MachineLookup.tapes_destination

/-- Every tape outside the query, work, and lookup-output roles is retained. -/
theorem lookupResultTapes_other (ports : Tape → K) (base : K → List Bool)
    (value : Nat) (indexSuffix : List Bool) (p : K)
    (hi : p ≠ ports .queryIndex) (hw : p ≠ ports .lookupWork)
    (ho : p ≠ ports .lookupOutput) :
    lookupResultTapes ports base value indexSuffix p = base p := by
  exact MachineLookup.tapes_other _ _ _ p hi hw ho _ _ _ _

theorem lookupResultTapes_table (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) (value : Nat) (indexSuffix : List Bool) :
    lookupResultTapes ports base value indexSuffix (ports .table) = base (ports .table) := by
  apply lookupResultTapes_other
  all_goals intro h; have := distinct h; cases this

theorem lookupResultTapes_restore (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) (value : Nat) (indexSuffix : List Bool) :
    lookupResultTapes ports base value indexSuffix (ports .lookupRestore) =
      base (ports .lookupRestore) := by
  apply lookupResultTapes_other
  all_goals intro h; have := distinct h; cases this

section Lookup

variable {v d : Nat} (second : Bool) (positive : 0 < d)
    (H : Table (cloudSize d) d) (ports : Tape → K)
    (distinct : Function.Injective ports) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (base : K → List Bool) (G : Table v (degree d))
    (tableWord : base (ports .table) = encodeWords (rotationWords G))
    (scratchEmpty : base (ports .lookupRestore) = [])
    (x : Fin v × Fin (degree d)) (indexSuffix : List Bool)
    (counterWord : base (ports .queryIndex) =
      encodeWord (rowIndex v (degree d) x).val ++ indexSuffix)
    (workEmpty : base (ports .lookupWork) = [])
    (ambient : (Ambient ρ d × Fin (degree d)) × Unit) (register : Option Bool)

include positive H distinct exit code tableWord scratchEmpty counterWord workEmpty

/-- Actual first/second lookup execution on a stored graph row. The selected
reverse index is obtained from `rotationWords_getElem?`, not a caller premise. -/
theorem lookupPhaseTrace :
    (advance (TM2.step target))^[MachinePreservingLookupClean.steps
        (rotationWords G) (rowIndex v (degree d) x).val]
      (some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))),
        (ambient, register), base⟩) =
      some ⟨some (labels (scanPhaseLabel second)), (ambient, none),
        lookupResultTapes ports base (reverseIndex G (rowIndex v (degree d) x)).val
          indexSuffix⟩ := by
  apply MachinePreservingLookupClean.traceAt_fromTapes (ports ∘ lookupTape)
    (distinct.comp lookupTape_injective)
    (fun l => labels (lookupPhaseLabel second l)) (some (labels (scanPhaseLabel second)))
    target
  · intro l
    cases second
    · exact code (.firstLookup l)
    · exact code (.secondLookup l)
  · exact tableWord
  · exact scratchEmpty
  · exact rotationWords_getElem? G (rowIndex v (degree d) x)
  · exact counterWord
  · exact workEmpty

/-- A linear bound in the original encoded table length for the same actual
phase. This includes the copy, restore, lookup, and residual cleanup. -/
def lookupPhaseInTime :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))),
        (ambient, register), base⟩
      (some ⟨some (labels (scanPhaseLabel second)), (ambient, none),
        lookupResultTapes ports base (reverseIndex G (rowIndex v (degree d) x)).val
          indexSuffix⟩)
      (6 * (encodeWords (rotationWords G)).length + 4) where
  steps := MachinePreservingLookupClean.steps (rotationWords G) (rowIndex v (degree d) x).val
  evals_in_steps := lookupPhaseTrace second positive H ports distinct labels exit target code
    base G tableWord scratchEmpty x indexSuffix counterWord workEmpty ambient register
  steps_le_m := MachinePreservingLookupClean.steps_le (rotationWords G) _ _
    (rotationWords_getElem? G (rowIndex v (degree d) x))

end Lookup

variable {d : Nat} (second : Bool) (positive : 0 < d)
    (H : Table (cloudSize d) d) (ports : Tape → K)
    (distinct : Function.Injective ports) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (base : K → List Bool)
    (ambient : (Ambient ρ d × Fin (degree d)) × Unit) (register : Option Bool)

include positive H distinct exit code

/-- The reversal consumes the reverse query word and prepends its forward
encoding to the index tape, retaining every other tape and finite state. -/
theorem reversePhaseTrace :
    (advance (TM2.step target))^[(base (ports .queryReverse)).length + 1]
      (some ⟨some (labels (reversePhaseLabel second)), (ambient, register), base⟩) =
      some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))), (ambient, none),
        Reduction.MachineTransfer.tapesAt (ports .queryReverse) (ports .queryIndex) base []
          ((base (ports .queryReverse)).reverse ++ base (ports .queryIndex))⟩ := by
  have h := Reduction.MachineTransfer.transferAt_fromTapes
    (ports .queryReverse) (ports .queryIndex)
    (fun h => (by decide : Tape.queryReverse ≠ .queryIndex) (distinct h))
    id false (labels (reversePhaseLabel second))
    (some (labels (lookupPhaseLabel second (.run .copyFirst)))) target
    (by cases second <;> exact code _) base ambient register
  unfold Reduction.MachineTransfer.nextAt at h
  unfold advance
  simpa only [List.map_id] using h

def reversePhaseInTime :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (reversePhaseLabel second)), (ambient, register), base⟩
      (some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))), (ambient, none),
        Reduction.MachineTransfer.tapesAt (ports .queryReverse) (ports .queryIndex) base []
          ((base (ports .queryReverse)).reverse ++ base (ports .queryIndex))⟩)
      ((base (ports .queryReverse)).length + 1) where
  steps := (base (ports .queryReverse)).length + 1
  evals_in_steps := reversePhaseTrace second positive H ports distinct labels exit target code
    base ambient register
  steps_le_m := Nat.le_refl _

/-- Reversing an actual emitted unary field takes exactly `index + 2` steps.
This includes consuming the field's delimiter and leaving the reversal loop. -/
theorem reversePhaseTrace_unary (index : Nat) (suffix : List Bool)
    (queryWord : base (ports .queryReverse) = (encodeWord index).reverse)
    (indexWord : base (ports .queryIndex) = suffix) :
    (advance (TM2.step target))^[index + 2]
      (some ⟨some (labels (reversePhaseLabel second)), (ambient, register), base⟩) =
      some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))), (ambient, none),
        Reduction.MachineTransfer.tapesAt (ports .queryReverse) (ports .queryIndex) base []
          (encodeWord index ++ suffix)⟩ := by
  have h := reversePhaseTrace second positive H ports distinct labels exit target code
    base ambient register
  simpa only [queryWord, indexWord, List.length_reverse, encodeWord_length,
    List.reverse_reverse, Nat.add_assoc] using h

end MaxCutGames.Foundations.Complexity.MachineExpanderRow

namespace MaxCutGames.Foundations.Complexity.MachineExpanderRow

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

@[simp] private theorem dirtyTape_zero : dirtyTape 0 = .queryIndex := rfl
@[simp] private theorem dirtyTape_one : dirtyTape 1 = .lookupOutput := rfl
@[simp] private theorem dirtyTape_two : dirtyTape 2 = .quotientFirst := rfl
@[simp] private theorem dirtyTape_three : dirtyTape 3 = .quotientSecond := rfl
@[simp] private theorem dirtyTape_four : dirtyTape 4 = .remainderFirst := rfl
@[simp] private theorem dirtyTape_five : dirtyTape 5 = .remainderSecond := rfl

variable {K Λ ρ : Type} [DecidableEq K]

def cleanupTapes (ports : Tape → K) (base : K → List Bool) : K → List Bool :=
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update base (ports .queryIndex) [])
            (ports .lookupOutput) [])
          (ports .quotientFirst) [])
        (ports .quotientSecond) [])
      (ports .remainderFirst) [])
    (ports .remainderSecond) []

def cleanupSteps (ports : Tape → K) (base : K → List Bool) : Nat :=
  ((base (ports .queryIndex)).length + 1) +
  ((base (ports .lookupOutput)).length + 1) +
  ((base (ports .quotientFirst)).length + 1) +
  ((base (ports .quotientSecond)).length + 1) +
  ((base (ports .remainderFirst)).length + 1) +
  ((base (ports .remainderSecond)).length + 1)

omit [DecidableEq K] in
theorem cleanupSteps_eq_sum (ports : Tape → K) (base : K → List Bool) :
    cleanupSteps ports base = ∑ i : Fin 6, ((base (ports (dirtyTape i))).length + 1) := by
  simp [cleanupSteps, Fin.sum_univ_succ, Nat.add_assoc]

@[simp] theorem cleanupTapes_dirty (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) (i : Fin 6) :
    cleanupTapes ports base (ports (dirtyTape i)) = [] := by
  fin_cases i <;>
    simp [cleanupTapes, distinct.eq_iff]

/-- Every tape outside the six named work roles keeps its exact contents. -/
theorem cleanupTapes_other (ports : Tape → K) (base : K → List Bool) (k : K)
    (outside : ∀ i : Fin 6, k ≠ ports (dirtyTape i)) :
    cleanupTapes ports base k = base k := by
  have h0 := outside 0
  have h1 := outside 1
  have h2 := outside 2
  have h3 := outside 3
  have h4 := outside 4
  have h5 := outside 5
  change k ≠ ports .queryIndex at h0
  change k ≠ ports .lookupOutput at h1
  change k ≠ ports .quotientFirst at h2
  change k ≠ ports .quotientSecond at h3
  change k ≠ ports .remainderFirst at h4
  change k ≠ ports .remainderSecond at h5
  simp [cleanupTapes, h0, h1, h2, h3, h4, h5]

@[simp] theorem cleanupTapes_table (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) :
    cleanupTapes ports base (ports .table) = base (ports .table) := by
  simp [cleanupTapes, distinct.eq_iff]

@[simp] theorem cleanupTapes_inputVertex (ports : Tape → K)
    (distinct : Function.Injective ports) (base : K → List Bool) :
    cleanupTapes ports base (ports .inputVertex) = base (ports .inputVertex) := by
  simp [cleanupTapes, distinct.eq_iff]

@[simp] theorem cleanupTapes_output (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) :
    cleanupTapes ports base (ports .output) = base (ports .output) := by
  simp [cleanupTapes, distinct.eq_iff]

private theorem join_trace_inline_MachineExpanderRowCleanup {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

variable [Fintype ρ] {d : Nat}

/-- One cleanup phase follows the actual drain instruction at its placed label. -/
theorem cleanupOneTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (i : Fin 6) (base : K → List Bool) (state : State ρ d) :
    (advance (TM2.step target))^[((base (ports (dirtyTape i))).length + 1)]
      (some ⟨some (labels (.cleanup i)), state, base⟩) =
      some ⟨some (if hi : i.val + 1 < 6 then labels (.cleanup ⟨i.val + 1, hi⟩)
          else labels .done),
        (state.1, none), Function.update base (ports (dirtyTape i)) []⟩ := by
  have run := MachineDrain.drainTrace (ports (dirtyTape i)) (labels (.cleanup i))
    (some (if hi : i.val + 1 < 6 then labels (.cleanup ⟨i.val + 1, hi⟩)
      else labels .done)) target
    (by simpa only [statement] using code (.cleanup i))
    base (base (ports (dirtyTape i))) state.1 state.2
  simpa only [Function.update_eq_self] using run

/-- All six phases execute in the common program, with exactly the sum of
the six initial word lengths plus one empty-branch transition per tape. -/
theorem cleanupTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    (advance (TM2.step target))^[cleanupSteps ports base]
      (some ⟨some (labels (.cleanup 0)), state, base⟩) =
      some ⟨some (labels .done), (state.1, none), cleanupTapes ports base⟩ := by
  let t1 := Function.update base (ports .queryIndex) []
  let t2 := Function.update t1 (ports .lookupOutput) []
  let t3 := Function.update t2 (ports .quotientFirst) []
  let t4 := Function.update t3 (ports .quotientSecond) []
  let t5 := Function.update t4 (ports .remainderFirst) []
  have h0 := cleanupOneTraceAt positive H ports labels exit target code 0 base state
  have h1 := cleanupOneTraceAt positive H ports labels exit target code 1 t1 (state.1, none)
  have h2 := cleanupOneTraceAt positive H ports labels exit target code 2 t2 (state.1, none)
  have h3 := cleanupOneTraceAt positive H ports labels exit target code 3 t3 (state.1, none)
  have h4 := cleanupOneTraceAt positive H ports labels exit target code 4 t4 (state.1, none)
  have h5 := cleanupOneTraceAt positive H ports labels exit target code 5 t5 (state.1, none)
  simp [t1, t2, t3, t4, t5, distinct.eq_iff,
    -Function.iterate_succ] at h0 h1 h2 h3 h4 h5
  have finished := join_trace_inline_MachineExpanderRowCleanup (join_trace_inline_MachineExpanderRowCleanup (join_trace_inline_MachineExpanderRowCleanup (join_trace_inline_MachineExpanderRowCleanup (join_trace_inline_MachineExpanderRowCleanup h0 h1) h2) h3) h4) h5
  simpa only [cleanupSteps, cleanupTapes] using finished

/-- The done label transfers control without inspecting or modifying any tape. -/
theorem doneStepAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    TM2.step target ⟨some (labels .done), state, base⟩ = some ⟨exit, state, base⟩ := by
  change some (TM2.stepAux (target (labels .done)) state base) = _
  rw [code]
  cases exit <;> rfl

/-- Cleanup followed by the actual done-to-caller transition. -/
theorem cleanupExitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    (advance (TM2.step target))^[cleanupSteps ports base + 1]
      (some ⟨some (labels (.cleanup 0)), state, base⟩) =
      some ⟨exit, (state.1, none), cleanupTapes ports base⟩ := by
  have cleaned := cleanupTraceAt positive H ports distinct labels exit target code base state
  have done : (advance (TM2.step target))^[1]
      (some ⟨some (labels .done), (state.1, none), cleanupTapes ports base⟩) =
      some ⟨exit, (state.1, none), cleanupTapes ports base⟩ := by
    simpa only [Function.iterate_one, advance_some] using
      doneStepAt positive H ports labels exit target code (cleanupTapes ports base) (state.1, none)
  exact join_trace_inline_MachineExpanderRowCleanup cleaned done

def initializedTapes (ports : Tape → K) (base : K → List Bool) : K → List Bool :=
  Function.update
    (Function.update
      (Function.update
        (Function.update base (ports .quotientFirst) (false :: base (ports .quotientFirst)))
        (ports .quotientSecond) (false :: base (ports .quotientSecond)))
      (ports .remainderFirst) (false :: base (ports .remainderFirst)))
    (ports .remainderSecond) (false :: base (ports .remainderSecond))

/-- Initialization physically pushes four delimiters and resets the bit register. -/
theorem initializeStepAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    TM2.step target ⟨some (labels .initialize), state, base⟩ =
      some ⟨some (labels (.firstEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))),
        (state.1, none), initializedTapes ports base⟩ := by
  change some (TM2.stepAux (target (labels .initialize)) state base) = _
  rw [code]
  simp [statement, TM2.stepAux, initializedTapes, distinct.eq_iff]

def clearedQueryTapes (ports : Tape → K) (base : K → List Bool) : K → List Bool :=
  Function.update
    (Function.update base (ports .queryIndex) (base (ports .queryIndex)).tail)
    (ports .lookupOutput) (base (ports .lookupOutput)).tail

/-- The query-clear phase removes one symbol from each of its two tapes and
preserves the complete finite state and every other tape. -/
theorem clearQueryStepAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    TM2.step target ⟨some (labels .clearQuery), state, base⟩ =
      some ⟨some (labels (.secondEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))),
        state, clearedQueryTapes ports base⟩ := by
  change some (TM2.stepAux (target (labels .clearQuery)) state base) = _
  rw [code]
  simp [statement, TM2.stepAux, clearedQueryTapes, distinct.eq_iff]

end MaxCutGames.Foundations.Complexity.MachineExpanderRow

end OAI
