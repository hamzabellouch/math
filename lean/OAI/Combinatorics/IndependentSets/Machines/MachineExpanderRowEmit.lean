import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineExpanderRowProgram

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.AlphabetTable

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

end IndependentSetsGames.Foundations.Complexity.MachineExpanderRow

end OAI
