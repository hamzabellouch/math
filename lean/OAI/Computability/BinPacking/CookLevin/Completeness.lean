import OAI.Computability.BinPacking.CookLevin.CircuitProducer
import OAI.Computability.BinPacking.CookLevin.TransitionIterationTime

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage

open Turing MachineComposition StatementCircuit CircuitBatch TransitionArena
open ProducerInvariant VerifierCircuit

local instance completenessLabelFintype (V : NPVerifier) :
    Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance completenessStateFintype (V : NPVerifier) :
    Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance completenessAlphabetFintype (V : NPVerifier) :
    ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance completenessLabelDecidableEq (V : NPVerifier) :
    DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance completenessStateDecidableEq (V : NPVerifier) :
    DecidableEq V.computation.tm.σ := Classical.decEq _
local instance completenessAlphabetDecidableEq (V : NPVerifier) :
    ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

theorem loweringSteps_eq_forestSteps (V : NPVerifier) (input : List Bool) {inputs : Nat}
    (frame : Frame inputs (width V input + 1)) :
    loweringSteps V input frame =
      ProducerTime.forestSteps frame (expressions V input) (encodeWords (rootValues frame)) := by
  unfold loweringSteps ProducerTime.forestSteps
  rw [tokens_eq_forest]
  have roots := step_roots frame (expressions V input)
  change rootValues (frame.step (expressions V input)) =
    Batch.roots (next frame) (List.ofFn (expressions V input)) at roots
  rw [roots]
  rfl

theorem verifier_steps_eq (V : NPVerifier) (input : List Bool) :
    steps V input (timeFrame V input (V.horizon input.length)) =
      ProducerTime.acceptanceEmissionSteps V input +
        ProducerTime.acceptanceForestSteps V input := by
  rw [steps, loweringSteps_eq_forestSteps]
  rfl

theorem verifier_steps_le (V : NPVerifier) (input : List Bool) :
    steps V input (timeFrame V input (V.horizon input.length)) ≤
      (ProducerTime.acceptanceEmissionPolynomial V + ProducerTime.loweringPolynomial V).eval
        input.length := by
  rw [verifier_steps_eq, Polynomial.eval_add]
  exact Nat.add_le_add (ProducerTime.acceptanceEmissionSteps_le V input)
    (ProducerTime.acceptanceForestSteps_le V input)

def verifierInPolynomialTime (V : NPVerifier) (input : List Bool)
    (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (machine V).step
      ⟨some (entry V), TermMachine.initialState,
        finishTapes base (capacity V input.length)
          (snapshot (timeFrame V input (V.horizon input.length)))⟩
      (some ⟨none, TermMachine.initialState,
        finishTapes base (capacity V input.length) (snapshot (finalFrame V input))⟩)
      ((ProducerTime.acceptanceEmissionPolynomial V + ProducerTime.loweringPolynomial V).eval
        input.length) where
  steps := steps V input (timeFrame V input (V.horizon input.length))
  evals_in_steps := verifierTrace V input base
  steps_le_m := verifier_steps_le V input

def verifierPlacedInPolynomialTime {CallerTape CallerLabel : Type}
    [DecidableEq CallerTape] (V : NPVerifier) (input : List Bool)
    (ports : Tape ↪ CallerTape) (labels : Label V → CallerLabel) (exit : Option CallerLabel)
    (target : CallerLabel → TM2.Stmt (fun _ : CallerTape => Bool) CallerLabel State)
    (code : ∀ label, target (labels label) =
      ForestPlacement.statement ports labels exit (program V label))
    (ambient : CallerTape → List Bool) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (entry V)), TermMachine.initialState,
        ForestPlacement.fill ports ambient
          (finishTapes base (capacity V input.length)
            (snapshot (timeFrame V input (V.horizon input.length))))⟩
      (some ⟨exit, TermMachine.initialState,
        ForestPlacement.fill ports ambient
          (finishTapes base (capacity V input.length) (snapshot (finalFrame V input)))⟩)
      ((ProducerTime.acceptanceEmissionPolynomial V + ProducerTime.loweringPolynomial V).eval
        input.length) := by
  simpa only [ForestPlacement.configuration, ForestPlacement.placedLabel] using
    ForestPlacement.execution ports labels exit ambient (program V) target code
      (verifierInPolynomialTime V input base)

end BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish

open Turing

variable {σ : Type}

def verifierInitialTapes (V : NPVerifier) (input : List Bool) : Tape → List Bool :=
  let C := VerifierCircuit.circuitOfVerifier V input
  initialTapes C.wires C.inputs C.output.val (recordsBits C.records)

def verifierFinalTapes (V : NPVerifier) (input : List Bool) : Tape → List Bool :=
  memory [] [] [] [] (circuitBits (VerifierCircuit.circuitOfVerifier V input)) [] []

def verifierInPolynomialTime (V : NPVerifier) (input : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .copyOut, (ambient, register), verifierInitialTapes V input⟩
      (some ⟨none, (ambient, none), verifierFinalTapes V input⟩)
      ((ProducerTime.finishPolynomial V).eval input.length) := by
  let run := circuitInTime (VerifierCircuit.circuitOfVerifier V input) ambient register
  exact {
    steps := run.steps
    evals_in_steps := run.evals_in_steps
    steps_le_m := ProducerTime.finishSteps_le V input }

theorem verifierInPolynomialTime_steps (V : NPVerifier) (input : List Bool)
    (ambient : σ) (register : Option Bool) :
    (verifierInPolynomialTime V input ambient register).steps =
      ProducerTime.finishSteps V input := rfl

def verifierPlacedInPolynomialTime {K Λ : Type} [DecidableEq K]
    (ports : Tape ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (base : K → List Bool)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (code : ∀ l, target (labels l) = ForestPlacement.statement ports labels exit (program l))
    (V : NPVerifier) (input : List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels .copyOut), (ambient, register),
        ForestPlacement.fill ports base (verifierInitialTapes V input)⟩
      (some ⟨exit, (ambient, none), ForestPlacement.fill ports base (verifierFinalTapes V input)⟩)
      ((ProducerTime.finishPolynomial V).eval input.length) :=
  ForestPlacement.execution ports labels exit base program target code
    (verifierInPolynomialTime V input ambient register)

theorem verifierFinal_output (V : NPVerifier) (input : List Bool) :
    verifierFinalTapes V input .output =
      circuitBits (VerifierCircuit.circuitOfVerifier V input) := rfl

theorem verifierFinal_clean (V : NPVerifier) (input : List Bool) (tape : Tape)
    (h : tape ≠ .output) : verifierFinalTapes V input tape = [] := by
  cases tape <;> simp_all [verifierFinalTapes, memory]

theorem verifierPlaced_output {K : Type} (ports : Tape ↪ K) (base : K → List Bool)
    (V : NPVerifier) (input : List Bool) :
    ForestPlacement.fill ports base (verifierFinalTapes V input) (ports .output) =
      circuitBits (VerifierCircuit.circuitOfVerifier V input) := by
  rw [ForestPlacement.fill_at, verifierFinal_output]

theorem verifierPlaced_clean {K : Type} (ports : Tape ↪ K) (base : K → List Bool)
    (V : NPVerifier) (input : List Bool) (tape : Tape) (h : tape ≠ .output) :
    ForestPlacement.fill ports base (verifierFinalTapes V input) (ports tape) = [] := by
  rw [ForestPlacement.fill_at, verifierFinal_clean V input tape h]

theorem verifierPlaced_other {K : Type} (ports : Tape ↪ K) (base : K → List Bool)
    (V : NPVerifier) (input : List Bool) (k : K) (outside : ∀ tape, ports tape ≠ k) :
    ForestPlacement.fill ports base (verifierFinalTapes V input) k = base k :=
  ForestPlacement.fill_other ports base _ k outside

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationStage

open Turing MachineComposition StatementCircuit CircuitBatch PostfixModel PostfixAlignment

abbrev Ports (K : Type) := ForestStage.Ports K
abbrev State (σ : Type) := ForestStage.State σ

def freeInputs (V : NPVerifier) (input : List Bool) : Nat :=
  2 * V.witnessBound.eval input.length + 1

def initialGates (V : NPVerifier) (input : List Bool) : List Gate :=
  Batch.gates Fin.val (freeInputs V input)
    (List.ofFn (VerifierCircuit.initialExpressions V input))

def preparedLocal (V : NPVerifier) (input : List Bool) : ForestStage.Tape → List Bool :=
  ForestStage.initialLocal (freeInputs V input)
    (InitializationTemplate.initializationTokens V input) [] []

def snapshotLocal (s : ProducerInvariant.Snapshot) : ForestStage.Tape → List Bool
  | .lower .current => s.currentBits
  | .lower .remaining => encodeWord 0
  | .records => s.reversedRecords
  | .rootTable => s.rootBits
  | _ => []

def finishedLocal (V : NPVerifier) (input : List Bool) : ForestStage.Tape → List Bool :=
  snapshotLocal (ProducerInvariant.snapshot (VerifierCircuit.initialFrame V input))

theorem initialCompile (V : NPVerifier) (input : List Bool) :
    compileTokens (freeInputs V input) []
      (InitializationTemplate.initializationTokens V input) =
      some (ProducerInvariant.next (VerifierCircuit.initialFrame V input),
        (ProducerInvariant.rootValues (VerifierCircuit.initialFrame V input)).reverse,
        initialGates V input) := by
  have h := ProducerInvariant.compile_frameForest
    (Frame.initial (id : Fin (freeInputs V input) → Fin (freeInputs V input)))
    (VerifierCircuit.initialExpressions V input)
  simpa [InitializationTemplate.initializationTokens_eq, freeInputs, initialGates,
    ProducerInvariant.next, Frame.initial, Fragment.empty,
    VerifierCircuit.initialFrame] using h

theorem initialRecords (V : NPVerifier) (input : List Bool) :
    ProducerInvariant.recordBits (VerifierCircuit.initialFrame V input) =
      recordsBits (gateRecords (freeInputs V input) (initialGates V input)) := by
  change ProducerInvariant.recordBits
    ((Frame.initial (id : Fin (freeInputs V input) → Fin (freeInputs V input))).step
      (VerifierCircuit.initialExpressions V input)) = _
  erw [ProducerInvariant.recordBits_step]
  simp [ProducerInvariant.recordBits, ProducerInvariant.next, Frame.initial,
    Fragment.empty, gateRecords, recordsBits, recordsWords, encodeWords,
    freeInputs, initialGates]

theorem finalLocal_eq (V : NPVerifier) (input : List Bool) :
    ForestStage.finalLocal
      (ProducerInvariant.next (VerifierCircuit.initialFrame V input))
      (ProducerInvariant.rootValues (VerifierCircuit.initialFrame V input)).reverse
      (recordsBits (gateRecords (freeInputs V input) (initialGates V input))) [] =
      finishedLocal V input := by
  rw [← initialRecords]
  funext tape
  cases tape with
  | lower tape => cases tape <;>
      simp [ForestStage.finalLocal, finishedLocal, snapshotLocal,
        ProducerInvariant.next, ProducerInvariant.snapshot,
        ProducerInvariant.Snapshot.currentBits]
  | tokens => rfl
  | records => simp [ForestStage.finalLocal, finishedLocal, snapshotLocal,
      ProducerInvariant.snapshot, ProducerInvariant.recordBits]
  | rootTable => simp [ForestStage.finalLocal, finishedLocal, snapshotLocal,
      ProducerInvariant.snapshot, ProducerInvariant.rootValues,
      ProducerInvariant.Snapshot.rootBits]

def lowerSteps (V : NPVerifier) (input : List Bool) : Nat :=
  ForestStage.steps (InitializationTemplate.initializationTokens V input)
    (freeInputs V input)
    (ProducerInvariant.rootValues (VerifierCircuit.initialFrame V input)).reverse
    (initialGates V input) []

variable {K Λ σ : Type} [DecidableEq K]

def Ready (p : Ports K) (base : K → List Bool) (V : NPVerifier)
    (input : List Bool) : Prop :=
  ∀ t, base (p t) = ForestStage.initialLocal (freeInputs V input) [] [] [] t

def Prepared (p : Ports K) (base : K → List Bool) (V : NPVerifier)
    (input : List Bool) : Prop :=
  ∀ t, base (p t) = preparedLocal V input t

def result (p : Ports K) (base : K → List Bool) (V : NPVerifier)
    (input : List Bool) : K → List Bool :=
  ForestPlacement.fill p base (finishedLocal V input)

theorem prepared_emitted (p : Ports K) (base : K → List Bool) (V : NPVerifier)
    (input : List Bool) (ready : Ready p base V input) :
    Prepared p
      (ClashMachine.emitted (p .tokens) (p (.lower .remaining)) base
        (InitializationTemplate.initializationTokens V input)) V input := by
  dsimp only [Ready] at ready
  intro t
  cases t with
  | lower t => cases t <;>
      simp [ClashMachine.emitted, p.injective.eq_iff, ready, preparedLocal,
        ForestStage.initialLocal, encodeWord]
  | tokens => simp [ClashMachine.emitted, p.injective.eq_iff, ready,
      preparedLocal, ForestStage.initialLocal, tokenBits, tokenWords, encodeWords]
  | records => simp [ClashMachine.emitted, p.injective.eq_iff, ready,
      preparedLocal, ForestStage.initialLocal]
  | rootTable => simp [ClashMachine.emitted, p.injective.eq_iff, ready,
      preparedLocal, ForestStage.initialLocal]

theorem result_emitted (p : Ports K) (base : K → List Bool) (V : NPVerifier)
    (input : List Bool) (tokens : List Token) :
    result p (ClashMachine.emitted (p .tokens) (p (.lower .remaining)) base tokens)
        V input = result p base V input := by
  classical
  funext k
  by_cases inside : ∃ t, p t = k
  · obtain ⟨t, rfl⟩ := inside
    simp only [result, ForestPlacement.fill_at]
  · have outside : ∀ t, p t ≠ k := not_exists.mp inside
    rw [result, ForestPlacement.fill_other p _ _ k outside,
      result, ForestPlacement.fill_other p _ _ k outside]
    exact ClashMachine.emitted_other (p .tokens) (p (.lower .remaining)) k
      (Ne.symm (outside .tokens)) (Ne.symm (outside (.lower .remaining))) base tokens

theorem lowerTrace (p : Ports K) (labels : ForestStage.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (code : ∀ l, program (labels l) = ForestStage.statement p labels exit l)
    (base : K → List Bool) (V : NPVerifier) (input : List Bool)
    (ready : Prepared p base V input) (ambient : σ × Bool) :
    (advance (TM2.step program))^[lowerSteps V input]
      (some ⟨some (labels .reverseTokens), (ambient, none), base⟩) =
      some ⟨exit, (ambient, none), result p base V input⟩ := by
  have h := ForestStage.traceAt p labels exit program code base ambient
    (InitializationTemplate.initializationTokens V input) (freeInputs V input)
    (ProducerInvariant.next (VerifierCircuit.initialFrame V input))
    (ProducerInvariant.rootValues (VerifierCircuit.initialFrame V input)).reverse
    (initialGates V input) [] [] (initialCompile V input)
  have hprepared : ForestPlacement.fill p base (preparedLocal V input) = base := by
    rw [show preparedLocal V input = (fun t => base (p t)) from funext fun t => (ready t).symm]
    exact ForestPlacement.fill_self p base
  rw [finalLocal_eq] at h
  change (advance (TM2.step program))^[lowerSteps V input]
    (some ⟨some (labels .reverseTokens), (ambient, none),
      ForestPlacement.fill p base (preparedLocal V input)⟩) =
    some ⟨exit, (ambient, none), result p base V input⟩ at h
  simpa only [hprepared] using h

omit [DecidableEq K] in
theorem result_at (p : Ports K) (base : K → List Bool) (V : NPVerifier)
    (input : List Bool) (t : ForestStage.Tape) :
    result p base V input (p t) = finishedLocal V input t :=
  ForestPlacement.fill_at p base _ t

omit [DecidableEq K] in
theorem result_other (p : Ports K) (base : K → List Bool) (V : NPVerifier)
    (input : List Bool) (k : K) (outside : ∀ t, p t ≠ k) :
    result p base V input k = base k :=
  ForestPlacement.fill_other p base _ k outside

def lowerTimePolynomial (V : NPVerifier) : Polynomial Nat :=
  ForestStage.timePolynomial.comp
    (ProducerInvariant.budgetPolynomial V + ProducerInvariant.tapePolynomial V + 1)

theorem lowerSteps_le (V : NPVerifier) (input : List Bool) :
    lowerSteps V input ≤ (lowerTimePolynomial V).eval input.length := by
  have roots := ProducerInvariant.step_roots
    (Frame.initial (id : Fin (freeInputs V input) → Fin (freeInputs V input)))
    (VerifierCircuit.initialExpressions V input)
  have h := ForestStage.forest_steps_le Fin.val
    (List.ofFn (VerifierCircuit.initialExpressions V input)) (freeInputs V input) []
    (fun i => i.isLt)
  have rootEq : ProducerInvariant.rootValues (VerifierCircuit.initialFrame V input) =
      Batch.roots (freeInputs V input)
        (List.ofFn (VerifierCircuit.initialExpressions V input)) := by
    simpa [ProducerInvariant.snapshot, ProducerInvariant.rootValues,
      VerifierCircuit.initialFrame, Frame.initial, Fragment.empty, freeInputs] using roots
  have hsteps : lowerSteps V input ≤ ForestStage.timePolynomial.eval
      (freeInputs V input + Batch.cost (List.ofFn (VerifierCircuit.initialExpressions V input)) +
        (tokenBits (InitializationTemplate.initializationTokens V input)).length + 1) := by
    simpa only [lowerSteps, InitializationTemplate.initializationTokens_eq, rootEq,
      initialGates, List.length_nil, Nat.add_zero] using h
  have hg := VerifierCircuit.circuitOfVerifier_gates_le_polynomial V input
  rw [VerifierCircuit.circuitOfVerifier_gate_count] at hg
  have hb := ProducerInvariant.budgetPolynomial_eval V input
  have ht := ProducerInvariant.initial_tokens_length_le V input
  rw [← InitializationTemplate.initializationTokens_eq] at ht
  have sizeBound : freeInputs V input +
      Batch.cost (List.ofFn (VerifierCircuit.initialExpressions V input)) +
      (tokenBits (InitializationTemplate.initializationTokens V input)).length + 1 ≤
      (ProducerInvariant.budgetPolynomial V + ProducerInvariant.tapePolynomial V + 1).eval
        input.length := by
    simp only [Polynomial.eval_add, Polynomial.eval_one]
    dsimp only [freeInputs]
    omega
  exact hsteps.trans (by
    rw [lowerTimePolynomial, Polynomial.eval_comp]
    exact natPolynomial_eval_mono ForestStage.timePolynomial sizeBound)

def lowerInTime (p : Ports K) (labels : ForestStage.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (code : ∀ l, program (labels l) = ForestStage.statement p labels exit l)
    (base : K → List Bool) (V : NPVerifier) (input : List Bool)
    (ready : Prepared p base V input) (ambient : σ × Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .reverseTokens), (ambient, none), base⟩
      (some ⟨exit, (ambient, none), result p base V input⟩)
      ((lowerTimePolynomial V).eval input.length) where
  steps := lowerSteps V input
  evals_in_steps := lowerTrace p labels exit program code base V input ready ambient
  steps_le_m := lowerSteps_le V input

structure FullPorts (K : Type) where
  emit : InitializationAssembly.Tape 9 ↪ K
  lower : ForestStage.Ports K
  output_shared : emit .reversed = lower .tokens
  count_shared : emit .count = lower (.lower .remaining)

abbrev Label (V : NPVerifier) := InitializationAssembly.Label V ⊕ ForestStage.Label

def entry (V : NPVerifier) : Label V := .inl .control

def emitLabels {V : NPVerifier} (labels : Label V ↪ Λ) :
    InitializationAssembly.Label V ↪ Λ :=
  ⟨fun l => labels (.inl l), fun _ _ h => Sum.inl.inj (labels.injective h)⟩

def statement (V : NPVerifier) (p : FullPorts K) (labels : Label V ↪ Λ)
    (exit : Option Λ) : Label V → TM2.Stmt (fun _ : K => Bool) Λ (State σ)
  | .inl l => InitializationAssembly.statement V p.emit (emitLabels labels)
      (some (labels (.inr .reverseTokens))) l
  | .inr l => ForestStage.statement p.lower (fun l => labels (.inr l)) exit l

def Agrees (V : NPVerifier) (p : FullPorts K) (labels : Label V ↪ Λ)
    (exit : Option Λ) (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ)) : Prop :=
  ∀ l, program (labels l) = statement V p labels exit l

structure FullReady (V : NPVerifier) (p : FullPorts K) (base : K → List Bool)
    (input : List Bool) : Prop where
  emitter : InitializationAssembly.Ready V p.emit base input
  lowerer : Ready p.lower base V input

def steps (V : NPVerifier) (input : List Bool) : Nat :=
  InitializationAssembly.steps V input + lowerSteps V input

theorem trace (V : NPVerifier) (p : FullPorts K) (labels : Label V ↪ Λ)
    (exit : Option Λ) (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (ha : Agrees V p labels exit program) (base : K → List Bool) (input : List Bool)
    (ready : FullReady V p base input) (ambient : σ) :
    (advance (TM2.step program))^[steps V input]
      (some ⟨some (labels (entry V)), ClashMachine.clean ambient, base⟩) =
      some ⟨exit, ClashMachine.clean ambient, result p.lower base V input⟩ := by
  have first := InitializationAssembly.trace V p.emit (emitLabels labels)
    (some (labels (.inr .reverseTokens))) program (fun l => ha (.inl l))
    base input ready.emitter ambient
  rw [p.output_shared, p.count_shared] at first
  have second := lowerTrace p.lower (fun l => labels (.inr l)) exit program
    (fun l => ha (.inr l))
    (ClashMachine.emitted (p.lower .tokens) (p.lower (.lower .remaining)) base
      (InitializationTemplate.initializationTokens V input)) V input
    (prepared_emitted p.lower base V input ready.lowerer) (ambient, false)
  rw [result_emitted] at second
  exact ClashMachine.chain first second

def program (V : NPVerifier) (p : FullPorts K) :
    Label V → TM2.Stmt (fun _ : K => Bool) (Label V) (State Unit) :=
  statement V p (Function.Embedding.refl _) none

def machine (V : NPVerifier) [Fintype K] (p : FullPorts K) : FinTM2 where
  K := K
  k₀ := p.emit .rawInput
  k₁ := p.lower .records
  Γ := fun _ => Bool
  Λ := Label V
  main := entry V
  σ := State Unit
  initialState := ClashMachine.clean ()
  Γk₀Fin := inferInstance
  m := program V p

theorem machineTrace (V : NPVerifier) [Fintype K] (p : FullPorts K)
    (base : K → List Bool) (input : List Bool) (ready : FullReady V p base input) :
    (advance (machine V p).step)^[steps V input]
      (some ⟨some (entry V), ClashMachine.clean (), base⟩) =
      some ⟨none, ClashMachine.clean (), result p.lower base V input⟩ :=
  trace V p (Function.Embedding.refl _) none (program V p) (fun _ => rfl)
    base input ready ()

def timePolynomial (V : NPVerifier) : Polynomial Nat :=
  InitializationAssembly.timePolynomial V + lowerTimePolynomial V

theorem steps_le_timePolynomial (V : NPVerifier) (input : List Bool) :
    steps V input ≤ (timePolynomial V).eval input.length := by
  simpa only [steps, timePolynomial, Polynomial.eval_add] using
    Nat.add_le_add (InitializationAssembly.steps_le_timePolynomial V input)
      (lowerSteps_le V input)

def verifierPlacedInPolynomialTime (V : NPVerifier) (p : FullPorts K)
    (labels : Label V ↪ Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (ha : Agrees V p labels exit program) (base : K → List Bool) (input : List Bool)
    (ready : FullReady V p base input) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (entry V)), ClashMachine.clean ambient, base⟩
      (some ⟨exit, ClashMachine.clean ambient, result p.lower base V input⟩)
      ((timePolynomial V).eval input.length) where
  steps := steps V input
  evals_in_steps := trace V p labels exit program ha base input ready ambient
  steps_le_m := steps_le_timePolynomial V input

def verifierInPolynomialTime (V : NPVerifier) [Fintype K] (p : FullPorts K)
    (base : K → List Bool) (input : List Bool) (ready : FullReady V p base input) :
    StateTransition.EvalsToInTime (machine V p).step
      ⟨some (entry V), ClashMachine.clean (), base⟩
      (some ⟨none, ClashMachine.clean (), result p.lower base V input⟩)
      ((timePolynomial V).eval input.length) :=
  verifierPlacedInPolynomialTime V p (Function.Embedding.refl _) none
    (program V p) (fun _ => rfl) base input ready ()

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationStage

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerHandoffs

open ProducerInvariant ProducerArena

def localBase (V : NPVerifier) (input : List Bool) : TransitionArena.Tape → List Bool :=
  fun t => bootstrapPrepared V input (transitionPorts V t)

def boundary (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot) : Tape V → List Bool :=
  ForestPlacement.fill (transitionPorts V) (bootstrapPrepared V input)
    (TransitionArena.tapes (localBase V input) (VerifierCircuit.capacity V input.length) remaining s)

def finished (V : NPVerifier) (input : List Bool) (s : Snapshot) : Tape V → List Bool :=
  ForestPlacement.fill (transitionPorts V) (bootstrapPrepared V input)
    (TransitionArena.finishTapes (localBase V input) (VerifierCircuit.capacity V input.length) s)

theorem fill_fill {I K : Type} (ports : I ↪ K) (base : K → List Bool)
    (first second : I → List Bool) :
    ForestPlacement.fill ports (ForestPlacement.fill ports base first) second =
      ForestPlacement.fill ports base second := by
  classical
  funext k
  by_cases hin : ∃ i, ports i = k
  · obtain ⟨i, rfl⟩ := hin
    simp only [ForestPlacement.fill_at]
  · rw [ForestPlacement.fill_other ports _ _ k (not_exists.mp hin),
      ForestPlacement.fill_other ports _ _ k (not_exists.mp hin),
      ForestPlacement.fill_other ports _ _ k (not_exists.mp hin)]

theorem boundary_view (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot) :
    (fun t => boundary V input remaining s (transitionPorts V t)) =
      TransitionArena.tapes (localBase V input) (VerifierCircuit.capacity V input.length) remaining s := by
  funext t
  exact ForestPlacement.fill_at _ _ _ t

theorem finished_view (V : NPVerifier) (input : List Bool) (s : Snapshot) :
    (fun t => finished V input s (transitionPorts V t)) =
      TransitionArena.finishTapes (localBase V input) (VerifierCircuit.capacity V input.length) s := by
  funext t
  exact ForestPlacement.fill_at _ _ _ t

theorem boundary_other (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot)
    (k : Tape V) (outside : ∀ t, transitionPorts V t ≠ k) :
    boundary V input remaining s k = bootstrapPrepared V input k :=
  ForestPlacement.fill_other _ _ _ k outside

theorem finished_other (V : NPVerifier) (input : List Bool) (s : Snapshot)
    (k : Tape V) (outside : ∀ t, transitionPorts V t ≠ k) :
    finished V input s k = bootstrapPrepared V input k :=
  ForestPlacement.fill_other _ _ _ k outside

theorem fill_boundary (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot)
    (contents : TransitionArena.Tape → List Bool) :
    ForestPlacement.fill (transitionPorts V) (boundary V input remaining s) contents =
      ForestPlacement.fill (transitionPorts V) (bootstrapPrepared V input) contents :=
  fill_fill _ _ _ _

theorem fill_finished (V : NPVerifier) (input : List Bool) (s : Snapshot)
    (contents : TransitionArena.Tape → List Bool) :
    ForestPlacement.fill (transitionPorts V) (finished V input s) contents =
      ForestPlacement.fill (transitionPorts V) (bootstrapPrepared V input) contents :=
  fill_fill _ _ _ _

theorem iteration_handoff (V : NPVerifier) (input : List Bool) (remaining : Nat) (s next : Snapshot) :
    ForestPlacement.fill (transitionPorts V) (boundary V input remaining s)
      (TransitionArena.finishTapes (localBase V input) (VerifierCircuit.capacity V input.length) next) =
      finished V input next := fill_boundary V input remaining s _

theorem acceptance_handoff (V : NPVerifier) (input : List Bool) (s next : Snapshot) :
    ForestPlacement.fill (transitionPorts V) (finished V input s)
      (TransitionArena.finishTapes (localBase V input) (VerifierCircuit.capacity V input.length) next) =
      finished V input next := fill_finished V input s _

@[simp] theorem boundary_current (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot) :
    boundary V input remaining s (current V) = s.currentBits := by
  change ForestPlacement.fill (transitionPorts V) _ _
    (transitionPorts V (.inl (.lower .current))) = _
  rw [ForestPlacement.fill_at]
  rfl

@[simp] theorem boundary_roots (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot) :
    boundary V input remaining s (roots V) = s.rootBits := by
  change ForestPlacement.fill (transitionPorts V) _ _ (transitionPorts V (.inl .rootTable)) = _
  rw [ForestPlacement.fill_at]
  rfl

@[simp] theorem boundary_records (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot) :
    boundary V input remaining s (records V) = s.reversedRecords := by
  change ForestPlacement.fill (transitionPorts V) _ _ (transitionPorts V (.inl .records)) = _
  rw [ForestPlacement.fill_at]
  rfl

@[simp] theorem boundary_countdown (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot) :
    boundary V input remaining s (countdown V) = encodeWord remaining := by
  change ForestPlacement.fill (transitionPorts V) _ _ (transitionPorts V (.inr .countdown)) = _
  rw [ForestPlacement.fill_at]
  rfl

@[simp] theorem finished_current (V : NPVerifier) (input : List Bool) (s : Snapshot) :
    finished V input s (current V) = s.currentBits := by
  change ForestPlacement.fill (transitionPorts V) _ _
    (transitionPorts V (.inl (.lower .current))) = _
  rw [ForestPlacement.fill_at]
  rfl

@[simp] theorem finished_roots (V : NPVerifier) (input : List Bool) (s : Snapshot) :
    finished V input s (roots V) = s.rootBits := by
  change ForestPlacement.fill (transitionPorts V) _ _ (transitionPorts V (.inl .rootTable)) = _
  rw [ForestPlacement.fill_at]
  rfl

@[simp] theorem finished_records (V : NPVerifier) (input : List Bool) (s : Snapshot) :
    finished V input s (records V) = s.reversedRecords := by
  change ForestPlacement.fill (transitionPorts V) _ _ (transitionPorts V (.inl .records)) = _
  rw [ForestPlacement.fill_at]
  rfl

@[simp] theorem finished_countdown (V : NPVerifier) (input : List Bool) (s : Snapshot) :
    finished V input s (countdown V) = [] := by
  change ForestPlacement.fill (transitionPorts V) _ _ (transitionPorts V (.inr .countdown)) = _
  rw [ForestPlacement.fill_at]
  simp [TransitionArena.finishTapes]

theorem boundary_private (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot)
    (w : Work) (outside : ∀ t, transitionPorts V t ≠ .inr w) :
    boundary V input remaining s (.inr w) = [] := by
  rw [boundary_other V input remaining s _ outside,
    bootstrapPrepared_other V input _
      (Ne.symm (outside (.inl (.lower .current))))
      (Ne.symm (outside (.inl (.lower .remaining))))
      (Ne.symm (outside (.inr .cursor)))]
  rfl

theorem finished_private (V : NPVerifier) (input : List Bool) (s : Snapshot)
    (w : Work) (outside : ∀ t, transitionPorts V t ≠ .inr w) :
    finished V input s (.inr w) = [] := by
  rw [finished_other V input s _ outside,
    bootstrapPrepared_other V input _
      (Ne.symm (outside (.inl (.lower .current))))
      (Ne.symm (outside (.inl (.lower .remaining))))
      (Ne.symm (outside (.inr .cursor)))]
  rfl

theorem private_finish_outside (V : NPVerifier) (f : CircuitFinish.Tape) :
    ∀ t, transitionPorts V t ≠ .inr (.finish f) := by
  intro t
  cases t with
  | inl t => simp [transitionTape]
  | inr t => cases t <;> simp [transitionTape, raw, q, capacity, countdown, clock]

theorem private_validity_outside (V : NPVerifier) (j : Fin 7) :
    ∀ t, transitionPorts V t ≠ .inr (.validity j) := by
  intro t
  cases t with
  | inl t => simp [transitionTape]
  | inr t => cases t <;> simp [transitionTape, raw, q, capacity, countdown, clock]

theorem private_cells_outside (V : NPVerifier) (j : Fin 9) :
    ∀ t, transitionPorts V t ≠ .inr (.cells j) := by
  intro t
  cases t with
  | inl t => simp [transitionTape]
  | inr t => cases t <;> simp [transitionTape, raw, q, capacity, countdown, clock]

theorem bootstrap_clock (V : NPVerifier) (input : List Bool) (c : ClockPreparation.Clock) :
    bootstrapPrepared V input (clock V c) = encodeWord (ClockPreparation.clockValue V input.length c) := by
  change bootstrapPrepared V input (frontPorts V (VerifierFront.clockTape V c)) = _
  rw [bootstrapPrepared_front]
  exact VerifierFront.prepared_clock V input c

theorem bootstrap_raw (V : NPVerifier) (input : List Bool) :
    bootstrapPrepared V input (raw V) = input := by
  change bootstrapPrepared V input (frontPorts V (VerifierFront.raw V)) = _
  rw [bootstrapPrepared_front]
  exact VerifierFront.prepared_raw V input

theorem bootstrap_work (V : NPVerifier) (input : List Bool) (w : Work)
    (hc : (.inr w : Tape V) ≠ current V) (hn : (.inr w : Tape V) ≠ count V)
    (hz : (.inr w : Tape V) ≠ cursor V) : bootstrapPrepared V input (.inr w) = [] := by
  rw [bootstrapPrepared_other V input _ hc hn hz]
  rfl

theorem bootstrap_extra (V : NPVerifier) (input : List Bool) (s : Snapshot)
    (e : TransitionArena.Extra) :
    localBase V input (.inr e) =
      TransitionArena.tapes (localBase V input) (VerifierCircuit.capacity V input.length)
        (V.horizon input.length) s (.inr e) := by
  cases e <;> simp only [TransitionArena.tapes]
  all_goals first
    | rfl
    | exact bootstrapPrepared_cursor V input
    | exact bootstrap_clock V input .capacity
    | exact bootstrap_clock V input .horizon

@[simp] theorem boundary_raw (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot) :
    boundary V input remaining s (raw V) = input := by
  change ForestPlacement.fill (transitionPorts V) _ _ (transitionPorts V (.inr .raw)) = _
  rw [ForestPlacement.fill_at]
  exact bootstrap_raw V input

@[simp] theorem boundary_q (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot) :
    boundary V input remaining s (q V) = encodeWord (V.witnessBound.eval input.length) := by
  change ForestPlacement.fill (transitionPorts V) _ _ (transitionPorts V (.inr .q)) = _
  rw [ForestPlacement.fill_at]
  exact bootstrap_clock V input .witness

@[simp] theorem boundary_capacity (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot) :
    boundary V input remaining s (capacity V) = encodeWord (VerifierCircuit.capacity V input.length) := by
  change ForestPlacement.fill (transitionPorts V) _ _ (transitionPorts V (.inr .capacity)) = _
  rw [ForestPlacement.fill_at]
  rfl

theorem initial_result_view (V : NPVerifier) (input : List Bool) :
    (fun t => InitializationStage.result (forestPorts V) (bootstrapPrepared V input) V input
      (transitionPorts V t)) =
      TransitionArena.tapes (localBase V input) (VerifierCircuit.capacity V input.length)
        (V.horizon input.length) (snapshot (VerifierCircuit.initialFrame V input)) := by
  funext t
  cases t with
  | inl t =>
    change InitializationStage.result (forestPorts V) _ V input (forestPorts V t) = _
    rw [InitializationStage.result_at]
    cases t with
    | lower t => cases t <;> rfl
    | tokens => rfl
    | records => rfl
    | rootTable => rfl
  | inr e =>
    have outside : ∀ t, forestPorts V t ≠ transitionPorts V (.inr e) := by
      intro t h
      change transitionPorts V (.inl t) = transitionPorts V (.inr e) at h
      have impossible := (transitionPorts V).injective h
      cases impossible
    rw [InitializationStage.result_other _ _ _ _ _ outside]
    exact bootstrap_extra V input _ e

theorem initial_result_eq_boundary (V : NPVerifier) (input : List Bool) :
    InitializationStage.result (forestPorts V) (bootstrapPrepared V input) V input =
      boundary V input (V.horizon input.length) (snapshot (VerifierCircuit.initialFrame V input)) := by
  classical
  funext k
  by_cases inside : ∃ t, transitionPorts V t = k
  · obtain ⟨t, rfl⟩ := inside
    exact (congrFun (initial_result_view V input) t).trans
      (congrFun (boundary_view V input _ _) t).symm
  · have outside := not_exists.mp inside
    have outsideForest : ∀ t, forestPorts V t ≠ k := fun t => outside (.inl t)
    rw [InitializationStage.result_other _ _ _ _ _ outsideForest,
      boundary_other V input _ _ _ outside]

theorem initialization_emitted_fill (V : NPVerifier) (input : List Bool) :
    ForestPlacement.fill (initializationPorts V) (bootstrapPrepared V input)
      (ClashMachine.emitted InitializationAssembly.Tape.reversed InitializationAssembly.Tape.count
        (initializationBase V input) (InitializationTemplate.initializationTokens V input)) =
      ClashMachine.emitted (tokens V) (count V) (bootstrapPrepared V input)
        (InitializationTemplate.initializationTokens V input) := by
  rw [← bootstrap_initialization_view V input]
  simp only [ClashMachine.emitted, ForestPlacement.fill_update, ForestPlacement.fill_self]
  rfl

theorem initialization_lowering_handoff (V : NPVerifier) (input : List Bool) :
    InitializationStage.result (forestPorts V)
      (ForestPlacement.fill (initializationPorts V) (bootstrapPrepared V input)
        (ClashMachine.emitted InitializationAssembly.Tape.reversed InitializationAssembly.Tape.count
          (initializationBase V input) (InitializationTemplate.initializationTokens V input))) V input =
      boundary V input (V.horizon input.length) (snapshot (VerifierCircuit.initialFrame V input)) := by
  rw [initialization_emitted_fill]
  change InitializationStage.result (forestPorts V)
    (ClashMachine.emitted (forestPorts V .tokens) (forestPorts V (.lower .remaining))
      (bootstrapPrepared V input) (InitializationTemplate.initializationTokens V input)) V input = _
  rw [InitializationStage.result_emitted, initial_result_eq_boundary]

theorem clock_outside (V : NPVerifier) (c : ClockPreparation.Clock)
    (hq : c ≠ .witness) (hS : c ≠ .capacity) (hT : c ≠ .horizon) :
    ∀ t, transitionPorts V t ≠ clock V c := by
  intro t
  cases t with
  | inl t => simp [transitionTape, clock]
  | inr e =>
    cases e with
    | q => change clock V .witness ≠ clock V c; simpa only [ne_eq, clock_eq_iff] using Ne.symm hq
    | capacity => change clock V .capacity ≠ clock V c; simpa only [ne_eq, clock_eq_iff] using Ne.symm hS
    | countdown => change clock V .horizon ≠ clock V c; simpa only [ne_eq, clock_eq_iff] using Ne.symm hT
    | raw => exact raw_ne_clock V c
    | cursor | position | address | value | scratch | copy | saveLeft | saveRight =>
      simp [transitionTape, clock]

theorem freeInputs_outside (V : NPVerifier) : ∀ t, transitionPorts V t ≠ freeInputs V :=
  clock_outside V .inputCount (by decide) (by decide) (by decide)

theorem framed_outside (V : NPVerifier) : ∀ t, transitionPorts V t ≠ framed V := by
  intro t
  cases t with
  | inl t => simp [transitionTape, framed]
  | inr e =>
    cases e with
    | q => exact clock_ne_framed V .witness
    | capacity => exact clock_ne_framed V .capacity
    | countdown => exact clock_ne_framed V .horizon
    | raw => exact raw_ne_framed V
    | cursor | position | address | value | scratch | copy | saveLeft | saveRight =>
      simp [transitionTape, framed]

theorem boundary_clock (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot)
    (c : ClockPreparation.Clock) (hq : c ≠ .witness) (hS : c ≠ .capacity) (hT : c ≠ .horizon) :
    boundary V input remaining s (clock V c) = encodeWord (ClockPreparation.clockValue V input.length c) := by
  rw [boundary_other V input remaining s _ (clock_outside V c hq hS hT)]
  exact bootstrap_clock V input c

theorem finished_clock (V : NPVerifier) (input : List Bool) (s : Snapshot)
    (c : ClockPreparation.Clock) (hq : c ≠ .witness) (hS : c ≠ .capacity) (hT : c ≠ .horizon) :
    finished V input s (clock V c) = encodeWord (ClockPreparation.clockValue V input.length c) := by
  rw [finished_other V input s _ (clock_outside V c hq hS hT)]
  exact bootstrap_clock V input c

theorem boundary_framed (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot) :
    boundary V input remaining s (framed V) = encodeWord input.length ++ input := by
  rw [boundary_other V input remaining s _ (framed_outside V)]
  change bootstrapPrepared V input (frontPorts V (VerifierFront.stream V)) = _
  rw [bootstrapPrepared_front]
  exact VerifierFront.prepared_stream V input

theorem finished_framed (V : NPVerifier) (input : List Bool) (s : Snapshot) :
    finished V input s (framed V) = encodeWord input.length ++ input := by
  rw [finished_other V input s _ (framed_outside V)]
  change bootstrapPrepared V input (frontPorts V (VerifierFront.stream V)) = _
  rw [bootstrapPrepared_front]
  exact VerifierFront.prepared_stream V input

@[simp] theorem finished_freeInputs (V : NPVerifier) (input : List Bool) (s : Snapshot) :
    finished V input s (freeInputs V) = encodeWord (2 * V.witnessBound.eval input.length + 1) := by
  rw [finished_other V input s _ (freeInputs_outside V)]
  exact bootstrap_clock V input .inputCount

theorem finish_view (V : NPVerifier) (input : List Bool) (s : Snapshot) :
    (fun t => finished V input s (finishPorts V t)) =
      CircuitFinish.memory s.currentBits
        (encodeWord (2 * V.witnessBound.eval input.length + 1)) s.rootBits s.reversedRecords [] [] [] := by
  funext t
  cases t with
  | current => exact finished_current V input s
  | freeInputs => exact finished_freeInputs V input s
  | root => exact finished_roots V input s
  | reversedRecords => exact finished_records V input s
  | output => exact finished_private V input s _ (private_finish_outside V .output)
  | gateCount => exact finished_private V input s _ (private_finish_outside V .gateCount)
  | scratch => exact finished_private V input s _ (private_finish_outside V .scratch)

theorem circuitFinish_view (V : NPVerifier) (input : List Bool) :
    (fun t => finished V input (snapshot (finalFrame V input)) (finishPorts V t)) =
      CircuitFinish.initialTapes (VerifierCircuit.circuitOfVerifier V input).wires
        (VerifierCircuit.circuitOfVerifier V input).inputs
        (VerifierCircuit.circuitOfVerifier V input).output.val
        (recordsBits (VerifierCircuit.circuitOfVerifier V input).records) := by
  rw [finish_view]
  rw [← finalFrame_circuit V input]
  simp [CircuitFinish.initialTapes, snapshot, Snapshot.currentBits, Snapshot.rootBits,
    CircuitBatch.Frame.toCircuit, CircuitBatch.Fragment.toCircuit, Circuit.wires,
    List.ofFn_succ, Circuit.records, encodeWords]

theorem bootstrap_emitter_ready (V : NPVerifier) (input : List Bool) :
    InitializationAssembly.Ready V (initializationPorts V)
      (bootstrapPrepared V input) input := by
  constructor
  · exact congrFun (bootstrap_initialization_view V input) .rawInput
  · exact congrFun (bootstrap_initialization_view V input) .framedInput
  · exact congrFun (bootstrap_initialization_view V input) .witnessBound
  · exact congrFun (bootstrap_initialization_view V input) .capacity
  · intro j
    exact congrFun (bootstrap_initialization_view V input) (.cellWork j)
  · intro j
    exact congrFun (bootstrap_initialization_view V input) (.validityWork j)

theorem bootstrap_lowerer_ready (V : NPVerifier) (input : List Bool) :
    InitializationStage.Ready (forestPorts V) (bootstrapPrepared V input) V input := by
  intro t
  cases t with
  | lower t =>
    cases t <;> simp only [ForestStage.initialLocal]
    all_goals first
      | exact bootstrapPrepared_current V input
      | exact bootstrapPrepared_count V input
      | apply bootstrap_work <;> simp [current, count, cursor, shared, TransitionArena.forestPorts]
  | tokens =>
    apply bootstrap_work <;> simp [current, count, cursor, shared, TransitionArena.forestPorts]
  | records =>
    apply bootstrap_work <;> simp [current, count, cursor, shared, TransitionArena.forestPorts]
  | rootTable =>
    apply bootstrap_work <;> simp [current, count, cursor, shared, TransitionArena.forestPorts]

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerHandoffs

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerTailStage

open Turing ProducerArena ProducerInvariant ProducerHandoffs

local instance completenessLabelFintype (V : NPVerifier) :
    Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance completenessStateFintype (V : NPVerifier) :
    Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance completenessAlphabetFintype (V : NPVerifier) :
    ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance completenessLabelDecidableEq (V : NPVerifier) :
    DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance completenessStateDecidableEq (V : NPVerifier) :
    DecidableEq V.computation.tm.σ := Classical.decEq _
local instance completenessAlphabetDecidableEq (V : NPVerifier) :
    ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

abbrev IterateLabel (V : NPVerifier) :=
  TransitionIteration.Label (VerifierCircuit.indexing V) V.computation.tm.m
abbrev Label (V : NPVerifier) :=
  IterateLabel V ⊕ (AcceptanceStage.Label V ⊕ CircuitFinish.Label)

def entry (V : NPVerifier) : Label V :=
  .inl (TransitionIteration.entry (VerifierCircuit.indexing V) V.computation.tm.m)

def statement {Λ : Type} (V : NPVerifier) (labels : Label V → Λ) (exit : Option Λ) :
    Label V → TM2.Stmt (Alphabet V) Λ State
  | .inl l => ForestPlacement.statement (transitionPorts V)
      (fun l => labels (.inl l)) (some (labels (.inr (.inl (AcceptanceStage.entry V)))))
      (TransitionIteration.program (VerifierCircuit.indexing V) V.computation.tm.m l)
  | .inr (.inl l) => ForestPlacement.statement (transitionPorts V)
      (fun l => labels (.inr (.inl l))) (some (labels (.inr (.inr .copyOut))))
      (AcceptanceStage.program V l)
  | .inr (.inr l) => ForestPlacement.statement (finishPorts V)
      (fun l => labels (.inr (.inr l))) exit (CircuitFinish.program (σ := Unit × Bool) l)

def initial (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  boundary V input (V.horizon input.length) (snapshot (VerifierCircuit.initialFrame V input))

def afterIteration (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  finished V input (snapshot (VerifierCircuit.timeFrame V input (V.horizon input.length)))

def afterAcceptance (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  finished V input (snapshot (ProducerInvariant.finalFrame V input))

def terminal (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  ForestPlacement.fill (finishPorts V) (afterAcceptance V input)
    (CircuitFinish.verifierFinalTapes V input)

def timePolynomial (V : NPVerifier) : Polynomial Nat :=
  ProducerTime.iterationPolynomial V +
    (ProducerTime.acceptanceEmissionPolynomial V + ProducerTime.loweringPolynomial V) +
    ProducerTime.finishPolynomial V

theorem finish_entry (V : NPVerifier) (input : List Bool) :
    ForestPlacement.fill (finishPorts V) (afterAcceptance V input)
      (CircuitFinish.verifierInitialTapes V input) = afterAcceptance V input := by
  have h := circuitFinish_view V input
  change (fun t => afterAcceptance V input (finishPorts V t)) =
    CircuitFinish.verifierInitialTapes V input at h
  rw [← h, ForestPlacement.fill_self]

def inTime {Λ : Type} (V : NPVerifier) (labels : Label V → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet V) Λ State)
    (code : ∀ l, program (labels l) = statement V labels exit l)
    (input : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (entry V)), initialState, initial V input⟩
      (some ⟨exit, initialState, terminal V input⟩)
      ((timePolynomial V).eval input.length) := by
  have iter := TransitionIteration.verifierPlacedInPolynomialTime V input
    (transitionPorts V) (fun l => labels (.inl l))
    (some (labels (.inr (.inl (AcceptanceStage.entry V))))) program
    (fun l => code (.inl l)) (bootstrapPrepared V input) (localBase V input)
  have iter' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (entry V)), initialState, initial V input⟩
      (some ⟨some (labels (.inr (.inl (AcceptanceStage.entry V)))), initialState,
        afterIteration V input⟩)
      ((ProducerTime.iterationPolynomial V).eval input.length) := iter
  have accept := AcceptanceStage.verifierPlacedInPolynomialTime V input
    (transitionPorts V) (fun l => labels (.inr (.inl l)))
    (some (labels (.inr (.inr .copyOut)))) program
    (fun l => code (.inr (.inl l))) (bootstrapPrepared V input) (localBase V input)
  have accept' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.inr (.inl (AcceptanceStage.entry V)))), initialState,
        afterIteration V input⟩
      (some ⟨some (labels (.inr (.inr .copyOut))), initialState,
        afterAcceptance V input⟩)
      ((ProducerTime.acceptanceEmissionPolynomial V + ProducerTime.loweringPolynomial V).eval
        input.length) := accept
  have finish := CircuitFinish.verifierPlacedInPolynomialTime (finishPorts V)
    (fun l => labels (.inr (.inr l))) exit (afterAcceptance V input) program
    (fun l => code (.inr (.inr l))) V input ((), false) none
  rw [finish_entry] at finish
  have combined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (StateTransition.EvalsToInTime.trans _ _ _ _ _ _ iter' accept') finish
  simpa only [timePolynomial, Polynomial.eval_add, terminal, initialState,
    TermMachine.initialState, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using combined

def program (V : NPVerifier) : Label V → TM2.Stmt (Alphabet V) (Label V) State :=
  statement V id none

def programInTime (V : NPVerifier) (input : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program V))
      ⟨some (entry V), initialState, initial V input⟩
      (some ⟨none, initialState, terminal V input⟩)
      ((timePolynomial V).eval input.length) :=
  inTime V id none (program V) (fun _ => rfl) input

theorem terminal_output (V : NPVerifier) (input : List Bool) :
    terminal V input (output V) = circuitBits (VerifierCircuit.circuitOfVerifier V input) := by
  change ForestPlacement.fill (finishPorts V) _ _ (finishPorts V .output) = _
  rw [ForestPlacement.fill_at, CircuitFinish.verifierFinal_output]

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerTailStage

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerMachine

open Turing ProducerArena

local instance completenessLabelFintype (V : NPVerifier) :
    Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance completenessStateFintype (V : NPVerifier) :
    Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance completenessAlphabetFintype (V : NPVerifier) :
    ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance completenessLabelDecidableEq (V : NPVerifier) :
    DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance completenessStateDecidableEq (V : NPVerifier) :
    DecidableEq V.computation.tm.σ := Classical.decEq _
local instance completenessAlphabetDecidableEq (V : NPVerifier) :
    ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

abbrev Label (V : NPVerifier) :=
  ProducerFrontStage.Label V ⊕ (InitializationStage.Label V ⊕ ProducerTailStage.Label V)

def initPorts (V : NPVerifier) : InitializationStage.FullPorts (Tape V) where
  emit := initializationPorts V
  lower := forestPorts V
  output_shared := rfl
  count_shared := rfl

def initLabels (V : NPVerifier) : InitializationStage.Label V ↪ Label V :=
  ⟨fun l => .inr (.inl l), by intro a b h; exact Sum.inl.inj (Sum.inr.inj h)⟩

def entry (V : NPVerifier) : Label V := .inl (ProducerFrontStage.entry V)

def program (V : NPVerifier) : Label V → TM2.Stmt (Alphabet V) (Label V) State
  | .inl l => ProducerFrontStage.statement V Sum.inl
      (some (initLabels V (InitializationStage.entry V))) l
  | .inr (.inl l) => InitializationStage.statement V (initPorts V) (initLabels V)
      (some (.inr (.inr (ProducerTailStage.entry V)))) l
  | .inr (.inr l) => ProducerTailStage.statement V (fun l => .inr (.inr l)) none l

def timePolynomial (V : NPVerifier) : Polynomial Nat :=
  ProducerFrontStage.timePolynomial V + InitializationStage.timePolynomial V +
    ProducerTailStage.timePolynomial V

theorem initializerReady (V : NPVerifier) (input : List Bool) :
    InitializationStage.FullReady V (initPorts V) (bootstrapPrepared V input) input :=
  ⟨ProducerHandoffs.bootstrap_emitter_ready V input,
    ProducerHandoffs.bootstrap_lowerer_ready V input⟩

def inTime (V : NPVerifier) (input : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program V))
      ⟨some (entry V), initialState, initialTapes V input⟩
      (some ⟨none, initialState, ProducerTailStage.terminal V input⟩)
      ((timePolynomial V).eval input.length) := by
  have front := ProducerFrontStage.inTime V Sum.inl
    (some (initLabels V (InitializationStage.entry V))) (program V)
    (fun _ => rfl) input
  have init := InitializationStage.verifierPlacedInPolynomialTime V (initPorts V)
    (initLabels V) (some (.inr (.inr (ProducerTailStage.entry V))))
    (program V) (fun _ => rfl) (bootstrapPrepared V input) input
    (initializerReady V input) ()
  have init' : StateTransition.EvalsToInTime (TM2.step (program V))
      ⟨some (initLabels V (InitializationStage.entry V)), initialState, bootstrapPrepared V input⟩
      (some ⟨some (.inr (.inr (ProducerTailStage.entry V))), initialState,
        ProducerTailStage.initial V input⟩)
      ((InitializationStage.timePolynomial V).eval input.length) := by
    simpa only [initPorts, ProducerHandoffs.initial_result_eq_boundary,
      ProducerTailStage.initial, initialState, TermMachine.initialState,
      ClashMachine.clean] using init
  have tail := ProducerTailStage.inTime V (fun l => .inr (.inr l)) none
    (program V) (fun _ => rfl) input
  have combined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (StateTransition.EvalsToInTime.trans _ _ _ _ _ _ front init') tail
  simpa only [entry, timePolynomial, Polynomial.eval_add,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using combined

def rawProgram (V : NPVerifier) : MachineCanonicalOutput.Program (Tape V) (Label V) State where
  input := raw V
  output := output V
  main := entry V
  initial := initialState
  code := program V

theorem initialCfg (V : NPVerifier) (input : List Bool) :
    initList (MachineCanonicalOutput.sourceMachine (rawProgram V)) input =
      (⟨some (entry V), initialState, initialTapes V input⟩ :
        (MachineCanonicalOutput.sourceMachine (rawProgram V)).Cfg) := by
  unfold initList
  congr 1
  funext k
  rw [initialTapes_eq]
  rfl

def terminalRun (V : NPVerifier) (input : List Bool) :
    MachineCanonicalOutput.TerminalRun (rawProgram V) input
      (circuitBits (VerifierCircuit.circuitOfVerifier V input))
      ((timePolynomial V).eval input.length) where
  state := initialState
  tapes := ProducerTailStage.terminal V input
  execution := by
    rw [initialCfg]
    exact inTime V input
  output_eq := ProducerTailStage.terminal_output V input

def cleanupTapes (V : NPVerifier) : List (Tape V) :=
  (Finset.univ.erase (output V)).toList

theorem cleanup_complete (V : NPVerifier) (k : Tape V) :
    k ∈ cleanupTapes V ↔ k ≠ (rawProgram V).output := by
  simp [cleanupTapes, rawProgram]

def computableInPolyTime (V : NPVerifier) :
    TM2ComputableInPolyTime id circuitBits (VerifierCircuit.circuitOfVerifier V) :=
  MachineCanonicalOutput.computableInPolyTime (rawProgram V) (cleanupTapes V)
    (cleanup_complete V) id circuitBits (VerifierCircuit.circuitOfVerifier V)
    (timePolynomial V) (terminalRun V)

theorem finiteAlphabet (V : NPVerifier) :
    MachineFiniteAlphabet.FiniteAlphabet (computableInPolyTime V).tm :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet
    (rawProgram V) (cleanupTapes V) (cleanup_complete V)
    id circuitBits (VerifierCircuit.circuitOfVerifier V) (timePolynomial V) (terminalRun V)

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.Completeness

open Turing

theorem circuitProducerFinite :
    MachineFiniteAlphabet.FiniteAlphabet CircuitProducer.computableInPolyTime.tm := by
  intro k
  change Finite Bool
  infer_instance

def verifierReduction (V : NPVerifier) : PolynomialThreeSATReduction V.Accepts where
  reduce input := (VerifierCircuit.circuitOfVerifier V input).toFormula
  computation := MachineSequential.composeBits (ProducerMachine.computableInPolyTime V)
    CircuitProducer.computableInPolyTime
  correct input := (VerifierCircuit.circuitOfVerifier_correct V input).symm

theorem verifierReduction_finiteAlphabet (V : NPVerifier) :
    MachineFiniteAlphabet.FiniteAlphabet (verifierReduction V).computation.tm :=
  MachineFiniteAlphabet.composeBits (ProducerMachine.computableInPolyTime V)
    CircuitProducer.computableInPolyTime (ProducerMachine.finiteAlphabet V) circuitProducerFinite

theorem threeSATReduction (language : List Bool → Prop) (membership : InNP language) :
    ∃ source : PolynomialThreeSATReduction language,
      MachineFiniteAlphabet.FiniteAlphabet source.computation.tm := by
  obtain ⟨V, recognized⟩ := membership
  let source : PolynomialThreeSATReduction language := {
    reduce := (verifierReduction V).reduce
    computation := (verifierReduction V).computation
    correct := fun input => (recognized input).trans ((verifierReduction V).correct input) }
  exact ⟨source, verifierReduction_finiteAlphabet V⟩

end BinPackingGames.Foundations.Complexity.CookLevin.Completeness

end

end OAI
