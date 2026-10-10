import OAI.Computability.PerfectCompleteness.Machines.CellsTokensAlignmentLemmas
import OAI.Computability.PerfectCompleteness.Machines.ClashMachine
import OAI.Computability.PerfectCompleteness.Machines.ForestStage
import OAI.Computability.PerfectCompleteness.Machines.InitializationTemplateLemmas
import OAI.Computability.PerfectCompleteness.Machines.ProducerInvariant
import OAI.Computability.PerfectCompleteness.Machines.TermMachine

namespace OAI


noncomputable section
namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationStage

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

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationStage

end


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena


open Turing MachineComposition

inductive Extra
  | cursor | capacity | position | address | value | scratch | copy | saveLeft | saveRight
  | countdown | q | raw
  deriving DecidableEq

/-- A list enumerating every element of the type, which are all zero-argument constructors. (Generated by the `Fintype` deriving handler.)-/
protected abbrev Extra.enumList : List Extra := [.cursor, .capacity, .position, .address, .value,
  .scratch, .copy, .saveLeft, .saveRight, .countdown, .q, .raw]

protected theorem Extra.enumList_getElem?_ctorIdx_eq (x : Extra) :
    Extra.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Extra.enumList_nodup : Extra.enumList.Nodup := by decide

instance : Fintype Extra where
  elems := ⟨Extra.enumList, Extra.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape := ForestStage.Tape ⊕ Extra
abbrev Alphabet (_ : Tape) := Bool
abbrev State := TermMachine.State

def forestPorts : ForestStage.Tape ↪ Tape :=
  ⟨Sum.inl, Sum.inl_injective⟩

def termTape : TermMachine.Tape → Tape
  | .cursor => .inr .cursor
  | .capacity => .inr .capacity
  | .roots => .inl .rootTable
  | .count => .inl (.lower .remaining)
  | .reversed => .inl .tokens
  | .position => .inr .position
  | .address => .inr .address
  | .value => .inr .value
  | .scratch => .inr .scratch
  | .copy => .inr .copy
  | .saveLeft => .inr .saveLeft
  | .saveRight => .inr .saveRight

def termPorts : TermMachine.Tape ↪ Tape where
  toFun := termTape
  inj' := by intro a b h; cases a <;> cases b <;> simp_all [termTape]

@[simp] theorem termPorts_apply (tape : TermMachine.Tape) : termPorts tape = termTape tape := rfl

def termInput (S : Nat) (snapshot : ProducerInvariant.Snapshot) : TermMachine.Input :=
  ⟨0, S, snapshot.roots⟩

def tapes (base : Tape → List Bool) (S remaining : Nat)
    (snapshot : ProducerInvariant.Snapshot) : Tape → List Bool
  | .inl (.lower .current) => encodeWord snapshot.current
  | .inl (.lower .remaining) => encodeWord 0
  | .inl (.lower _) => []
  | .inl .tokens => []
  | .inl .records => snapshot.reversedRecords
  | .inl .rootTable => encodeWords snapshot.roots
  | .inr .cursor => encodeWord 0
  | .inr .capacity => encodeWord S
  | .inr .countdown => encodeWord remaining
  | .inr .q => base (.inr .q)
  | .inr .raw => base (.inr .raw)
  | .inr _ => []

def finishTapes (base : Tape → List Bool) (S : Nat)
    (snapshot : ProducerInvariant.Snapshot) : Tape → List Bool :=
  Function.update (tapes base S 0 snapshot) (.inr .countdown) []

@[simp] theorem tapes_q (base : Tape → List Bool) (S remaining : Nat)
    (snapshot : ProducerInvariant.Snapshot) : tapes base S remaining snapshot (.inr .q) =
      base (.inr .q) := rfl

@[simp] theorem tapes_raw (base : Tape → List Bool) (S remaining : Nat)
    (snapshot : ProducerInvariant.Snapshot) : tapes base S remaining snapshot (.inr .raw) =
      base (.inr .raw) := rfl

@[simp] theorem tapes_capacity (base : Tape → List Bool) (S remaining : Nat)
    (snapshot : ProducerInvariant.Snapshot) :
    tapes base S remaining snapshot (.inr .capacity) = encodeWord S := rfl

theorem termFrame (base : Tape → List Bool) (S remaining : Nat)
    (snapshot : ProducerInvariant.Snapshot) :
    TermMachine.Frame (termInput S snapshot)
      (fun tape => tapes base S remaining snapshot (termPorts tape)) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro tape ht
  cases tape <;> simp_all [TermMachine.work, termTape, tapes]

theorem tapes_countdown_tail (base : Tape → List Bool) (S remaining : Nat)
    (snapshot : ProducerInvariant.Snapshot) :
    Function.update (tapes base S (remaining + 1) snapshot) (.inr .countdown)
      (tapes base S (remaining + 1) snapshot (.inr .countdown)).tail =
        tapes base S remaining snapshot := by
  funext tape
  cases tape with
  | inl tape =>
    cases tape with
    | lower tape => cases tape <;> simp [tapes]
    | tokens => simp [tapes]
    | records => simp [tapes]
    | rootTable => simp [tapes]
  | inr tape => cases tape <;> simp [tapes, encodeWord, List.replicate_succ]

def preparedTapes (base : Tape → List Bool) (S remaining : Nat)
    (snapshot : ProducerInvariant.Snapshot) (tokens : List PostfixModel.Token) : Tape → List Bool :=
  Function.update
    (Function.update (tapes base S remaining snapshot) (.inl .tokens)
      (PostfixModel.tokenBits tokens).reverse)
    (.inl (.lower .remaining)) (encodeWord tokens.length)

theorem place_emitTapes (base : Tape → List Bool) (S remaining : Nat)
    (snapshot : ProducerInvariant.Snapshot) (tokens : List PostfixModel.Token) :
    ForestPlacement.fill termPorts (tapes base S remaining snapshot)
      (TermMachine.emitTapes (fun tape => tapes base S remaining snapshot (termPorts tape)) tokens) =
      preparedTapes base S remaining snapshot tokens := by
  simp only [TermMachine.emitTapes, ForestPlacement.fill_update, ForestPlacement.fill_self]
  simp [termTape, tapes, preparedTapes, encodeWord]

theorem fill_forest (base : Tape → List Bool) (contents : ForestStage.Tape → List Bool) :
    ForestPlacement.fill forestPorts base contents =
      fun tape => match tape with
      | .inl t => contents t
      | .inr t => base (.inr t) := by
  funext tape
  cases tape with
  | inl t => exact ForestPlacement.fill_at forestPorts base contents t
  | inr t =>
    exact ForestPlacement.fill_other forestPorts base contents (.inr t)
      (by intro i; simp [forestPorts])

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena

end OAI
