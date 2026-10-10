import OAI.Computability.PerfectCompleteness.Machines.AcceptanceMachine
import OAI.Computability.PerfectCompleteness.Machines.AcceptanceStage
import OAI.Computability.PerfectCompleteness.Machines.CircuitFinish
import OAI.Computability.PerfectCompleteness.Machines.CircuitProducerStagesLemmas
import OAI.Computability.PerfectCompleteness.Machines.ForestStage
import OAI.Computability.PerfectCompleteness.Machines.ProducerArenaLemmas
import OAI.Computability.PerfectCompleteness.Machines.ProducerBootstrapLemmas
import OAI.Computability.PerfectCompleteness.Machines.ProducerInvariant
import OAI.Computability.PerfectCompleteness.Machines.TransitionIteration
import OAI.Computability.PerfectCompleteness.Machines.ValidityComposition
import OAI.Computability.PerfectCompleteness.Machines.VerifierFront
import OAI.Computability.UniqueGames.Machines.MachineCanonicalOutputLemmas

namespace OAI


noncomputable section
namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.ProducerTime

open CircuitBatch StatementCircuit PostfixModel PostfixAlignment ProducerInvariant
open MachineComposition VerifierCircuit
open scoped BigOperators

local instance (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

def bootstrapPolynomial (V : NPVerifier) : Polynomial Nat :=
  2 * WitnessEncoding.freeInputPolynomial V.witnessBound + 5

def validityPolynomial (V : NPVerifier) : Polynomial Nat :=
  ValidityMachine.Full.timePolynomial.comp V.witnessBound

def loweringPolynomial (V : NPVerifier) : Polynomial Nat :=
  ForestStage.timePolynomial.comp (4 * stageEnvelopePolynomial V + 1)

def transitionEmissionPolynomial (V : NPVerifier) : Polynomial Nat :=
  (TransitionMachine.timePolynomial (indexing V)
    (TransitionMachine.transitionPlan (indexing V) V.computation.tm.m)).comp
      (2 * stageEnvelopePolynomial V)

def acceptanceEmissionPolynomial (V : NPVerifier) : Polynomial Nat :=
  (AcceptanceMachine.timePolynomial (indexing V) (AcceptancePlan.plan V)).comp
    (2 * stageEnvelopePolynomial V)

def finishPolynomial (V : NPVerifier) : Polynomial Nat :=
  9 * budgetPolynomial V + tapePolynomial V + 18

def iterationPolynomial (V : NPVerifier) : Polynomial Nat :=
  Bounds.horizonPolynomial V.computation.time V.witnessBound *
    (1 + transitionEmissionPolynomial V + loweringPolynomial V) + 1

def knownPhasePolynomial (V : NPVerifier) : Polynomial Nat :=
  VerifierFront.timePolynomial V + bootstrapPolynomial V + 1 + validityPolynomial V +
    loweringPolynomial V + iterationPolynomial V + acceptanceEmissionPolynomial V +
    loweringPolynomial V + finishPolynomial V

def producerPolynomial (V : NPVerifier) (cellTime : Polynomial Nat) : Polynomial Nat :=
  knownPhasePolynomial V + cellTime

theorem bootstrapPolynomial_eval (V : NPVerifier) (n : Nat) :
    (bootstrapPolynomial V).eval n = 2 * (2 * V.witnessBound.eval n + 1) + 5 := by
  simp [bootstrapPolynomial]

theorem validity_steps_le (V : NPVerifier) (n : Nat) :
    ValidityMachine.Full.steps (V.witnessBound.eval n) ≤ (validityPolynomial V).eval n := by
  simpa only [validityPolynomial, Polynomial.eval_comp] using
    ValidityMachine.Full.steps_le_time (V.witnessBound.eval n)

theorem front_steps_le (V : NPVerifier) (input : List Bool) :
    (VerifierFront.prepareInTime V input ()).steps ≤
      (VerifierFront.timePolynomial V).eval input.length :=
  (VerifierFront.prepareInTime V input ()).steps_le_m

theorem loweringPolynomial_eval (V : NPVerifier) (n : Nat) :
    (loweringPolynomial V).eval n =
      25 * (4 * (stageEnvelopePolynomial V).eval n + 1)^2 +
      80 * (4 * (stageEnvelopePolynomial V).eval n + 1) + 20 := by
  simp [loweringPolynomial, ForestStage.timePolynomial]

theorem transitionEmissionPolynomial_eval (V : NPVerifier) (n : Nat) :
    (transitionEmissionPolynomial V).eval n =
      TransitionMachine.timeConstant (indexing V)
        (TransitionMachine.transitionPlan (indexing V) V.computation.tm.m) *
          (2 * (stageEnvelopePolynomial V).eval n + 1)^2 := by
  simp [transitionEmissionPolynomial, TransitionMachine.timePolynomial]

theorem acceptanceEmissionPolynomial_eval (V : NPVerifier) (n : Nat) :
    (acceptanceEmissionPolynomial V).eval n =
      AcceptanceMachine.timeConstant (indexing V) (AcceptancePlan.plan V) *
        (2 * (stageEnvelopePolynomial V).eval n + 1)^2 := by
  simp [acceptanceEmissionPolynomial, AcceptanceMachine.timePolynomial]

variable {inputs oldWidth newWidth : Nat}

def forestSteps (f : Frame inputs oldWidth) (es : Fin newWidth → Expr (Fin oldWidth))
    (oldRoots : List Bool) : Nat :=
  ForestStage.steps (forestTokens (fun i => (f.wires i).val) (List.ofFn es))
    (next f) (Batch.roots (next f) (List.ofFn es)).reverse
    (Batch.gates (fun i => (f.wires i).val) (next f) (List.ofFn es)) oldRoots

theorem forestSteps_le (V : NPVerifier) (input : List Bool)
    (f : Frame inputs oldWidth) (es : Fin newWidth → Expr (Fin oldWidth))
    (oldRoots : List Bool)
    (hc : next f ≤ (stageEnvelopePolynomial V).eval input.length)
    (he : Batch.cost (List.ofFn es) ≤ (stageEnvelopePolynomial V).eval input.length)
    (ht : (tokenBits (forestTokens (fun i => (f.wires i).val) (List.ofFn es))).length ≤
      (stageEnvelopePolynomial V).eval input.length)
    (hr : oldRoots.length ≤ (stageEnvelopePolynomial V).eval input.length) :
    forestSteps f es oldRoots ≤ (loweringPolynomial V).eval input.length := by
  have h := ForestStage.forest_steps_le (fun i => (f.wires i).val)
    (List.ofFn es) (next f) oldRoots (fun i => (f.wires i).isLt)
  change ForestStage.steps _ _ _ _ _ ≤ _
  apply h.trans
  rw [loweringPolynomial, Polynomial.eval_comp]
  apply natPolynomial_eval_mono
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_one]
  omega

def initialForestSteps (V : NPVerifier) (input : List Bool) : Nat :=
  forestSteps (Frame.initial (id : Fin (2 * V.witnessBound.eval input.length + 1) →
    Fin (2 * V.witnessBound.eval input.length + 1))) (initialExpressions V input) []

theorem initialForestSteps_le (V : NPVerifier) (input : List Bool) :
    initialForestSteps V input ≤ (loweringPolynomial V).eval input.length := by
  have hg := circuitOfVerifier_gates_le_polynomial V input
  rw [circuitOfVerifier_gate_count] at hg
  have hb := budgetPolynomial_eval V input
  have hE := stageEnvelopePolynomial_eval V input
  have ht := initial_tokens_length_le V input
  apply forestSteps_le
  · change _ + 0 ≤ _
    omega
  · omega
  · exact ht.trans (by omega)
  · simp

def transitionForestSteps (V : NPVerifier) (input : List Bool) (t : Nat) : Nat :=
  forestSteps (timeFrame V input t) (VerifierCircuit.stepExpressions V input)
    (snapshot (timeFrame V input t)).rootBits

theorem transitionForestSteps_le (V : NPVerifier) (input : List Bool) (t : Nat)
    (ht : t < V.horizon input.length) :
    transitionForestSteps V input t ≤ (loweringPolynomial V).eval input.length := by
  obtain ⟨_, hc, he, hr, htok⟩ := timeFrame_stageEnvelope V input t ht
  exact forestSteps_le V input _ _ _ hc he htok hr

def acceptanceForestSteps (V : NPVerifier) (input : List Bool) : Nat :=
  forestSteps (timeFrame V input (V.horizon input.length))
    (fun _ : Fin 1 => acceptanceExpr V input)
    (snapshot (timeFrame V input (V.horizon input.length))).rootBits

theorem acceptanceForestSteps_le (V : NPVerifier) (input : List Bool) :
    acceptanceForestSteps V input ≤ (loweringPolynomial V).eval input.length := by
  have hg := circuitOfVerifier_gates_le_polynomial V input
  rw [circuitOfVerifier_gate_count] at hg
  have hb := budgetPolynomial_eval V input
  have hE := stageEnvelopePolynomial_eval V input
  have hc := timeFrame_current_le V input (V.horizon input.length) le_rfl
  have hr := (timeFrame_lengths_le V input (V.horizon input.length) le_rfl).2.1
  have htok := acceptance_tokens_length_le V input
  apply forestSteps_le
  · omega
  · simp only [List.ofFn_succ, List.ofFn_zero, Batch.cost_cons, Batch.cost_nil, Nat.add_zero]
    omega
  · exact htok.trans (by omega)
  · exact hr.trans (by omega)

def frameInput (V : NPVerifier) (input : List Bool) (t : Nat) : TermMachine.Input :=
  AcceptanceMachine.verifierInput V input (fun i => ((timeFrame V input t).wires i).val)

theorem frameInput_dataSize_le (V : NPVerifier) (input : List Bool) (t : Nat)
    (ht : t ≤ V.horizon input.length) :
    TransitionMachine.dataSize (frameInput V input t) ≤
      2 * (stageEnvelopePolynomial V).eval input.length := by
  have hE := stageEnvelopePolynomial_eval V input
  have hr := (timeFrame_lengths_le V input t ht).2.1
  change capacity V input.length + (snapshot (timeFrame V input t)).rootBits.length ≤ _
  omega

def transitionEmissionSteps (V : NPVerifier) (input : List Bool) (t : Nat) : Nat :=
  TransitionMachine.steps (indexing V) (TransitionMachine.transitionPlan (indexing V)
    V.computation.tm.m) (frameInput V input t)

theorem transitionEmissionSteps_le (V : NPVerifier) (input : List Bool) (t : Nat)
    (ht : t ≤ V.horizon input.length) :
    transitionEmissionSteps V input t ≤ (transitionEmissionPolynomial V).eval input.length := by
  have hv : TransitionMachine.Valid (indexing V)
      (TransitionMachine.transitionPlan (indexing V) V.computation.tm.m)
      (frameInput V input t) := by
    simp [TransitionMachine.Valid, TransitionMachine.transitionPlan, frameInput,
      AcceptanceMachine.verifierInput, width]
  have h := TransitionMachine.steps_le (indexing V)
    (TransitionMachine.transitionPlan (indexing V) V.computation.tm.m) (frameInput V input t) hv
  change TransitionMachine.steps _ _ _ ≤ _
  have he : TransitionMachine.timeConstant (indexing V)
      (TransitionMachine.transitionPlan (indexing V) V.computation.tm.m) *
      (TransitionMachine.dataSize (frameInput V input t) + 1)^2 =
      (TransitionMachine.timePolynomial (indexing V)
        (TransitionMachine.transitionPlan (indexing V) V.computation.tm.m)).eval
          (TransitionMachine.dataSize (frameInput V input t)) := by
    simp [TransitionMachine.timePolynomial]
  rw [he] at h
  apply h.trans
  rw [transitionEmissionPolynomial, Polynomial.eval_comp]
  apply natPolynomial_eval_mono
  simpa using frameInput_dataSize_le V input t ht

def acceptanceEmissionSteps (V : NPVerifier) (input : List Bool) : Nat :=
  AcceptanceMachine.steps (indexing V) (AcceptancePlan.plan V)
    (frameInput V input (V.horizon input.length))

theorem acceptanceEmissionSteps_le (V : NPVerifier) (input : List Bool) :
    acceptanceEmissionSteps V input ≤ (acceptanceEmissionPolynomial V).eval input.length := by
  have hv := AcceptanceMachine.verifierInput_valid V input
    (fun i => ((timeFrame V input (V.horizon input.length)).wires i).val)
  have h := AcceptanceMachine.steps_le (indexing V) (AcceptancePlan.plan V)
    (frameInput V input (V.horizon input.length)) hv
  change AcceptanceMachine.steps _ _ _ ≤ _
  have he : AcceptanceMachine.timeConstant (indexing V) (AcceptancePlan.plan V) *
      (TransitionMachine.dataSize (frameInput V input (V.horizon input.length)) + 1)^2 =
      (AcceptanceMachine.timePolynomial (indexing V) (AcceptancePlan.plan V)).eval
        (TransitionMachine.dataSize (frameInput V input (V.horizon input.length))) := by
    simp [AcceptanceMachine.timePolynomial]
  rw [he] at h
  apply h.trans
  rw [acceptanceEmissionPolynomial, Polynomial.eval_comp]
  apply natPolynomial_eval_mono
  simpa using frameInput_dataSize_le V input (V.horizon input.length) le_rfl

def finishSteps (V : NPVerifier) (input : List Bool) : Nat :=
  let C := circuitOfVerifier V input
  CircuitFinish.totalTime C.wires C.inputs C.output.val (recordsBits C.records).length

theorem finishSteps_le (V : NPVerifier) (input : List Bool) :
    finishSteps V input ≤ (finishPolynomial V).eval input.length := by
  let C := circuitOfVerifier V input
  have hf : C.inputs ≤ C.wires := Nat.le_add_right _ _
  have h := CircuitFinish.totalTime_le C.wires C.inputs C.output.val
    (recordsBits C.records).length hf C.output.isLt
  have hg := circuitOfVerifier_gates_le_polynomial V input
  have hb := budgetPolynomial_eval V input
  have hr := (finalFrame_lengths_le V input).2.2
  have hr' : (recordsBits C.records).length ≤ (tapePolynomial V).eval input.length := by
    simpa only [snapshot, List.length_reverse, Circuit.records, finalFrame, C,
      circuitOfVerifier, Frame.toCircuit, Fragment.toCircuit] using hr
  have hc : C.wires ≤ (budgetPolynomial V).eval input.length := by
    change (2 * V.witnessBound.eval input.length + 1) +
      (circuitOfVerifier V input).gates.length ≤ _
    omega
  unfold finishSteps
  apply h.trans
  simp only [finishPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat]
  omega

theorem iterationPolynomial_eval (V : NPVerifier) (input : List Bool) :
    (iterationPolynomial V).eval input.length = V.horizon input.length *
      (1 + (transitionEmissionPolynomial V).eval input.length +
        (loweringPolynomial V).eval input.length) + 1 := by
  simp [iterationPolynomial, NPVerifier.horizon]

def iterationSteps (V : NPVerifier) (input : List Bool) : Nat :=
  (∑ t ∈ Finset.range (V.horizon input.length),
    (1 + transitionEmissionSteps V input t + transitionForestSteps V input t)) + 1

theorem iterationSteps_le (V : NPVerifier) (input : List Bool) :
    iterationSteps V input ≤ (iterationPolynomial V).eval input.length := by
  rw [iterationPolynomial_eval]
  unfold iterationSteps
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑ _t ∈ Finset.range (V.horizon input.length),
        (1 + (transitionEmissionPolynomial V).eval input.length +
          (loweringPolynomial V).eval input.length) := by
      apply Finset.sum_le_sum
      intro t ht
      have hlt := Finset.mem_range.mp ht
      exact Nat.add_le_add
        (Nat.add_le_add_left (transitionEmissionSteps_le V input t (Nat.le_of_lt hlt)) 1)
        (transitionForestSteps_le V input t hlt)
    _ = _ := by simp

def knownPhaseSteps (V : NPVerifier) (input : List Bool) : Nat :=
  (VerifierFront.prepareInTime V input ()).steps +
    (2 * (2 * V.witnessBound.eval input.length + 1) + 5) + 1 +
    ValidityMachine.Full.steps (V.witnessBound.eval input.length) + initialForestSteps V input +
    iterationSteps V input + acceptanceEmissionSteps V input + acceptanceForestSteps V input +
    finishSteps V input

theorem knownPhaseSteps_le (V : NPVerifier) (input : List Bool) :
    knownPhaseSteps V input ≤ (knownPhasePolynomial V).eval input.length := by
  have hf := front_steps_le V input
  have hb := bootstrapPolynomial_eval V input.length
  have hv := validity_steps_le V input.length
  have hi := initialForestSteps_le V input
  have ht := iterationSteps_le V input
  have ha := acceptanceEmissionSteps_le V input
  have hl := acceptanceForestSteps_le V input
  have he := finishSteps_le V input
  simp only [knownPhasePolynomial, Polynomial.eval_add, Polynomial.eval_one]
  unfold knownPhaseSteps
  omega

theorem producerPolynomial_eval (V : NPVerifier) (cellTime : Polynomial Nat) (n : Nat) :
    (producerPolynomial V cellTime).eval n =
      (knownPhasePolynomial V).eval n + cellTime.eval n := by
  simp only [producerPolynomial, Polynomial.eval_add]

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.ProducerTime

end


noncomputable section
namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.AcceptanceStage

open Turing MachineComposition StatementCircuit CircuitBatch TransitionArena
open ProducerInvariant VerifierCircuit


local instance (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
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

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.AcceptanceStage


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.CircuitFinish

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

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.CircuitFinish


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionIteration


open Turing MachineComposition StatementCircuit CircuitBatch TransitionArena
open scoped BigOperators

section Generic
variable {K Λ σ : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, DecidableEq (Γ k)] [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ]
variable {inputs : Nat}

theorem steps_eq_sum (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (S : Nat)
    (frame : Frame inputs (indexing.width S + 1)) (remaining : Nat) :
    steps indexing machineProgram S frame remaining =
      (∑ t ∈ Finset.range remaining,
        (1 + stageSteps indexing machineProgram S
          (frame.repeat (ProducerInvariant.stepExpressions indexing machineProgram S) t))) + 1 := by
  induction remaining generalizing frame with
  | zero => simp [steps]
  | succ remaining ih =>
    rw [steps, ih, Finset.sum_range_succ']
    simp only [ProducerInvariant.step_repeat, Frame.repeat]
    omega

theorem tokens_frame_eq_forest (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (S : Nat)
    (frame : Frame inputs (indexing.width S + 1)) :
    tokens indexing machineProgram S (ProducerInvariant.snapshot frame) =
      PostfixAlignment.forestTokens (fun i => (frame.wires i).val)
        (List.ofFn (ProducerInvariant.stepExpressions indexing machineProgram S)) := by
  rw [tokens, ProducerInvariant.transitionTokens_eq]
  have hw : (fun i : Fin (indexing.width S + 1) =>
      (ProducerInvariant.snapshot frame).roots[i.val]?.getD 0) =
      (fun i => (frame.wires i).val) := by
    funext i
    change (List.ofFn (fun i => (frame.wires i).val))[i.val]?.getD 0 = _
    rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using i.isLt), List.getElem_ofFn]
    rfl
  rw [hw]

theorem lowerSteps_eq_forestSteps (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (S : Nat)
    (frame : Frame inputs (indexing.width S + 1)) :
    lowerSteps indexing machineProgram S frame =
      ProducerTime.forestSteps frame (ProducerInvariant.stepExpressions indexing machineProgram S)
        (encodeWords (ProducerInvariant.rootValues frame)) := by
  unfold lowerSteps ProducerTime.forestSteps
  rw [tokens_frame_eq_forest]
  have roots := ProducerInvariant.step_roots frame (ProducerInvariant.stepExpressions indexing machineProgram S)
  change ProducerInvariant.rootValues (frame.step (ProducerInvariant.stepExpressions indexing machineProgram S)) = _ at roots
  rw [roots]
  rfl

end Generic

local instance (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

theorem stageSteps_verifier (V : NPVerifier) (input : List Bool) (t : Nat) :
    stageSteps (VerifierCircuit.indexing V) V.computation.tm.m
      (VerifierCircuit.capacity V input.length) (VerifierCircuit.timeFrame V input t) =
      ProducerTime.transitionEmissionSteps V input t + ProducerTime.transitionForestSteps V input t := by
  rw [stageSteps, lowerSteps_eq_forestSteps, ProducerInvariant.stepExpressions_verifier]
  rfl

theorem verifier_steps_eq (V : NPVerifier) (input : List Bool) :
    steps (VerifierCircuit.indexing V) V.computation.tm.m
      (VerifierCircuit.capacity V input.length) (VerifierCircuit.initialFrame V input)
      (V.horizon input.length) = ProducerTime.iterationSteps V input := by
  rw [steps_eq_sum, ProducerInvariant.stepExpressions_verifier]
  unfold ProducerTime.iterationSteps
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  change 1 + stageSteps (VerifierCircuit.indexing V) V.computation.tm.m
    (VerifierCircuit.capacity V input.length) (VerifierCircuit.timeFrame V input t) = _
  rw [stageSteps_verifier]
  omega

theorem verifier_steps_le (V : NPVerifier) (input : List Bool) :
    steps (VerifierCircuit.indexing V) V.computation.tm.m
      (VerifierCircuit.capacity V input.length) (VerifierCircuit.initialFrame V input)
      (V.horizon input.length) ≤ (ProducerTime.iterationPolynomial V).eval input.length := by
  rw [verifier_steps_eq]
  exact ProducerTime.iterationSteps_le V input

noncomputable def verifierInPolynomialTime (V : NPVerifier) (input : List Bool)
    (base : Tape → List Bool) :
    StateTransition.EvalsToInTime
      (machine (VerifierCircuit.indexing V) V.computation.tm.m).step
      ⟨some (entry (VerifierCircuit.indexing V) V.computation.tm.m), TermMachine.initialState,
        tapes base (VerifierCircuit.capacity V input.length) (V.horizon input.length)
          (ProducerInvariant.snapshot (VerifierCircuit.initialFrame V input))⟩
      (some ⟨none, TermMachine.initialState,
        finishTapes base (VerifierCircuit.capacity V input.length)
          (ProducerInvariant.snapshot (VerifierCircuit.timeFrame V input (V.horizon input.length)))⟩)
      ((ProducerTime.iterationPolynomial V).eval input.length) where
  steps := steps (VerifierCircuit.indexing V) V.computation.tm.m
    (VerifierCircuit.capacity V input.length) (VerifierCircuit.initialFrame V input) (V.horizon input.length)
  evals_in_steps := repeatTrace (VerifierCircuit.indexing V) V.computation.tm.m base
    (VerifierCircuit.capacity V input.length) (VerifierCircuit.initialFrame V input) (V.horizon input.length)
  steps_le_m := verifier_steps_le V input

noncomputable def verifierPlacedInPolynomialTime {CallerTape CallerLabel : Type}
    [DecidableEq CallerTape] (V : NPVerifier) (input : List Bool)
    (ports : Tape ↪ CallerTape)
    (labels : Label (VerifierCircuit.indexing V) V.computation.tm.m → CallerLabel)
    (exit : Option CallerLabel)
    (target : CallerLabel → TM2.Stmt (fun _ : CallerTape => Bool) CallerLabel State)
    (code : ∀ label, target (labels label) = ForestPlacement.statement ports labels exit
      (program (VerifierCircuit.indexing V) V.computation.tm.m label))
    (ambient : CallerTape → List Bool) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (entry (VerifierCircuit.indexing V) V.computation.tm.m)), TermMachine.initialState,
        ForestPlacement.fill ports ambient
          (tapes base (VerifierCircuit.capacity V input.length) (V.horizon input.length)
            (ProducerInvariant.snapshot (VerifierCircuit.initialFrame V input)))⟩
      (some ⟨exit, TermMachine.initialState,
        ForestPlacement.fill ports ambient (finishTapes base (VerifierCircuit.capacity V input.length)
          (ProducerInvariant.snapshot (VerifierCircuit.timeFrame V input (V.horizon input.length))))⟩)
      ((ProducerTime.iterationPolynomial V).eval input.length) := by
  simpa only [ForestPlacement.configuration, ForestPlacement.placedLabel] using
    ForestPlacement.execution ports labels exit ambient
      (program (VerifierCircuit.indexing V) V.computation.tm.m) target code
      (verifierInPolynomialTime V input base)

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionIteration

end


noncomputable section
namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.ProducerTailStage

open Turing ProducerArena ProducerInvariant ProducerHandoffs

local instance (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
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

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.ProducerTailStage


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.ProducerMachine

open Turing ProducerArena

local instance (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
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
  by_cases h : k = raw V <;>
    simp [MachineCanonicalOutput.sourceMachine, rawProgram, h] <;> rfl

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

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.ProducerMachine

end

end OAI
