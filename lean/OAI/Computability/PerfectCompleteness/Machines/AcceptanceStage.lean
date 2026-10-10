import OAI.Computability.PerfectCompleteness.Machines.AcceptanceMachine
import OAI.Computability.PerfectCompleteness.Machines.InitializationStageLemmas

namespace OAI

section

noncomputable section
namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.AcceptanceStage

open Turing MachineComposition StatementCircuit CircuitBatch
open PostfixModel PostfixAlignment ProducerInvariant VerifierCircuit
open TransitionArena


local instance (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

abbrev EmitLabel (V : NPVerifier) :=
  AcceptanceMachine.Label (indexing V) (AcceptancePlan.plan V)

abbrev Label (V : NPVerifier) := EmitLabel V ⊕ ForestStage.Label

def entry (V : NPVerifier) : Label V :=
  .inl (.carry (AcceptanceMachine.carryEmitter (indexing V)).entry)

def program (V : NPVerifier) : Label V → TM2.Stmt Alphabet (Label V) State
  | .inl label => ForestPlacement.statement termPorts Sum.inl
      (some (.inr .reverseTokens))
      (AcceptanceMachine.program (indexing V) (AcceptancePlan.plan V) label)
  | .inr label => ForestStage.statement forestPorts Sum.inr none label

def machine (V : NPVerifier) : FinTM2 where
  K := Tape
  k₀ := .inr .capacity
  k₁ := .inl .records
  Γ := Alphabet
  Λ := Label V
  main := entry V
  σ := State
  initialState := TermMachine.initialState
  m := program V

def expressions (V : NPVerifier) (input : List Bool) :
    Fin 1 → Expr (Fin (width V input + 1)) :=
  fun _ => acceptanceExpr V input

def wireValues {inputs count : Nat} (frame : Frame inputs count) : Fin count → Nat :=
  fun i => (frame.wires i).val

theorem tokens_eq_forest (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) :
    AcceptanceTemplate.tokens V input wire =
      forestTokens wire (List.ofFn (expressions V input)) := by
  rw [AcceptanceTemplate.tokens_eq]
  simp [expressions, List.ofFn_succ, forestTokens]

theorem finish_termFrame (base : Tape → List Bool) (S : Nat) (s : Snapshot) :
    TermMachine.Frame (termInput S s)
      (fun tape => finishTapes base S s (termPorts tape)) := by
  have restriction : (fun tape => finishTapes base S s (termPorts tape)) =
      (fun tape => tapes base S 0 s (termPorts tape)) := by
    funext tape
    rw [termPorts.eq_1]
    change finishTapes base S s (termTape tape) = tapes base S 0 s (termTape tape)
    cases tape <;> simp [finishTapes, termTape]
  rw [restriction]
  exact termFrame base S 0 s

def prepared (base : Tape → List Bool) (S : Nat) (s : Snapshot)
    (tokens : List Token) : Tape → List Bool :=
  Function.update
    (Function.update (finishTapes base S s) (.inl .tokens) (tokenBits tokens).reverse)
    (.inl (.lower .remaining)) (encodeWord tokens.length)

theorem finish_place_emitTapes (base : Tape → List Bool) (S : Nat) (s : Snapshot)
    (tokens : List Token) :
    ForestPlacement.fill termPorts (finishTapes base S s)
      (TermMachine.emitTapes (fun tape => finishTapes base S s (termPorts tape)) tokens) =
      prepared base S s tokens := by
  simp only [TermMachine.emitTapes, ForestPlacement.fill_update, ForestPlacement.fill_self]
  simp only [termPorts_apply]
  simp [termTape, tapes, finishTapes, prepared, encodeWord]

theorem prepared_eq_lower (base : Tape → List Bool) (S : Nat) (s : Snapshot)
    (tokens : List Token) :
    prepared base S s tokens =
      ForestPlacement.fill forestPorts (finishTapes base S s)
        (ForestStage.initialLocal s.current tokens s.reversedRecords (encodeWords s.roots)) := by
  rw [fill_forest]
  funext tape
  cases tape with
  | inl tape =>
    cases tape with
    | lower tape => cases tape <;>
        simp [prepared, finishTapes, tapes, ForestStage.initialLocal]
    | tokens => simp [prepared, finishTapes, ForestStage.initialLocal]
    | records => simp [prepared, finishTapes, tapes, ForestStage.initialLocal]
    | rootTable => simp [prepared, finishTapes, tapes, ForestStage.initialLocal]
  | inr tape => cases tape <;>
      simp [prepared, finishTapes, tapes]

theorem lower_final_eq {inputs oldWidth newWidth : Nat}
    (base : Tape → List Bool) (S : Nat) (frame : Frame inputs oldWidth)
    (es : Fin newWidth → Expr (Fin oldWidth)) :
    ForestPlacement.fill forestPorts (finishTapes base S (snapshot frame))
      (ForestStage.finalLocal (next (frame.step es)) (rootValues (frame.step es)).reverse
        (recordsBits (gateRecords (next frame)
          (Batch.gates (wireValues frame) (next frame) (List.ofFn es))))
        (recordBits frame).reverse) =
      finishTapes base S (snapshot (frame.step es)) := by
  rw [fill_forest]
  funext tape
  cases tape with
  | inl tape =>
    cases tape with
    | lower tape => cases tape <;> rfl
    | tokens => rfl
    | records =>
      change (recordsBits (gateRecords (next frame)
        (Batch.gates (wireValues frame) (next frame) (List.ofFn es)))).reverse ++
        (recordBits frame).reverse = (recordBits (frame.step es)).reverse
      rw [recordBits_step, List.reverse_append]
      rfl
    | rootTable =>
      change encodeWords (rootValues (frame.step es)).reverse.reverse =
        encodeWords (rootValues (frame.step es))
      rw [List.reverse_reverse]
  | inr tape => cases tape <;> rfl

def emissionSteps (V : NPVerifier) (input : List Bool) {inputs : Nat}
    (frame : Frame inputs (width V input + 1)) : Nat :=
  AcceptanceMachine.steps (indexing V) (AcceptancePlan.plan V)
    (AcceptanceMachine.verifierInput V input (wireValues frame))

def loweringSteps (V : NPVerifier) (input : List Bool) {inputs : Nat}
    (frame : Frame inputs (width V input + 1)) : Nat :=
  ForestStage.steps (AcceptanceTemplate.tokens V input (wireValues frame)) (next frame)
    (rootValues (frame.step (expressions V input))).reverse
    (Batch.gates (wireValues frame) (next frame) (List.ofFn (expressions V input)))
    (encodeWords (rootValues frame))

def steps (V : NPVerifier) (input : List Bool) {inputs : Nat}
    (frame : Frame inputs (width V input + 1)) : Nat :=
  emissionSteps V input frame + loweringSteps V input frame

private theorem chain {α : Type*} (f : α → α) {n m : Nat} {a b c : α}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm n m, Function.iterate_add_apply, first, second]

theorem fullTrace (V : NPVerifier) (input : List Bool) {inputs : Nat}
    (frame : Frame inputs (width V input + 1)) (base : Tape → List Bool) :
    (advance (TM2.step (program V)))^[steps V input frame]
      (some ⟨some (entry V), TermMachine.initialState,
        finishTapes base (capacity V input.length) (snapshot frame)⟩) =
      some ⟨none, TermMachine.initialState,
        finishTapes base (capacity V input.length)
          (snapshot (frame.step (expressions V input)))⟩ := by
  let boundary := finishTapes base (capacity V input.length) (snapshot frame)
  let wire := wireValues frame
  let inp := AcceptanceMachine.verifierInput V input wire
  let tokens := AcceptanceTemplate.tokens V input wire
  have hframe : TermMachine.Frame inp (fun tape => boundary (termPorts tape)) :=
    finish_termFrame base (capacity V input.length) (snapshot frame)
  have source := AcceptanceMachine.fullTrace (indexing V) (AcceptancePlan.plan V) inp
    (AcceptanceMachine.verifierInput_valid V input wire)
    (fun tape => boundary (termPorts tape)) hframe
  rw [AcceptanceMachine.outputTokens_eq_acceptance] at source
  have emitter := ForestPlacement.trace termPorts Sum.inl (some (.inr .reverseTokens))
    boundary (AcceptanceMachine.program (indexing V) (AcceptancePlan.plan V))
    (program V) (fun _ => rfl) _ _ _ source
  change (advance (TM2.step (program V)))^[emissionSteps V input frame]
    (some ⟨some (entry V), TermMachine.initialState,
      ForestPlacement.fill termPorts boundary (fun tape => boundary (termPorts tape))⟩) =
      some ⟨some (.inr .reverseTokens), TermMachine.initialState,
        ForestPlacement.fill termPorts boundary
          (TermMachine.emitTapes (fun tape => boundary (termPorts tape)) tokens)⟩ at emitter
  rw [ForestPlacement.fill_self] at emitter
  rw [finish_place_emitTapes, prepared_eq_lower] at emitter
  have valid := compile_frameForest frame (expressions V input)
  rw [← tokens_eq_forest] at valid
  have lower := ForestStage.traceAt forestPorts Sum.inr none (program V) (fun _ => rfl)
    boundary ((), false) tokens (next frame) (next (frame.step (expressions V input)))
    (rootValues (frame.step (expressions V input))).reverse
    (Batch.gates wire (next frame) (List.ofFn (expressions V input)))
    (recordBits frame).reverse (encodeWords (rootValues frame)) valid
  rw [lower_final_eq] at lower
  exact chain _ emitter lower

def budget (V : NPVerifier) (input : List Bool) {inputs : Nat}
    (frame : Frame inputs (width V input + 1)) : Nat :=
  (AcceptanceMachine.timePolynomial (indexing V) (AcceptancePlan.plan V)).eval
      (TransitionMachine.dataSize
        (AcceptanceMachine.verifierInput V input (wireValues frame))) +
    ForestStage.timePolynomial.eval
      (next frame + Batch.cost (List.ofFn (expressions V input)) +
        (tokenBits (AcceptanceTemplate.tokens V input (wireValues frame))).length +
        (encodeWords (rootValues frame)).length + 1)

theorem steps_le_budget (V : NPVerifier) (input : List Bool) {inputs : Nat}
    (frame : Frame inputs (width V input + 1)) : steps V input frame ≤ budget V input frame := by
  have he := AcceptanceMachine.steps_le (indexing V) (AcceptancePlan.plan V)
    (AcceptanceMachine.verifierInput V input (wireValues frame))
    (AcceptanceMachine.verifierInput_valid V input (wireValues frame))
  have hl := ForestStage.forest_steps_le (wireValues frame) (List.ofFn (expressions V input))
    (next frame) (encodeWords (rootValues frame)) (fun i => (frame.wires i).isLt)
  have roots : rootValues (frame.step (expressions V input)) =
      Batch.roots (next frame) (List.ofFn (expressions V input)) :=
    step_roots frame (expressions V input)
  rw [← tokens_eq_forest] at hl
  unfold steps emissionSteps loweringSteps budget
  rw [roots]
  apply Nat.add_le_add _ hl
  simpa only [AcceptanceMachine.timePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] using he

def inTime (V : NPVerifier) (input : List Bool) {inputs : Nat}
    (frame : Frame inputs (width V input + 1)) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (machine V).step
      ⟨some (entry V), TermMachine.initialState,
        finishTapes base (capacity V input.length) (snapshot frame)⟩
      (some ⟨none, TermMachine.initialState,
        finishTapes base (capacity V input.length)
          (snapshot (frame.step (expressions V input)))⟩)
      (budget V input frame) where
  steps := steps V input frame
  evals_in_steps := fullTrace V input frame base
  steps_le_m := steps_le_budget V input frame

theorem verifierTrace (V : NPVerifier) (input : List Bool) (base : Tape → List Bool) :
    (advance (TM2.step (program V)))^[
      steps V input (timeFrame V input (V.horizon input.length))]
      (some ⟨some (entry V), TermMachine.initialState,
        finishTapes base (capacity V input.length)
          (snapshot (timeFrame V input (V.horizon input.length)))⟩) =
      some ⟨none, TermMachine.initialState,
        finishTapes base (capacity V input.length) (snapshot (finalFrame V input))⟩ :=
  fullTrace V input (timeFrame V input (V.horizon input.length)) base

theorem final_root_singleton (V : NPVerifier) (input : List Bool) (base : Tape → List Bool) :
    finishTapes base (capacity V input.length) (snapshot (finalFrame V input))
      (.inl .rootTable) = encodeWords [((finalFrame V input).wires 0).val] := by
  simp [finishTapes, tapes, snapshot, List.ofFn_succ]

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.AcceptanceStage

end

end

end OAI
