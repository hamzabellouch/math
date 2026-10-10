import OAI.Computability.PerfectCompleteness.Machines.ForestStage
import OAI.Computability.PerfectCompleteness.Machines.InitializationStageLemmas
import OAI.Computability.PerfectCompleteness.Machines.ProducerInvariant
import OAI.Computability.PerfectCompleteness.Machines.TransitionMachine

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionIteration


open Turing MachineComposition StatementCircuit CircuitBatch TransitionTemplate

open TransitionArena

section Transition

variable {K Λ σ : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, DecidableEq (Γ k)] [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ]

noncomputable def tokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (S : Nat)
    (snapshot : ProducerInvariant.Snapshot) : List PostfixModel.Token :=
  ProducerInvariant.transitionTokens indexing machineProgram S snapshot.roots

noncomputable def emitSteps (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (S : Nat)
    (snapshot : ProducerInvariant.Snapshot) : Nat :=
  TransitionMachine.steps indexing (TransitionMachine.transitionPlan indexing machineProgram)
    (termInput S snapshot)

theorem emitTraceAt {Caller : Type} (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ)
    (labels : TransitionMachine.Label indexing (TransitionMachine.transitionPlan indexing machineProgram) → Caller)
    (exit : Option Caller) (target : Caller → TM2.Stmt Alphabet Caller State)
    (code : ∀ label, target (labels label) = ForestPlacement.statement termPorts labels exit
      (TransitionMachine.program indexing (TransitionMachine.transitionPlan indexing machineProgram) label))
    (base : Tape → List Bool) (S remaining : Nat) (snapshot : ProducerInvariant.Snapshot)
    (valid : indexing.width S + 1 ≤ snapshot.roots.length) :
    (advance (TM2.step target))^[emitSteps indexing machineProgram S snapshot]
      (some ⟨some (labels (.prefix (TransitionMachine.compilePrefix indexing
        (TransitionMachine.transitionPlan indexing machineProgram).prefix).entry)),
        TermMachine.initialState, tapes base S remaining snapshot⟩) =
      some ⟨exit, TermMachine.initialState,
        preparedTapes base S remaining snapshot (tokens indexing machineProgram S snapshot)⟩ := by
  let input := termInput S snapshot
  let plan := TransitionMachine.transitionPlan indexing machineProgram
  have hv : TransitionMachine.Valid indexing plan input := by
    simpa [TransitionMachine.Valid, plan, TransitionMachine.transitionPlan, input, termInput] using valid
  have sourceTrace := TransitionMachine.fullTrace indexing plan input hv
    (fun tape => tapes base S remaining snapshot (termPorts tape))
    (termFrame base S remaining snapshot)
  have placed := ForestPlacement.trace termPorts labels exit (tapes base S remaining snapshot)
    (TransitionMachine.program indexing plan) target code
    (TransitionMachine.steps indexing plan input) _ _ sourceTrace
  simp only [ForestPlacement.configuration, ForestPlacement.placedLabel,
    ForestPlacement.fill_self] at placed
  rw [TransitionMachine.transition_outputTokens, place_emitTapes] at placed
  simpa only [emitSteps, tokens, ProducerInvariant.transitionTokens, input, termInput, plan]
    using placed

abbrev Label (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) :=
  Unit ⊕ (TransitionMachine.Label indexing
    (TransitionMachine.transitionPlan indexing machineProgram) ⊕ ForestStage.Label)

def entry (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) : Label indexing machineProgram := .inl ()

def emitLabel (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ)
    (label : TransitionMachine.Label indexing (TransitionMachine.transitionPlan indexing machineProgram)) :
    Label indexing machineProgram := .inr (.inl label)

def lowerLabel (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (label : ForestStage.Label) :
    Label indexing machineProgram := .inr (.inr label)

noncomputable def emitEntry (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) : Label indexing machineProgram :=
  emitLabel indexing machineProgram (.prefix (TransitionMachine.compilePrefix indexing
    (TransitionMachine.transitionPlan indexing machineProgram).prefix).entry)

def countdownStatement {Caller : Type} (next : Caller) : TM2.Stmt Alphabet Caller State :=
  .peek (.inr .countdown) (fun _ head => (((), head.getD false), none))
    (.branch (fun state => state.1.2)
      (.pop (.inr .countdown) (fun _ _ => TermMachine.initialState) (.goto fun _ => next))
      (.pop (.inr .countdown) (fun _ _ => TermMachine.initialState) .halt))

noncomputable def program (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) :
    Label indexing machineProgram → TM2.Stmt Alphabet (Label indexing machineProgram) State
  | .inl _ => countdownStatement (emitEntry indexing machineProgram)
  | .inr (.inl label) => ForestPlacement.statement termPorts (emitLabel indexing machineProgram)
      (some (lowerLabel indexing machineProgram .reverseTokens))
      (TransitionMachine.program indexing (TransitionMachine.transitionPlan indexing machineProgram) label)
  | .inr (.inr label) => ForestStage.statement (σ := Unit) forestPorts
      (lowerLabel indexing machineProgram) (some (entry indexing machineProgram)) label

noncomputable def machine (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) : FinTM2 where
  K := Tape
  k₀ := .inr .raw
  k₁ := .inl .records
  Γ := Alphabet
  Λ := Label indexing machineProgram
  main := entry indexing machineProgram
  σ := State
  initialState := TermMachine.initialState
  m := program indexing machineProgram

theorem guardZero (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (base : Tape → List Bool)
    (S : Nat) (snapshot : ProducerInvariant.Snapshot) :
    (advance (TM2.step (program indexing machineProgram)))^[1]
      (some ⟨some (entry indexing machineProgram), TermMachine.initialState, tapes base S 0 snapshot⟩) =
      some ⟨none, TermMachine.initialState, finishTapes base S snapshot⟩ := by
  change some (TM2.stepAux (program indexing machineProgram (entry indexing machineProgram))
    TermMachine.initialState (tapes base S 0 snapshot)) = _
  simp [program, entry, countdownStatement, TM2.stepAux, tapes, encodeWord, finishTapes]

theorem guardSucc (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (base : Tape → List Bool)
    (S remaining : Nat) (snapshot : ProducerInvariant.Snapshot) :
    (advance (TM2.step (program indexing machineProgram)))^[1]
      (some ⟨some (entry indexing machineProgram), TermMachine.initialState,
        tapes base S (remaining + 1) snapshot⟩) =
      some ⟨some (emitEntry indexing machineProgram), TermMachine.initialState,
        tapes base S remaining snapshot⟩ := by
  change some (TM2.stepAux (program indexing machineProgram (entry indexing machineProgram))
    TermMachine.initialState (tapes base S (remaining + 1) snapshot)) = _
  simp only [program, entry, countdownStatement, TM2.stepAux]
  have hhead : (tapes base S (remaining + 1) snapshot (.inr .countdown)).head? = some true := by
    simp [tapes, encodeWord, List.replicate_succ]
  rw [hhead]
  simpa only [Option.getD_some, Bool.cond_true] using
    congrArg (fun stack => some (TM2.Cfg.mk (some (emitEntry indexing machineProgram))
      TermMachine.initialState stack)) (tapes_countdown_tail base S remaining snapshot)

variable {inputs : Nat}

noncomputable def stageGates (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (S : Nat)
    (frame : CircuitBatch.Frame inputs (indexing.width S + 1)) : List Gate :=
  Batch.gates (fun i => (frame.wires i).val) (ProducerInvariant.next frame)
    (List.ofFn (ProducerInvariant.stepExpressions indexing machineProgram S))

noncomputable def lowerSteps (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (S : Nat)
    (frame : CircuitBatch.Frame inputs (indexing.width S + 1)) : Nat :=
  ForestStage.steps (tokens indexing machineProgram S (ProducerInvariant.snapshot frame))
    (ProducerInvariant.next frame)
    (ProducerInvariant.rootValues
      (frame.step (ProducerInvariant.stepExpressions indexing machineProgram S))).reverse
    (stageGates indexing machineProgram S frame) (encodeWords (ProducerInvariant.rootValues frame))

noncomputable def stageSteps (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (S : Nat)
    (frame : CircuitBatch.Frame inputs (indexing.width S + 1)) : Nat :=
  emitSteps indexing machineProgram S (ProducerInvariant.snapshot frame) +
    lowerSteps indexing machineProgram S frame

noncomputable def steps (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (S : Nat) :
    CircuitBatch.Frame inputs (indexing.width S + 1) → Nat → Nat
  | _, 0 => 1
  | frame, remaining + 1 => 1 + stageSteps indexing machineProgram S frame +
      steps indexing machineProgram S
        (frame.step (ProducerInvariant.stepExpressions indexing machineProgram S)) remaining

private theorem chain {A : Type*} {f : A → A} {x y z : A} {n m : Nat}
    (first : f^[n] x = y) (second : f^[m] y = z) : f^[n + m] x = z := by
  rw [Nat.add_comm n m, Function.iterate_add_apply, first, second]

theorem place_forest_initial (base : Tape → List Bool) (S remaining : Nat)
    (snapshot : ProducerInvariant.Snapshot) (ts : List PostfixModel.Token) :
    ForestPlacement.fill forestPorts (tapes base S remaining snapshot)
      (ForestStage.initialLocal snapshot.current ts snapshot.reversedRecords
        (encodeWords snapshot.roots)) = preparedTapes base S remaining snapshot ts := by
  rw [fill_forest]
  funext tape
  cases tape with
  | inl tape =>
    cases tape with
    | lower tape => cases tape <;> simp [ForestStage.initialLocal, preparedTapes, tapes]
    | tokens => simp [ForestStage.initialLocal, preparedTapes]
    | records => simp [ForestStage.initialLocal, preparedTapes, tapes]
    | rootTable => simp [ForestStage.initialLocal, preparedTapes, tapes]
  | inr tape => cases tape <;> simp [preparedTapes, tapes]

theorem place_forest_final {oldWidth newWidth : Nat}
    (base : Tape → List Bool) (S remaining : Nat) (frame : Frame inputs oldWidth)
    (es : Fin newWidth → Expr (Fin oldWidth)) :
    ForestPlacement.fill forestPorts (tapes base S remaining (ProducerInvariant.snapshot frame))
      (ForestStage.finalLocal (ProducerInvariant.next (frame.step es))
        (ProducerInvariant.rootValues (frame.step es)).reverse
        (recordsBits (gateRecords
          (ProducerInvariant.next frame)
          (Batch.gates (fun i => (frame.wires i).val) (ProducerInvariant.next frame) (List.ofFn es))))
        (ProducerInvariant.snapshot frame).reversedRecords) =
      tapes base S remaining (ProducerInvariant.snapshot (frame.step es)) := by
  have hr := congrArg List.reverse (ProducerInvariant.recordBits_step frame es)
  rw [List.reverse_append] at hr
  rw [fill_forest]
  funext tape
  cases tape with
  | inl tape =>
    cases tape with
    | lower tape => cases tape <;> rfl
    | tokens => rfl
    | rootTable => simp only [ForestStage.finalLocal, List.reverse_reverse]; rfl
    | records => exact hr.symm
  | inr tape => cases tape <;> rfl

theorem stageTrace (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (base : Tape → List Bool)
    (S remaining : Nat) (frame : Frame inputs (indexing.width S + 1)) :
    (advance (TM2.step (program indexing machineProgram)))^[
        stageSteps indexing machineProgram S frame]
      (some ⟨some (emitEntry indexing machineProgram), TermMachine.initialState,
        tapes base S remaining (ProducerInvariant.snapshot frame)⟩) =
      some ⟨some (entry indexing machineProgram), TermMachine.initialState,
        tapes base S remaining (ProducerInvariant.snapshot
          (frame.step (ProducerInvariant.stepExpressions indexing machineProgram S)))⟩ := by
  let es := ProducerInvariant.stepExpressions indexing machineProgram S
  have emitted := emitTraceAt indexing machineProgram (emitLabel indexing machineProgram)
    (some (lowerLabel indexing machineProgram .reverseTokens)) (program indexing machineProgram)
    (fun _ => rfl) base S remaining (ProducerInvariant.snapshot frame)
    (by simp only [ProducerInvariant.snapshot, List.length_ofFn]; exact le_rfl)
  have compiled := ForestStage.traceAt (σ := Unit) forestPorts (lowerLabel indexing machineProgram)
    (some (entry indexing machineProgram)) (program indexing machineProgram) (fun _ => rfl)
    (tapes base S remaining (ProducerInvariant.snapshot frame)) ((), false)
    (tokens indexing machineProgram S (ProducerInvariant.snapshot frame))
    (ProducerInvariant.next frame) (ProducerInvariant.next (frame.step es))
    (ProducerInvariant.rootValues (frame.step es)).reverse (stageGates indexing machineProgram S frame)
    (ProducerInvariant.snapshot frame).reversedRecords (encodeWords (ProducerInvariant.rootValues frame))
    (ProducerInvariant.compile_transitionTokens indexing machineProgram S frame)
  have initial := place_forest_initial base S remaining (ProducerInvariant.snapshot frame)
    (tokens indexing machineProgram S (ProducerInvariant.snapshot frame))
  change ForestPlacement.fill forestPorts (tapes base S remaining (ProducerInvariant.snapshot frame))
      (ForestStage.initialLocal (ProducerInvariant.next frame)
        (tokens indexing machineProgram S (ProducerInvariant.snapshot frame))
        (ProducerInvariant.snapshot frame).reversedRecords (encodeWords (ProducerInvariant.rootValues frame))) = _ at initial
  rw [initial] at compiled
  have final := place_forest_final base S remaining frame es
  change ForestPlacement.fill forestPorts (tapes base S remaining (ProducerInvariant.snapshot frame))
      (ForestStage.finalLocal (ProducerInvariant.next (frame.step es))
        (ProducerInvariant.rootValues (frame.step es)).reverse
        (recordsBits (gateRecords (ProducerInvariant.next frame) (stageGates indexing machineProgram S frame)))
        (ProducerInvariant.snapshot frame).reversedRecords) = _ at final
  rw [final] at compiled
  simpa only [stageSteps, lowerSteps, emitEntry, es, TermMachine.initialState]
    using chain emitted compiled

theorem repeatTrace (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (base : Tape → List Bool)
    (S : Nat) (frame : Frame inputs (indexing.width S + 1)) (remaining : Nat) :
    (advance (TM2.step (program indexing machineProgram)))^[steps indexing machineProgram S frame remaining]
      (some ⟨some (entry indexing machineProgram), TermMachine.initialState,
        tapes base S remaining (ProducerInvariant.snapshot frame)⟩) =
      some ⟨none, TermMachine.initialState, finishTapes base S (ProducerInvariant.snapshot
        (frame.repeat (ProducerInvariant.stepExpressions indexing machineProgram S) remaining))⟩ := by
  induction remaining generalizing frame with
  | zero => exact guardZero indexing machineProgram base S (ProducerInvariant.snapshot frame)
  | succ remaining ih =>
    have first := chain (guardSucc indexing machineProgram base S remaining (ProducerInvariant.snapshot frame))
      (stageTrace indexing machineProgram base S remaining frame)
    have result := chain first (ih (frame.step (ProducerInvariant.stepExpressions indexing machineProgram S)))
    simpa only [steps, ProducerInvariant.step_repeat] using result

noncomputable def repeatInTime (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (base : Tape → List Bool)
    (S : Nat) (frame : Frame inputs (indexing.width S + 1)) (remaining : Nat) :
    StateTransition.EvalsToInTime (machine indexing machineProgram).step
      ⟨some (entry indexing machineProgram), TermMachine.initialState,
        tapes base S remaining (ProducerInvariant.snapshot frame)⟩
      (some ⟨none, TermMachine.initialState, finishTapes base S (ProducerInvariant.snapshot
        (frame.repeat (ProducerInvariant.stepExpressions indexing machineProgram S) remaining))⟩)
      (steps indexing machineProgram S frame remaining) where
  steps := steps indexing machineProgram S frame remaining
  evals_in_steps := repeatTrace indexing machineProgram base S frame remaining
  steps_le_m := le_rfl

theorem repeatTraceAt {Caller : Type} (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ)
    (labels : Label indexing machineProgram → Caller) (exit : Option Caller)
    (target : Caller → TM2.Stmt Alphabet Caller State)
    (code : ∀ label, target (labels label) =
      MachineSubroutine.statement labels exit (program indexing machineProgram label))
    (base : Tape → List Bool) (S : Nat)
    (frame : Frame inputs (indexing.width S + 1)) (remaining : Nat) :
    (advance (TM2.step target))^[steps indexing machineProgram S frame remaining]
      (some ⟨some (labels (entry indexing machineProgram)), TermMachine.initialState,
        tapes base S remaining (ProducerInvariant.snapshot frame)⟩) =
      some ⟨exit, TermMachine.initialState, finishTapes base S (ProducerInvariant.snapshot
        (frame.repeat (ProducerInvariant.stepExpressions indexing machineProgram S) remaining))⟩ := by
  simpa only [MachineSubroutine.configuration, MachineSubroutine.label] using
    MachineSubroutine.trace labels exit (program indexing machineProgram) target code
      (steps indexing machineProgram S frame remaining) _ _
      (repeatTrace indexing machineProgram base S frame remaining)

end Transition

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionIteration

end OAI
