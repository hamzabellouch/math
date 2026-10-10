import OAI.Computability.UniqueGames.Machines.MachineControlLemmas
import OAI.Computability.UniqueGames.Machines.Runtime

namespace OAI

section

/-!
Execution transport and polynomial budget arithmetic for genuine TM2 sequential
composition. These lemmas preserve actual transition witnesses. The four-phase
lemma requires all phases to be executions of the same combined program; it is
not a replacement for constructing that program and proving its tape handoffs.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineComposition

def advance {σ : Type} (step : σ → Option σ) (state : Option σ) : Option σ :=
  state.bind step

@[simp] theorem advance_none {σ : Type} (step : σ → Option σ) :
    advance step none = none := rfl

@[simp] theorem advance_some {σ : Type} (step : σ → Option σ) (state : σ) :
    advance step (some state) = step state := rfl

@[simp] theorem advance_iterate_none {σ : Type} (step : σ → Option σ) (n : Nat) :
    (advance step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, advance_none]

theorem liftSuccessfulTrace {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    (n : Nat) (start finish : σ)
    (trace : (advance source)^[n] (some start) = some finish) :
    (advance target)^[n] (some (embed start)) = some (embed finish) := by
  induction n generalizing start with
  | zero =>
      have same := Option.some.inj trace
      cases same
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at trace ⊢
      change (advance source)^[n] (source start) = some finish at trace
      change (advance target)^[n] (target (embed start)) = some (embed finish)
      cases firstStep : source start with
      | none =>
          rw [firstStep, advance_iterate_none] at trace
          contradiction
      | some intermediate =>
          rw [firstStep] at trace
          rw [simulation start intermediate firstStep]
          exact ih intermediate trace

def liftExecutionInTime {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime source start (some finish) budget) :
    StateTransition.EvalsToInTime target (embed start) (some (embed finish)) budget where
  steps := execution.steps
  evals_in_steps := by
    have sourceTrace := execution.evals_in_steps
    change (advance source)^[execution.steps] (some start) = some finish at sourceTrace
    change (advance target)^[execution.steps] (some (embed start)) = some (embed finish)
    exact liftSuccessfulTrace source target embed simulation execution.steps start finish sourceTrace
  steps_le_m := execution.steps_le_m

@[simp] theorem liftExecutionInTime_steps {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime source start (some finish) budget) :
    (liftExecutionInTime source target embed simulation execution).steps = execution.steps := rfl

/-- The checked disjoint-stack embedding transports a complete successful run
with no additional transitions, including its final jump to a bridge label. -/
def embeddedExecution {K E Λ Λextra σ τ : Type} {Γ : K → Type} {Δ : E → Type}
    [DecidableEq K] [DecidableEq E]
    (haltTarget : Option (Λ ⊕ Λextra)) (extraState : τ)
    (extraTapes : ∀ e, List (Δ e))
    (source : Λ → Turing.TM2.Stmt Γ Λ σ)
    (extra : Λextra → Turing.TM2.Stmt (MachineEmbedding.Alphabet Γ Δ)
      (Λ ⊕ Λextra) (σ × τ))
    {start finish : Turing.TM2.Cfg Γ Λ σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (Turing.TM2.step source)
      start (some finish) budget) :
    StateTransition.EvalsToInTime (Turing.TM2.step (MachineEmbedding.program haltTarget source extra))
      (MachineEmbedding.configuration haltTarget extraState extraTapes start)
      (some (MachineEmbedding.configuration haltTarget extraState extraTapes finish)) budget :=
  liftExecutionInTime (Turing.TM2.step source)
    (Turing.TM2.step (MachineEmbedding.program haltTarget source extra))
    (MachineEmbedding.configuration haltTarget extraState extraTapes)
    (MachineEmbedding.step_simulation haltTarget extraState extraTapes source extra) execution

theorem natPolynomial_eval_mono (p : Polynomial Nat) {a b : Nat} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial degree coefficient =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left h degree)

/-- Two reversal transfers each consume `intermediateLength + 1` transitions. -/
noncomputable def compositionPolynomial (first second intermediate : Polynomial Nat) : Polynomial Nat :=
  first + Polynomial.C 2 * (intermediate + 1) + second.comp intermediate

theorem compositionBudget_le (first second intermediate : Polynomial Nat)
    (inputLength intermediateLength : Nat)
    (intermediateBound : intermediateLength ≤ intermediate.eval inputLength) :
    first.eval inputLength + 2 * (intermediateLength + 1) + second.eval intermediateLength ≤
      (compositionPolynomial first second intermediate).eval inputLength := by
  have secondBound := natPolynomial_eval_mono second intermediateBound
  have transferBound := Nat.mul_le_mul_left 2 (Nat.add_le_add_right intermediateBound 1)
  simp only [compositionPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_comp]
  omega

def fourPhaseExecution {σ : Type} (step : σ → Option σ)
    (start afterFirst afterTransfer₁ afterTransfer₂ : σ) (finish : Option σ)
    (first second intermediate : Polynomial Nat) (inputLength intermediateLength : Nat)
    (intermediateBound : intermediateLength ≤ intermediate.eval inputLength)
    (runFirst : StateTransition.EvalsToInTime step start (some afterFirst) (first.eval inputLength))
    (transfer₁ : StateTransition.EvalsToInTime step afterFirst (some afterTransfer₁)
      (intermediateLength + 1))
    (transfer₂ : StateTransition.EvalsToInTime step afterTransfer₁ (some afterTransfer₂)
      (intermediateLength + 1))
    (runSecond : StateTransition.EvalsToInTime step afterTransfer₂ finish
      (second.eval intermediateLength)) :
    StateTransition.EvalsToInTime step start finish
      ((compositionPolynomial first second intermediate).eval inputLength) := by
  let firstTwo := StateTransition.EvalsToInTime.trans step _ _ start afterFirst
    (some afterTransfer₁) runFirst transfer₁
  let firstThree := StateTransition.EvalsToInTime.trans step _ _ start afterTransfer₁
    (some afterTransfer₂) firstTwo transfer₂
  let allFour := StateTransition.EvalsToInTime.trans step _ _ start afterTransfer₂
    finish firstThree runSecond
  refine {
    toEvalsTo := allFour.toEvalsTo
    steps_le_m := Nat.le_trans allFour.steps_le_m ?_
  }
  have bounded := compositionBudget_le first second intermediate inputLength intermediateLength
    intermediateBound
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineComposition

end

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineAlphabetTransport

open Turing.TM2

variable {K Λ σ : Type} {Γ Δ : K → Type}

def tapes (h : Γ = Δ) (source : ∀ k, List (Γ k)) : ∀ k, List (Δ k) := h ▸ source

def statement (h : Γ = Δ) (source : Stmt Γ Λ σ) : Stmt Δ Λ σ := h ▸ source

def configuration (h : Γ = Δ) (source : Cfg Γ Λ σ) : Cfg Δ Λ σ := h ▸ source

def program (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ) : Λ → Stmt Δ Λ σ :=
  fun label => statement h (source label)

abbrev castStatement (h : Γ = Δ) (source : Stmt Γ Λ σ) : Stmt Δ Λ σ := statement h source
abbrev castConfiguration (h : Γ = Δ) (source : Cfg Γ Λ σ) : Cfg Δ Λ σ := configuration h source
abbrev castProgram (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ) : Λ → Stmt Δ Λ σ := program h source

@[simp] theorem tapes_rfl (source : ∀ k, List (Γ k)) : tapes rfl source = source := rfl
@[simp] theorem statement_rfl (source : Stmt Γ Λ σ) : statement rfl source = source := rfl
@[simp] theorem configuration_rfl (source : Cfg Γ Λ σ) : configuration rfl source = source := rfl
@[simp] theorem program_rfl (source : Λ → Stmt Γ Λ σ) : program rfl source = source := rfl

@[simp] theorem program_apply (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ) (label : Λ) :
    program h source label = statement h (source label) := rfl

@[simp] theorem statement_roundtrip (h : Γ = Δ) (source : Stmt Δ Λ σ) :
    statement h (statement h.symm source) = source := by cases h; rfl

@[simp] theorem statement_symm_roundtrip (h : Γ = Δ) (source : Stmt Γ Λ σ) :
    statement h.symm (statement h source) = source := by cases h; rfl

@[simp] theorem configuration_roundtrip (h : Γ = Δ) (source : Cfg Δ Λ σ) :
    configuration h (configuration h.symm source) = source := by cases h; rfl

@[simp] theorem configuration_symm_roundtrip (h : Γ = Δ) (source : Cfg Γ Λ σ) :
    configuration h.symm (configuration h source) = source := by cases h; rfl

@[simp] theorem program_roundtrip (h : Γ = Δ) (source : Λ → Stmt Δ Λ σ) :
    program h (program h.symm source) = source := by cases h; rfl

@[simp] theorem program_symm_roundtrip (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ) :
    program h.symm (program h source) = source := by cases h; rfl

@[simp] theorem tapes_roundtrip (h : Γ = Δ) (source : ∀ k, List (Δ k)) :
    tapes h (tapes h.symm source) = source := by cases h; rfl

@[simp] theorem tapes_symm_roundtrip (h : Γ = Δ) (source : ∀ k, List (Γ k)) :
    tapes h.symm (tapes h source) = source := by cases h; rfl

@[simp] theorem configuration_label (h : Γ = Δ) (source : Cfg Γ Λ σ) :
    (configuration h source).l = source.l := by cases h; rfl

@[simp] theorem configuration_state (h : Γ = Δ) (source : Cfg Γ Λ σ) :
    (configuration h source).var = source.var := by cases h; rfl

@[simp] theorem configuration_tapes (h : Γ = Δ) (source : Cfg Γ Λ σ) :
    (configuration h source).stk = tapes h source.stk := by cases h; rfl

@[simp] theorem configuration_mk (h : Γ = Δ) (label : Option Λ) (state : σ)
    (source : ∀ k, List (Γ k)) :
    configuration h ⟨label, state, source⟩ = ⟨label, state, tapes h source⟩ := by cases h; rfl

@[simp] theorem map_configuration_rfl (source : Option (Cfg Γ Λ σ)) :
    source.map (configuration (rfl : Γ = Γ)) = source := by cases source <;> rfl

variable [DecidableEq K]

theorem stepAux_simulation (h : Γ = Δ) (source : Stmt Γ Λ σ) (state : σ)
    (sourceTapes : ∀ k, List (Γ k)) :
    stepAux (statement h source) state (tapes h sourceTapes) =
      configuration h (stepAux source state sourceTapes) := by cases h; rfl

theorem step_simulation (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ) (start : Cfg Γ Λ σ) :
    step (program h source) (configuration h start) =
      (step source start).map (configuration h) := by
  cases h
  simp only [program_rfl, configuration_rfl, map_configuration_rfl]

/-- Exact conjugacy of every finite trace, including a `none` endpoint. -/
theorem trace_transport (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    (n : Nat) (start : Option (Cfg Γ Λ σ)) :
    (MachineComposition.advance (step (program h source)))^[n]
      (start.map (configuration h)) =
      ((MachineComposition.advance (step source))^[n] start).map (configuration h) := by
  cases h
  simp only [program_rfl, map_configuration_rfl]

theorem successfulTrace (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    (n : Nat) (start finish : Cfg Γ Λ σ)
    (trace : (MachineComposition.advance (step source))^[n] (some start) = some finish) :
    (MachineComposition.advance (step (program h source)))^[n]
      (some (configuration h start)) = some (configuration h finish) := by
  have transported := trace_transport h source n (some start)
  simpa only [Option.map_some, trace] using transported

def executionInTime (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (step source) start finish budget) :
    StateTransition.EvalsToInTime (step (program h source)) (configuration h start)
      (finish.map (configuration h)) budget where
  steps := execution.steps
  evals_in_steps := by
    cases h
    simpa only [program_rfl, configuration_rfl, map_configuration_rfl]
      using execution.evals_in_steps
  steps_le_m := execution.steps_le_m

@[simp] theorem executionInTime_steps (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (step source) start finish budget) :
    (executionInTime h source execution).steps = execution.steps := rfl

def successfulExecutionInTime (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    {start finish : Cfg Γ Λ σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (step source) start (some finish) budget) :
    StateTransition.EvalsToInTime (step (program h source)) (configuration h start)
      (some (configuration h finish)) budget := executionInTime h source execution

@[simp] theorem successfulExecutionInTime_steps (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    {start finish : Cfg Γ Λ σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (step source) start (some finish) budget) :
    (successfulExecutionInTime h source execution).steps = execution.steps := rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineAlphabetTransport

end

section

/-! Static concatenation of finitely many concrete subroutines on common
tapes. The labels are a finite disjoint sum; no runtime instruction counter
or list is placed in the machine state. The simulation theorem composes the
actual local traces with exactly their summed transition counts. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFiniteSequence

open Turing MachineComposition

variable {Command : Type} (LocalLabel : Command → Type)

def Label : List Command → Type
  | [] => Empty
  | command :: commands => LocalLabel command ⊕ Label commands

instance labelFintype [∀ command, Fintype (LocalLabel command)]
    (commands : List Command) : Fintype (Label LocalLabel commands) := by
  induction commands with
  | nil => exact inferInstanceAs (Fintype Empty)
  | cons command commands ih =>
      letI := ih
      exact inferInstanceAs (Fintype (LocalLabel command ⊕ Label LocalLabel commands))

instance labelDecidableEq [∀ command, DecidableEq (LocalLabel command)]
    (commands : List Command) : DecidableEq (Label LocalLabel commands) := by
  induction commands with
  | nil => exact inferInstanceAs (DecidableEq Empty)
  | cons command commands ih =>
      letI := ih
      exact inferInstanceAs (DecidableEq (LocalLabel command ⊕ Label LocalLabel commands))

variable (main : ∀ command, LocalLabel command)
variable {K Λ σ : Type} {Γ : K → Type}

def entry : (commands : List Command) → (Label LocalLabel commands → Λ) → Option Λ → Option Λ
  | [], _, exit => exit
  | command :: _, labels, _ => some (labels (.inl (main command)))

variable (localInstruction : ∀ command, (LocalLabel command → Λ) → Option Λ →
  LocalLabel command → TM2.Stmt Γ Λ σ)

def instruction : (commands : List Command) → (Label LocalLabel commands → Λ) → Option Λ →
    Label LocalLabel commands → TM2.Stmt Γ Λ σ
  | [], _, _, label => nomatch label
  | command :: commands, labels, exit, .inl label =>
      localInstruction command (fun l => labels (.inl l))
        (entry LocalLabel main commands (fun l => labels (.inr l)) exit) label
  | _ :: commands, labels, exit, .inr label =>
      instruction commands (fun l => labels (.inr l)) exit label

variable {Data : Type} (result : Command → Data → Data) (cost : Command → Data → Nat)

def resultOf : List Command → Data → Data
  | [], data => data
  | command :: commands, data => resultOf commands (result command data)

def steps : List Command → Data → Nat
  | [], _ => 0
  | command :: commands, data => cost command data + steps commands (result command data)

variable [DecidableEq K]

/-- This generic composition lemma retains the local execution obligations.
Concrete callers discharge them with the rotor, comparison and row programs. -/
theorem trace (program : Λ → TM2.Stmt Γ Λ σ)
    (invariant : Data → Prop) (state : Data → σ) (tapes : Data → ∀ k, List (Γ k))
    (commands : List Command)
    (localInvariant : ∀ command ∈ commands, ∀ data, invariant data →
      invariant (result command data))
    (localTrace : ∀ command ∈ commands, ∀ (labels : LocalLabel command → Λ) (exit : Option Λ),
      (∀ l, program (labels l) = localInstruction command labels exit l) →
      ∀ data, invariant data →
      (advance (TM2.step program))^[cost command data]
        (some ⟨some (labels (main command)), state data, tapes data⟩) =
      some ⟨exit, state (result command data), tapes (result command data)⟩)
    (labels : Label LocalLabel commands → Λ) (exit : Option Λ)
    (atLabels : ∀ l, program (labels l) =
      instruction LocalLabel main localInstruction commands labels exit l)
    (data : Data) (valid : invariant data) :
    (advance (TM2.step program))^[steps result cost commands data]
      (some ⟨entry LocalLabel main commands labels exit, state data, tapes data⟩) =
    some ⟨exit, state (resultOf result commands data), tapes (resultOf result commands data)⟩ := by
  induction commands generalizing data with
  | nil => rfl
  | cons command commands ih =>
      have firstRun := localTrace command (by simp)
        (fun l => labels (.inl l))
        (entry LocalLabel main commands (fun l => labels (.inr l)) exit)
        (fun l => atLabels (.inl l)) data valid
      have nextValid := localInvariant command (by simp) data valid
      have tailRun := ih
        (fun c hc d hd => localInvariant c (by simp [hc]) d hd)
        (fun c hc => localTrace c (by simp [hc]))
        (fun l => labels (.inr l)) (fun l => atLabels (.inr l))
        (result command data) nextValid
      rw [steps, Nat.add_comm, Function.iterate_add_apply]
      change (advance (TM2.step program))^[steps result cost commands (result command data)]
        ((advance (TM2.step program))^[cost command data]
          (some ⟨some (labels (.inl (main command))), state data, tapes data⟩)) = _
      rw [firstRun]
      exact tailRun

end UniqueGamesTheorem.Foundations.Complexity.MachineFiniteSequence

end

section

/-!
# An actual finite machine for a fixed-size Boolean block map

The program parameters `N`, `M`, and `F` are fixed. The local register has
exactly `N` bits. A syntactic chain of `N` pops fills that register, and a
syntactic chain of `M` pushes writes `F` of the register. No instruction
applies `F` to an unbounded word. An arbitrary ambient state is preserved,
and the local register is reset before the optional continuation.

TM2 executes a whole finite statement in one transition. The push bound
below separately records the exact `M` pushes in this statement.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFixedBlockMap

open Turing

abbrev Buffer (N : Nat) := Fin N → Bool

def emptyBuffer (N : Nat) : Buffer N := fun _ => false

section Chains

variable {K Λ σ : Type} {N : Nat}

def readSlots (src : K) : List (Fin N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)
  | [], next => next
  | i :: slots, next =>
      .pop src (fun state head =>
        (state.1, Function.update state.2 i (head.getD false)))
        (readSlots src slots next)

/-- Proof-level description of the finite register updates. -/
def fill (slots : List (Fin N)) (bits buffer : Buffer N) : Buffer N :=
  slots.foldl (fun buffer i => Function.update buffer i (bits i)) buffer

theorem fill_apply (slots : List (Fin N)) (bits buffer : Buffer N) (i : Fin N) :
    fill slots bits buffer i = if i ∈ slots then bits i else buffer i := by
  induction slots generalizing buffer with
  | nil => simp [fill]
  | cons j slots ih =>
      change fill slots bits (Function.update buffer j (bits j)) i = _
      rw [ih]
      by_cases hm : i ∈ slots
      · simp [hm]
      · by_cases he : i = j <;> simp [hm, he]

@[simp] theorem fill_all (bits buffer : Buffer N) :
    fill (List.ofFn id) bits buffer = bits := by
  funext i
  simp [fill_apply, List.mem_ofFn]

variable [DecidableEq K]

/-- The input symbols are physically popped; the remaining suffix is exact. -/
theorem stepAux_readSlots (src : K) (slots : List (Fin N))
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (ambient : σ) (bits buffer : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool) :
    TM2.stepAux (readSlots src slots next) (ambient, buffer)
        (Function.update tapes src (slots.map bits ++ suffix)) =
      TM2.stepAux next (ambient, fill slots bits buffer)
        (Function.update tapes src suffix) := by
  induction slots generalizing buffer tapes with
  | nil => simp [readSlots, fill]
  | cons i slots ih =>
      simpa only [readSlots, List.map_cons, List.cons_append, TM2.stepAux,
        Function.update_self, List.head?_cons, Option.getD_some, List.tail_cons,
        Function.update_idem, fill, List.foldl_cons] using
        ih (Function.update buffer i (bits i)) tapes

theorem stepAux_readAll (src : K)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool) (hinput : tapes src = List.ofFn bits ++ suffix) :
    TM2.stepAux (readSlots src (List.ofFn id) next) state tapes =
      TM2.stepAux next (state.1, bits) (Function.update tapes src suffix) := by
  have h := stepAux_readSlots src (List.ofFn id) next state.1 bits state.2 tapes suffix
  have hin : Function.update tapes src ((List.ofFn id).map bits ++ suffix) = tapes := by
    simpa only [List.map_ofFn, Function.comp_id, ← hinput] using
      Function.update_eq_self src tapes
  rw [hin, fill_all] at h
  exact h

omit [DecidableEq K] in
theorem statementPushBound_readSlots (src : K) (slots : List (Fin N))
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)) :
    Runtime.statementPushBound (readSlots src slots next) =
      Runtime.statementPushBound next := by
  induction slots with
  | nil => rfl
  | cons i slots ih => exact ih

/-- The slot list is a fixed part of the syntax; each instruction reads only
the finite internal state. Push order is reversed on the stack. -/
def writeSlots {M : Nat} (dst : K) (emit : σ → Buffer M) : List (Fin M) →
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | [], next => next
  | i :: slots, next => .push dst (fun state => emit state i) (writeSlots dst emit slots next)

theorem stepAux_writeSlots {M : Nat} (dst : K) (emit : σ → Buffer M)
    (slots : List (Fin M)) (next : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (writeSlots dst emit slots next) state tapes =
      TM2.stepAux next state
        (Function.update tapes dst ((slots.map (emit state)).reverse ++ tapes dst)) := by
  induction slots generalizing tapes with
  | nil => simp [writeSlots]
  | cons i slots ih =>
      simp only [writeSlots, TM2.stepAux]
      rw [ih]
      simp only [Function.update_self, Function.update_idem, List.map_cons,
        List.reverse_cons, List.append_assoc, List.singleton_append]

omit [DecidableEq K] in
theorem statementPushBound_writeSlots {M : Nat} (dst : K) (emit : σ → Buffer M)
    (slots : List (Fin M)) (next : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    Runtime.statementPushBound (writeSlots dst emit slots next) =
      slots.length + Runtime.statementPushBound next := by
  induction slots with
  | nil => simp [writeSlots]
  | cons i slots ih =>
      simp only [writeSlots, Runtime.statementPushBound, ih, List.length_cons]
      omega

end Chains

section Block

variable {K Λ σ : Type} {N M : Nat}

/-- Read a fixed block, write its fixed finite transformation, reset the local
register, and execute the next finite statement. -/
def blockStmt (src dst : K) (F : Buffer N → Buffer M)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) :=
  readSlots src (List.ofFn id)
    (writeSlots dst (fun state => F state.2) (List.ofFn id).reverse
      (.load (fun state => (state.1, emptyBuffer N)) next))

def finishAt (exit : Option Λ) : TM2.Stmt (fun _ : K => Bool) Λ σ :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def blockMapAt (src dst : K) (F : Buffer N → Buffer M) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) :=
  blockStmt src dst F (finishAt exit)

theorem statementPushBound_blockStmt (src dst : K) (F : Buffer N → Buffer M)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)) :
    Runtime.statementPushBound (blockStmt src dst F next) =
      M + Runtime.statementPushBound next := by
  simp only [blockStmt, statementPushBound_readSlots, statementPushBound_writeSlots,
    Runtime.statementPushBound, List.length_reverse, List.length_ofFn]

theorem statementPushBound_blockMapAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ) :
    Runtime.statementPushBound (blockMapAt (σ := σ) src dst F exit) = M := by
  cases exit <;> simp [blockMapAt, statementPushBound_blockStmt, finishAt,
    Runtime.statementPushBound]

variable [DecidableEq K]

theorem stepAux_blockStmt (src dst : K) (F : Buffer N → Buffer M)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = List.ofFn bits ++ suffix) :
    TM2.stepAux (blockStmt src dst F next) state tapes =
      TM2.stepAux next (state.1, emptyBuffer N)
        (Function.update (Function.update tapes src suffix) dst
          (List.ofFn (F bits) ++ tapes dst)) := by
  unfold blockStmt
  rw [stepAux_readAll src _ state bits tapes suffix hinput, stepAux_writeSlots]
  simp only [List.map_reverse, List.map_ofFn, Function.comp_id, List.reverse_reverse,
    Function.update_of_ne (Ne.symm hne), TM2.stepAux]

/-- The suffix and all unmentioned tapes are preserved, and the local register
is reset, in the actual transition semantics. -/
theorem stepAux_blockMapAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ) (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = List.ofFn bits ++ suffix) :
    TM2.stepAux (blockMapAt src dst F exit) state tapes =
      { l := exit, var := (state.1, emptyBuffer N),
        stk := Function.update (Function.update tapes src suffix) dst
          (List.ofFn (F bits) ++ tapes dst) } := by
  rw [blockMapAt, stepAux_blockStmt src dst F _ hne bits suffix state tapes hinput]
  cases exit <;> rfl

/-- Placement in an arbitrary program gives one actual TM2 transition. -/
theorem step_blockMapAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (label : Λ) (hprogram : program label = blockMapAt src dst F exit)
    (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = List.ofFn bits ++ suffix) :
    TM2.step program { l := some label, var := state, stk := tapes } =
      some { l := exit
             var := (state.1, emptyBuffer N)
             stk := Function.update (Function.update tapes src suffix) dst
               (List.ofFn (F bits) ++ tapes dst) } := by
  simp only [TM2.step, hprogram,
    stepAux_blockMapAt src dst F exit hne bits suffix state tapes hinput]

end Block

/-- The fixed block map is also a concrete machine with two Boolean tapes and
a finite register, independently of any ambient placement. -/
def machine {N M : Nat} (F : Buffer N → Buffer M) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Unit × Buffer N
  initialState := ((), emptyBuffer N)
  m _ := blockMapAt false true F none

theorem machine_statementPushBound {N M : Nat} (F : Buffer N → Buffer M) :
    Runtime.statementPushBound ((machine F).m ()) = M :=
  statementPushBound_blockMapAt false true F none

end UniqueGamesTheorem.Foundations.Complexity.MachineFixedBlockMap

end

section

/-!
# Exact register-equivalence transport for finite-stack programs

The instruction translation reuses `MachineControl.statement` with unchanged
labels. An explicit register equivalence changes neither tapes nor labels.
The transition function, every iterated trace, and runtime witnesses are
transported in exactly the same number of transitions, including failed or
halted traces. No simulation premise is assumed.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineStateEquiv

open Turing.TM2

variable {K Λ σ τ : Type} {Γ : K → Type}

/-- Translate instructions using the checked recursive translator, keeping
every tape and destination label unchanged. -/
abbrev statement (e : σ ≃ τ) : Stmt Γ Λ σ → Stmt Γ Λ τ :=
  MachineControl.statement (id : Λ → Λ) e

/-- Translating every instruction back restores the original statement,
including its state-dependent instruction functions. -/
@[simp] theorem statement_symm_statement (e : σ ≃ τ) (q : Stmt Γ Λ σ) :
    statement e.symm (statement e q) = q := by
  induction q <;>
    simp_all only [statement, MachineControl.statement, Equiv.symm_symm,
      Equiv.symm_apply_apply, id_eq]

def configuration (e : σ ≃ τ) (c : Cfg Γ Λ σ) : Cfg Γ Λ τ :=
  ⟨c.l, e c.var, c.stk⟩

@[simp] theorem configuration_label (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    (configuration e c).l = c.l := rfl

@[simp] theorem configuration_state (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    (configuration e c).var = e c.var := rfl

@[simp] theorem configuration_tapes (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    (configuration e c).stk = c.stk := rfl

@[simp] theorem configuration_symm_configuration (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    configuration e.symm (configuration e c) = c := by
  cases c
  simp only [configuration, Equiv.symm_apply_apply]

@[simp] theorem configuration_configuration_symm (e : σ ≃ τ) (c : Cfg Γ Λ τ) :
    configuration e (configuration e.symm c) = c := by
  cases c
  simp only [configuration, Equiv.apply_symm_apply]

/-- This is a bijection on actual machine configurations, not just on states. -/
def configurationEquiv (e : σ ≃ τ) : Cfg Γ Λ σ ≃ Cfg Γ Λ τ where
  toFun := configuration e
  invFun := configuration e.symm
  left_inv := configuration_symm_configuration e
  right_inv := configuration_configuration_symm e

@[simp] theorem configurationEquiv_apply (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    configurationEquiv e c = configuration e c := rfl

@[simp] theorem control_configuration (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    MachineControl.configuration (id : Λ → Λ) e c = configuration e c := by
  cases c
  simp [MachineControl.configuration, configuration]

def program (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) : Λ → Stmt Γ Λ τ :=
  fun l => statement e (source l)

@[simp] theorem program_symm_program (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) :
    program e.symm (program e source) = source := by
  funext l
  exact statement_symm_statement e (source l)

/-- The register change does not alter the finite statement's push bound. -/
theorem statementPushBound (e : σ ≃ τ) (q : Stmt Γ Λ σ) :
    Runtime.statementPushBound (statement e q) = Runtime.statementPushBound q := by
  induction q <;>
    simp_all only [statement, MachineControl.statement, Runtime.statementPushBound]

/-- Exactly the same finite label set supports the translated statement. -/
theorem supportsStmt_iff (e : σ ≃ τ) (S : Finset Λ) (q : Stmt Γ Λ σ) :
    SupportsStmt S (statement e q) ↔ SupportsStmt S q := by
  induction q with
  | push k f next ih =>
      simpa only [statement, MachineControl.statement, SupportsStmt] using ih
  | peek k f next ih =>
      simpa only [statement, MachineControl.statement, SupportsStmt] using ih
  | pop k f next ih =>
      simpa only [statement, MachineControl.statement, SupportsStmt] using ih
  | load f next ih =>
      simpa only [statement, MachineControl.statement, SupportsStmt] using ih
  | branch f yes no ihYes ihNo =>
      simp only [statement, MachineControl.statement, SupportsStmt, ihYes, ihNo]
  | goto f =>
      change (∀ state : τ, f (e.symm state) ∈ S) ↔ ∀ state : σ, f state ∈ S
      constructor
      · intro h state
        simpa only [Equiv.symm_apply_apply] using h (e state)
      · intro h state
        exact h (e.symm state)
  | halt => rfl

theorem supports_iff [Inhabited Λ] (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    (S : Finset Λ) : Supports (program e source) S ↔ Supports source S := by
  simp only [Supports, program, supportsStmt_iff]

variable [DecidableEq K]

/-- The actual recursively interpreted statement commutes with the register
equivalence, with exactly the same tape updates. -/
theorem stepAux_transport (e : σ ≃ τ) (q : Stmt Γ Λ σ) (state : σ)
    (tapes : ∀ k, List (Γ k)) :
    stepAux (statement e q) (e state) tapes =
      configuration e (stepAux q state tapes) := by
  simpa only [statement, control_configuration] using
    MachineControl.stepAux_simulation (id : Λ → Λ) e q state tapes

theorem stepAux_transport_symm (e : σ ≃ τ) (q : Stmt Γ Λ σ) (state : τ)
    (tapes : ∀ k, List (Γ k)) :
    stepAux (statement e q) state tapes =
      configuration e (stepAux q (e.symm state) tapes) := by
  simpa only [Equiv.apply_symm_apply] using
    stepAux_transport e q (e.symm state) tapes

/-- Exact conjugacy also covers the halted configuration and the `none` step. -/
theorem step_transport (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) :
    step (program e source) (configuration e c) =
      (step source c).map (configuration e) := by
  cases c with
  | mk l state tapes =>
      cases l with
      | none => rfl
      | some l =>
          change some (stepAux (statement e (source l)) (e state) tapes) = _
          rw [stepAux_transport]
          rfl

theorem step_iff (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (a b : Cfg Γ Λ σ) :
    step (program e source) (configuration e a) = some (configuration e b) ↔
      step source a = some b := by
  rw [step_transport]
  change (step source a).map (configuration e) = (some b).map (configuration e) ↔ _
  constructor
  · intro h
    apply Option.map_injective (configurationEquiv e).injective
    change (step source a).map (configuration e) = (some b).map (configuration e)
    exact h
  · exact congrArg (Option.map (configuration e))

theorem advance_transport (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    (c : Option (Cfg Γ Λ σ)) :
    MachineComposition.advance (step (program e source)) (c.map (configuration e)) =
      (MachineComposition.advance (step source) c).map (configuration e) := by
  cases c with
  | none => rfl
  | some c => exact step_transport e source c

/-- Every intermediate configuration is transported at its original time
index. This includes traces whose option-valued result is `none`. -/
theorem iterate_transport (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (n : Nat)
    (c : Option (Cfg Γ Λ σ)) :
    (MachineComposition.advance (step (program e source)))^[n]
        (c.map (configuration e)) =
      ((MachineComposition.advance (step source))^[n] c).map (configuration e) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, advance_transport,
        Function.iterate_succ_apply']

/-- A successful running trace exists for exactly the same number of steps in
the translated and original program. -/
theorem trace_iff (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (n : Nat)
    (a b : Cfg Γ Λ σ) :
    (MachineComposition.advance (step (program e source)))^[n]
        (some (configuration e a)) = some (configuration e b) ↔
      (MachineComposition.advance (step source))^[n] (some a) = some b := by
  change (MachineComposition.advance (step (program e source)))^[n]
      ((some a).map (configuration e)) = (some b).map (configuration e) ↔ _
  rw [iterate_transport]
  constructor
  · intro h
    apply Option.map_injective (configurationEquiv e).injective
    change ((MachineComposition.advance (step source))^[n] (some a)).map (configuration e) =
      (some b).map (configuration e)
    exact h
  · exact congrArg (Option.map (configuration e))

theorem trace (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (n : Nat)
    (a b : Cfg Γ Λ σ)
    (run : (MachineComposition.advance (step source))^[n] (some a) = some b) :
    (MachineComposition.advance (step (program e source)))^[n]
      (some (configuration e a)) = some (configuration e b) :=
  (trace_iff e source n a b).2 run

/-- Transport an actual runtime witness without changing its step count or
budget; the final option may be either a configuration or `none`. -/
def execution (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step source) start finish budget) :
    StateTransition.EvalsToInTime (step (program e source))
      (configuration e start) (finish.map (configuration e)) budget where
  steps := run.steps
  evals_in_steps := by
    have h := run.evals_in_steps
    change (MachineComposition.advance (step source))^[run.steps] (some start) = finish at h
    change (MachineComposition.advance (step (program e source)))^[run.steps]
      ((some start).map (configuration e)) = finish.map (configuration e)
    rw [iterate_transport, h]
  steps_le_m := run.steps_le_m

@[simp] theorem execution_steps (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step source) start finish budget) :
    (execution e source run).steps = run.steps := rfl

/-- Conversely, a translated runtime witness determines the original witness
at exactly the same number of transitions. -/
def execution_reflect (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step (program e source))
      (configuration e start) (finish.map (configuration e)) budget) :
    StateTransition.EvalsToInTime (step source) start finish budget where
  steps := run.steps
  evals_in_steps := by
    change (MachineComposition.advance (step source))^[run.steps] (some start) = finish
    apply Option.map_injective (configurationEquiv e).injective
    change ((MachineComposition.advance (step source))^[run.steps] (some start)).map
      (configuration e) = finish.map (configuration e)
    rw [← iterate_transport]
    exact run.evals_in_steps
  steps_le_m := run.steps_le_m

@[simp] theorem execution_reflect_steps (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step (program e source))
      (configuration e start) (finish.map (configuration e)) budget) :
    (execution_reflect e source run).steps = run.steps := rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineStateEquiv

end

end OAI
