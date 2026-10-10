import OAI.Computability.PerfectCompleteness.Machines.AcceptanceStage
import OAI.Computability.PerfectCompleteness.Machines.CellsTokensAlignmentLemmas
import OAI.Computability.PerfectCompleteness.Machines.CircuitFinish
import OAI.Computability.PerfectCompleteness.Machines.InitializationStageLemmas
import OAI.Computability.PerfectCompleteness.Machines.ProducerBootstrapLemmas
import OAI.Computability.PerfectCompleteness.Machines.VerifierFront

namespace OAI


noncomputable section
namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.ProducerArena


open Turing

inductive Work
  | transition (tape : TransitionArena.Tape)
  | validity (index : Fin 7)
  | cells (index : Fin 9)
  | finish (tape : CircuitFinish.Tape)
  | bootstrap
  deriving DecidableEq, Fintype

abbrev Tape (V : NPVerifier) := VerifierFront.Tape V ⊕ Work
abbrev Alphabet (V : NPVerifier) (_ : Tape V) := Bool
abbrev State := TermMachine.State
abbrev initialState : State := TermMachine.initialState

def frontPorts (V : NPVerifier) : VerifierFront.Tape V ↪ Tape V :=
  ⟨Sum.inl, Sum.inl_injective⟩

def raw (V : NPVerifier) : Tape V := .inl (VerifierFront.raw V)
def framed (V : NPVerifier) : Tape V := .inl (VerifierFront.stream V)
def clock (V : NPVerifier) (c : ClockPreparation.Clock) : Tape V :=
  .inl (VerifierFront.clockTape V c)
def q (V : NPVerifier) : Tape V := clock V .witness
def capacity (V : NPVerifier) : Tape V := clock V .capacity
def countdown (V : NPVerifier) : Tape V := clock V .horizon
def freeInputs (V : NPVerifier) : Tape V := clock V .inputCount

def shared (V : NPVerifier) (t : ForestStage.Tape) : Tape V :=
  .inr (.transition (.inl t))
def current (V : NPVerifier) : Tape V := shared V (.lower .current)
def roots (V : NPVerifier) : Tape V := shared V .rootTable
def records (V : NPVerifier) : Tape V := shared V .records
def tokens (V : NPVerifier) : Tape V := shared V .tokens
def count (V : NPVerifier) : Tape V := shared V (.lower .remaining)
def cursor (V : NPVerifier) : Tape V := .inr (.transition (.inr .cursor))
def output (V : NPVerifier) : Tape V := .inr (.finish .output)

theorem clock_injective (V : NPVerifier) : Function.Injective (clock V) := by
  intro a b h
  have hs := (VerifierFront.clockSlots V).injective (Sum.inl.inj h)
  have ho := ClockPreparation.outputSlot_injective _ hs
  cases a <;> cases b <;> simp_all [ClockPreparation.clockOutput] <;> cases ho

@[simp] theorem clock_eq_iff (V : NPVerifier) (a b : ClockPreparation.Clock) :
    clock V a = clock V b ↔ a = b := (clock_injective V).eq_iff

@[simp] theorem clock_ne_raw (V : NPVerifier) (c : ClockPreparation.Clock) :
    clock V c ≠ raw V := by
  simp [clock, raw, VerifierFront.clockTape, VerifierFront.clockSlots, VerifierFront.raw]

@[simp] theorem raw_ne_clock (V : NPVerifier) (c : ClockPreparation.Clock) :
    raw V ≠ clock V c := (clock_ne_raw V c).symm

@[simp] theorem clock_ne_framed (V : NPVerifier) (c : ClockPreparation.Clock) :
    clock V c ≠ framed V := by
  simp [clock, framed, VerifierFront.clockTape, VerifierFront.clockSlots, VerifierFront.stream]

@[simp] theorem framed_ne_clock (V : NPVerifier) (c : ClockPreparation.Clock) :
    framed V ≠ clock V c := (clock_ne_framed V c).symm

@[simp] theorem raw_ne_framed (V : NPVerifier) : raw V ≠ framed V := by
  simp [raw, framed, VerifierFront.raw, VerifierFront.stream]

def transitionTape (V : NPVerifier) : TransitionArena.Tape → Tape V
  | .inr .raw => raw V
  | .inr .q => q V
  | .inr .capacity => capacity V
  | .inr .countdown => countdown V
  | t => .inr (.transition t)

def transitionPorts (V : NPVerifier) : TransitionArena.Tape ↪ Tape V where
  toFun := transitionTape V
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => simpa [transitionTape] using h
      | inr b =>
        cases b <;>
          simp_all [transitionTape, raw, q, capacity, countdown, clock]
    | inr a =>
      cases b with
      | inl b =>
        cases a <;>
          simp_all [transitionTape, raw, q, capacity, countdown, clock]
      | inr b =>
        cases a <;> cases b <;>
          simp_all [transitionTape, q, capacity, countdown, raw, clock,
            VerifierFront.raw, VerifierFront.clockTape, VerifierFront.clockSlots,
            ClockPreparation.clockOutput] <;>
          cases h

@[simp] theorem transitionPorts_apply (V : NPVerifier) (t : TransitionArena.Tape) :
    transitionPorts V t = transitionTape V t := rfl

def forestPorts (V : NPVerifier) : ForestStage.Tape ↪ Tape V :=
  TransitionArena.forestPorts.trans (transitionPorts V)

def termPorts (V : NPVerifier) : TermMachine.Tape ↪ Tape V :=
  TransitionArena.termPorts.trans (transitionPorts V)

def initializationTape (V : NPVerifier) : InitializationAssembly.Tape 9 → Tape V
  | .rawInput => raw V
  | .framedInput => framed V
  | .witnessBound => q V
  | .capacity => capacity V
  | .reversed => tokens V
  | .count => count V
  | .validityWork j => .inr (.validity j)
  | .cellWork j => .inr (.cells j)

def initializationPorts (V : NPVerifier) : InitializationAssembly.Tape 9 ↪ Tape V where
  toFun := initializationTape V
  inj' := by
    intro a b h
    cases a <;> cases b <;>
      simp_all [initializationTape, q, capacity, tokens, count, shared,
        raw, framed, clock, VerifierFront.raw, VerifierFront.stream,
        VerifierFront.clockTape, VerifierFront.clockSlots,
        ClockPreparation.clockOutput]
    all_goals
      have ho := ClockPreparation.outputSlot_injective (ClockPreparation.clockPolynomials V) h
      cases ho

@[simp] theorem initializationPorts_apply (V : NPVerifier) (t : InitializationAssembly.Tape 9) :
    initializationPorts V t = initializationTape V t := rfl

def finishTape (V : NPVerifier) : CircuitFinish.Tape → Tape V
  | .current => current V
  | .freeInputs => freeInputs V
  | .root => roots V
  | .reversedRecords => records V
  | .output => output V
  | .gateCount => .inr (.finish .gateCount)
  | .scratch => .inr (.finish .scratch)

def finishPorts (V : NPVerifier) : CircuitFinish.Tape ↪ Tape V where
  toFun := finishTape V
  inj' := by
    intro a b h
    cases a <;> cases b <;>
      simp_all [finishTape, current, freeInputs, roots, records, output, shared, clock]

@[simp] theorem finishPorts_apply (V : NPVerifier) (t : CircuitFinish.Tape) :
    finishPorts V t = finishTape V t := rfl

def bootstrapPorts (V : NPVerifier) : ProducerBootstrap.Ports (Tape V) where
  toFun := ![freeInputs V, current V, .inr .bootstrap, count V, cursor V]
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;>
      simp_all [freeInputs, current, count, cursor, shared, clock]

@[simp] theorem bootstrap_source (V : NPVerifier) : bootstrapPorts V 0 = freeInputs V := rfl
@[simp] theorem bootstrap_current (V : NPVerifier) : bootstrapPorts V 1 = current V := rfl
@[simp] theorem bootstrap_scratch (V : NPVerifier) :
    bootstrapPorts V 2 = .inr .bootstrap := rfl
@[simp] theorem bootstrap_count (V : NPVerifier) : bootstrapPorts V 3 = count V := rfl
@[simp] theorem bootstrap_cursor (V : NPVerifier) : bootstrapPorts V 4 = cursor V := rfl

def empty (V : NPVerifier) : Tape V → List Bool := fun _ => []

def frontTapes (V : NPVerifier) (contents : VerifierFront.Tape V → List Bool) :
    Tape V → List Bool
  | .inl t => contents t
  | .inr _ => []

@[simp] theorem frontTapes_at (V : NPVerifier)
    (contents : VerifierFront.Tape V → List Bool) (t : VerifierFront.Tape V) :
    frontTapes V contents (frontPorts V t) = contents t := rfl

@[simp] theorem frontTapes_work (V : NPVerifier)
    (contents : VerifierFront.Tape V → List Bool) (t : Work) :
    frontTapes V contents (.inr t) = [] := rfl

theorem front_fill (V : NPVerifier) (contents : VerifierFront.Tape V → List Bool) :
    ForestPlacement.fill (frontPorts V) (empty V) contents = frontTapes V contents := by
  funext t
  cases t with
  | inl t => exact ForestPlacement.fill_at (frontPorts V) (empty V) contents t
  | inr t =>
    exact ForestPlacement.fill_other (frontPorts V) (empty V) contents _
      (by intro i; simp [frontPorts])

def initialTapes (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  frontTapes V (VerifierFront.frameTapes V input)

theorem initialTapes_eq (V : NPVerifier) (input : List Bool) :
    initialTapes V input = fun t => if t = raw V then input else [] := by
  funext t
  cases t with
  | inl t =>
    cases t with
    | inl i => fin_cases i <;> simp [initialTapes, frontTapes, VerifierFront.frameTapes,
        raw, VerifierFront.raw]
    | inr t => simp [initialTapes, frontTapes, VerifierFront.frameTapes, raw, VerifierFront.raw]
  | inr t => simp [initialTapes, frontTapes, raw]

def frontendPrepared (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  frontTapes V (VerifierFront.preparedTapes V input)

@[simp] theorem frontendPrepared_raw (V : NPVerifier) (input : List Bool) :
    frontendPrepared V input (raw V) = input := VerifierFront.prepared_raw V input

@[simp] theorem frontendPrepared_framed (V : NPVerifier) (input : List Bool) :
    frontendPrepared V input (framed V) = encodeWord input.length ++ input :=
  VerifierFront.prepared_stream V input

@[simp] theorem frontendPrepared_clock (V : NPVerifier) (input : List Bool)
    (c : ClockPreparation.Clock) : frontendPrepared V input (clock V c) =
      encodeWord (ClockPreparation.clockValue V input.length c) :=
  VerifierFront.prepared_clock V input c

@[simp] theorem frontendPrepared_work (V : NPVerifier) (input : List Bool) (t : Work) :
    frontendPrepared V input (.inr t) = [] := rfl

theorem bootstrapReady (V : NPVerifier) (input : List Bool) :
    ProducerBootstrap.Ready (bootstrapPorts V) (frontendPrepared V input)
      (2 * V.witnessBound.eval input.length + 1) := by
  exact ⟨frontendPrepared_clock V input .inputCount, rfl, rfl, rfl, rfl⟩

def bootstrapPrepared (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  ProducerBootstrap.prepared (bootstrapPorts V) (frontendPrepared V input)

@[simp] theorem bootstrapPrepared_front (V : NPVerifier) (input : List Bool)
    (t : VerifierFront.Tape V) :
    bootstrapPrepared V input (frontPorts V t) = VerifierFront.preparedTapes V input t := by
  apply ProducerBootstrap.prepared_other
  all_goals simp [frontPorts, bootstrapPorts, current, count, cursor, shared]

@[simp] theorem bootstrapPrepared_current (V : NPVerifier) (input : List Bool) :
    bootstrapPrepared V input (current V) =
      encodeWord (2 * V.witnessBound.eval input.length + 1) :=
  ProducerBootstrap.prepared_current (bootstrapPorts V) (frontendPrepared V input) _
    (bootstrapReady V input)

@[simp] theorem bootstrapPrepared_count (V : NPVerifier) (input : List Bool) :
    bootstrapPrepared V input (count V) = encodeWord 0 :=
  ProducerBootstrap.prepared_count (bootstrapPorts V) (frontendPrepared V input) _
    (bootstrapReady V input)

@[simp] theorem bootstrapPrepared_cursor (V : NPVerifier) (input : List Bool) :
    bootstrapPrepared V input (cursor V) = encodeWord 0 :=
  ProducerBootstrap.prepared_cursor (bootstrapPorts V) (frontendPrepared V input) _
    (bootstrapReady V input)

theorem bootstrapPrepared_other (V : NPVerifier) (input : List Bool) (t : Tape V)
    (hc : t ≠ current V) (ht : t ≠ count V) (hz : t ≠ cursor V) :
    bootstrapPrepared V input t = frontendPrepared V input t :=
  ProducerBootstrap.prepared_other (bootstrapPorts V) (frontendPrepared V input) t hc ht hz

def initializationBase (V : NPVerifier) (input : List Bool) :
    InitializationAssembly.Tape 9 → List Bool
  | .rawInput => input
  | .framedInput => encodeWord input.length ++ input
  | .witnessBound => encodeWord (V.witnessBound.eval input.length)
  | .capacity => encodeWord (VerifierCircuit.capacity V input.length)
  | .count => encodeWord 0
  | _ => []

theorem bootstrap_initialization_view (V : NPVerifier) (input : List Bool) :
    (fun t => bootstrapPrepared V input (initializationPorts V t)) =
      initializationBase V input := by
  funext t
  cases t <;>
    simp [initializationTape, initializationBase, bootstrapPrepared,
      ProducerBootstrap.prepared, ProducerBootstrap.copied,
      frontendPrepared, frontTapes, current, count, cursor, tokens, shared,
      raw, framed, q, capacity, freeInputs, clock,
      VerifierFront.prepared_raw, VerifierFront.prepared_stream, VerifierFront.prepared_clock,
      ClockPreparation.clockValue, encodeWord]

theorem initializationValidityReady (V : NPVerifier) (input : List Bool) :
    ClashMachine.Full.Ready (InitializationAssembly.validitySlots 9)
      (fun t => bootstrapPrepared V input (initializationPorts V t))
      (V.witnessBound.eval input.length) := by
  rw [bootstrap_initialization_view]
  exact InitializationAssembly.validityReady _ _ rfl (fun _ => rfl)

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.ProducerArena


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.ProducerFrontStage

open Turing ProducerArena

abbrev Label (V : NPVerifier) := VerifierFront.Label V ⊕ ProducerBootstrap.Label

def entry (V : NPVerifier) : Label V := .inl (.inl 0)

def statement {Λ : Type} (V : NPVerifier) (labels : Label V → Λ) (exit : Option Λ) :
    Label V → TM2.Stmt (Alphabet V) Λ State
  | .inl l => ForestPlacement.statement (frontPorts V) (fun l => labels (.inl l))
      (some (labels (.inr .copy))) (VerifierFront.program (A := Unit × Bool) V l)
  | .inr l => ProducerBootstrap.statement (bootstrapPorts V) (fun l => labels (.inr l)) exit l

def timePolynomial (V : NPVerifier) : Polynomial Nat :=
  VerifierFront.timePolynomial V +
    Polynomial.C 2 * WitnessEncoding.freeInputPolynomial V.witnessBound + Polynomial.C 5

theorem timePolynomial_eval (V : NPVerifier) (n : Nat) :
    (timePolynomial V).eval n = (VerifierFront.timePolynomial V).eval n +
      (2 * (2 * V.witnessBound.eval n + 1) + 5) := by
  simp [timePolynomial, Nat.add_assoc]

def inTime {Λ : Type} (V : NPVerifier) (labels : Label V → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet V) Λ State)
    (code : ∀ l, program (labels l) = statement V labels exit l)
    (input : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (entry V)), initialState, initialTapes V input⟩
      (some ⟨exit, initialState, bootstrapPrepared V input⟩)
      ((timePolynomial V).eval input.length) := by
  have front := ForestPlacement.execution (frontPorts V)
    (fun l => labels (.inl l)) (some (labels (.inr .copy))) (empty V)
    (VerifierFront.program (A := Unit × Bool) V) program (fun l => code (.inl l))
    (VerifierFront.prepareInTime V input ((), false))
  have front' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (entry V)), initialState, initialTapes V input⟩
      (some ⟨some (labels (.inr .copy)), initialState, frontendPrepared V input⟩)
      ((VerifierFront.timePolynomial V).eval input.length) := by
    simpa only [ForestPlacement.configuration, ForestPlacement.placedLabel,
      front_fill, entry, initialTapes, frontendPrepared, initialState,
      TermMachine.initialState] using front
  have boot := ProducerBootstrap.inTime (bootstrapPorts V) (fun l => labels (.inr l))
    exit program (fun l => code (.inr l)) (frontendPrepared V input)
    (2 * V.witnessBound.eval input.length + 1) (bootstrapReady V input) ((), false) none
  have combined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ front' boot
  simpa only [timePolynomial_eval, bootstrapPrepared, initialState,
    TermMachine.initialState, Nat.add_comm] using combined

def program (V : NPVerifier) : Label V → TM2.Stmt (Alphabet V) (Label V) State :=
  statement V id none

def programInTime (V : NPVerifier) (input : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program V))
      ⟨some (entry V), initialState, initialTapes V input⟩
      (some ⟨none, initialState, bootstrapPrepared V input⟩)
      ((timePolynomial V).eval input.length) :=
  inTime V id none (program V) (fun _ => rfl) input

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.ProducerFrontStage


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.ProducerHandoffs

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

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.ProducerHandoffs

end

end OAI
