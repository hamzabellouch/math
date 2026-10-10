import OAI.Computability.PerfectCompleteness.Machines.CircuitProducerStagesLemmas
import OAI.Computability.PerfectCompleteness.Machines.PostfixBounds
import OAI.Computability.PerfectCompleteness.Machines.ProducerBootstrapLemmas
import OAI.Computability.UniqueGames.Machines.MachineControlLemmas
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage

open Turing MachineComposition StatementCircuit CircuitBatch CircuitProducerModel
open PostfixModel PostfixAlignment


inductive Tape
  | lower (tape : PostfixMachine.Tape)
  | tokens | records | rootTable
  deriving DecidableEq, Fintype

abbrev Ports (K : Type) := Tape ↪ K
abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

inductive Label
  | reverseTokens
  | lower (label : PostfixMachine.Label)
  | reverseRecords | drainRoots | rootGuard | rootStart | rootLoop | finish
  deriving DecidableEq, Fintype

def lowerPorts {K : Type} (ports : Ports K) : PostfixMachine.Tape ↪ K :=
  ⟨fun t => ports (.lower t), by
    intro a b h
    exact Tape.lower.inj (ports.injective h)⟩

def initialLocal (start : Nat) (tokens : List Token)
    (oldRecords oldRoots : List Bool) : Tape → List Bool
  | .lower .current => encodeWord start
  | .lower .remaining => encodeWord tokens.length
  | .tokens => (tokenBits tokens).reverse
  | .records => oldRecords
  | .rootTable => oldRoots
  | _ => []

def finalLocal (next : Nat) (roots : List Nat)
    (newRecords oldRecords : List Bool) : Tape → List Bool
  | .lower .current => encodeWord next
  | .lower .remaining => encodeWord 0
  | .records => newRecords.reverse ++ oldRecords
  | .rootTable => encodeWords roots.reverse
  | _ => []

def coreBase (tokens : List Token) : PostfixMachine.Tape → List Bool
  | .remaining => encodeWord tokens.length
  | _ => []

def coreInitial (start : Nat) (tokens : List Token) : PostfixMachine.Tape → List Bool :=
  PostfixMachine.boundaryTapes (coreBase tokens) start [] (tokenBits tokens)

def coreFinal (next : Nat) (roots : List Nat) (records : List Bool) :
    PostfixMachine.Tape → List Bool :=
  PostfixMachine.finalTapes (fun _ => []) next roots [] records

private theorem chain {A : Type*} {f : A → A} {x y z : A} {n m : Nat}
    (first : f^[n] x = y) (second : f^[m] y = z) : f^[n + m] x = z := by
  rw [Nat.add_comm n m, Function.iterate_add_apply, first, second]

theorem coreTrace (tokens : List Token) (start next : Nat) (roots : List Nat)
    (gates : List Gate)
    (valid : compileTokens start [] tokens = some (next, roots, gates)) :
    (advance (TM2.step PostfixMachine.program))^[
      PostfixMachine.tokensSteps start [] tokens +
        (recordsBits (gateRecords start gates)).length + 3]
      (some ⟨some .guard, PostfixMachine.initialState, coreInitial start tokens⟩) =
      some ⟨none, PostfixMachine.initialState,
        coreFinal next roots (recordsBits (gateRecords start gates))⟩ := by
  let bits := recordsBits (gateRecords start gates)
  let middle := PostfixMachine.boundaryTapes
    (PostfixMachine.outputTapes
      (Function.update (coreBase tokens) .remaining (encodeWord 0)) bits.reverse)
    next roots []
  have first := PostfixMachine.tokensTrace tokens (coreBase tokens) start [] next roots
    gates [] valid (by rfl)
  simp only [List.append_nil] at first
  have second := PostfixMachine.reverseTrace middle bits
    (by simp [middle, PostfixMachine.boundaryTapes, PostfixMachine.outputTapes])
    (by simp [middle, PostfixMachine.boundaryTapes, PostfixMachine.outputTapes, coreBase])
  have result := chain first second
  have frame : PostfixMachine.reversedTapes middle bits = coreFinal next roots bits := by
    funext tape
    cases tape <;> simp [PostfixMachine.reversedTapes, middle, coreFinal,
      PostfixMachine.finalTapes, PostfixMachine.boundaryTapes, PostfixMachine.outputTapes,
      coreBase]
  rw [frame] at result
  simpa only [coreInitial, bits, Nat.add_assoc] using result

def stateEquiv (σ : Type) : PostfixMachine.State × (σ × Bool) ≃ State σ where
  toFun state := (state.2, state.1.2)
  invFun state := (((), state.2), state.1)
  left_inv state := by rcases state with ⟨⟨u, register⟩, ambient⟩; cases u; rfl
  right_inv _ := rfl

def framedStatement {σ : Type}
    (stmt : TM2.Stmt PostfixMachine.Alphabet PostfixMachine.Label PostfixMachine.State) :
    TM2.Stmt PostfixMachine.Alphabet PostfixMachine.Label (State σ) :=
  MachineControl.statement id (stateEquiv σ) (MachineStateFrame.frameStatement stmt)

def framedProgram {σ : Type} :
    PostfixMachine.Label → TM2.Stmt PostfixMachine.Alphabet PostfixMachine.Label (State σ) :=
  fun label => framedStatement (PostfixMachine.program label)

def framedCfg {σ : Type} (ambient : σ × Bool) (cfg : PostfixMachine.machine.Cfg) :
    TM2.Cfg PostfixMachine.Alphabet PostfixMachine.Label (State σ) :=
  MachineControl.configuration id (stateEquiv σ)
    (MachineStateFrame.frameConfiguration ambient cfg)

theorem framed_step {σ : Type} (ambient : σ × Bool)
    (a b : PostfixMachine.machine.Cfg) (h : PostfixMachine.machine.step a = some b) :
    TM2.step framedProgram (framedCfg ambient a) = some (framedCfg ambient b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => simp [FinTM2.step, TM2.step] at h
    | some label =>
      have hb : TM2.stepAux (PostfixMachine.program label) state tapes = b := Option.some.inj h
      rw [← hb]
      change some (TM2.stepAux
        (MachineControl.statement id (stateEquiv σ)
          (MachineStateFrame.frameStatement (PostfixMachine.program label)))
        (stateEquiv σ (state, ambient)) tapes) = _
      erw [MachineControl.stepAux_simulation, MachineStateFrame.frame_stepAux]
      rfl

theorem framed_coreTrace {σ : Type} (ambient : σ × Bool)
    (tokens : List Token) (start next : Nat) (roots : List Nat) (gates : List Gate)
    (valid : compileTokens start [] tokens = some (next, roots, gates)) :
    (advance (TM2.step framedProgram))^[PostfixMachine.tokensSteps start [] tokens +
        (recordsBits (gateRecords start gates)).length + 3]
      (some ⟨some .guard, (ambient, none), coreInitial start tokens⟩) =
      some ⟨none, (ambient, none), coreFinal next roots (recordsBits (gateRecords start gates))⟩ :=
  liftSuccessfulTrace PostfixMachine.machine.step (TM2.step framedProgram)
    (framedCfg ambient) (framed_step ambient) _ _ _ (coreTrace tokens start next roots gates valid)

def steps (tokens : List Token) (start : Nat) (roots : List Nat) (gates : List Gate)
    (oldRoots : List Bool) : Nat :=
  (tokenBits tokens).length + PostfixMachine.tokensSteps start [] tokens +
    2 * (recordsBits (gateRecords start gates)).length + oldRoots.length +
    RootRefresh.steps roots + 7

private theorem forest_length_le_cost {ι : Type*} (es : List (Expr ι)) :
    es.length ≤ Batch.cost es := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have hp := e.size_pos
    simp only [List.length_cons, Batch.cost_cons]
    omega

private theorem forest_rootsBits_length_le {ι : Type*}
    (es : List (Expr ι)) (start : Nat) :
    (encodeWords (Batch.roots start es).reverse).length ≤
      Batch.cost es * (start + Batch.cost es + 1) := by
  have h := encodeWords_length_le (Batch.roots start es).reverse
    (start + Batch.cost es) (by
      intro r hr
      exact (Batch.roots_bounds start es r (List.mem_reverse.mp hr)).2.le)
  have h' : (encodeWords (Batch.roots start es).reverse).length ≤
      es.length * (start + Batch.cost es + 1) := by
    simpa only [List.length_reverse, Batch.roots_length] using h
  exact h'.trans (Nat.mul_le_mul_right _ (forest_length_le_cost es))

private theorem forest_rootRefresh_le {ι : Type*} (es : List (Expr ι)) (start : Nat) :
    RootRefresh.steps (Batch.roots start es).reverse ≤
      3 * (Batch.cost es * (start + Batch.cost es + 1)) + 1 :=
  (RootRefresh.steps_le_length _).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (forest_rootsBits_length_le es start)) 1)

private theorem forest_cost_quadratic (start c T R S G H : Nat)
    (hS : S ≤ c * (12 * (start + c) + 25))
    (hG : G ≤ 4 * c * (start + c + 5))
    (hH : H ≤ 3 * (c * (start + c + 1)) + 1) :
    let m := start + c + T + R + 1
    T + S + 2 * G + R + H + 7 ≤ 25 * m ^ 2 + 80 * m + 20 := by
  dsimp only
  let m := start + c + T + R + 1
  change T + S + 2 * G + R + H + 7 ≤ 25 * m ^ 2 + 80 * m + 20
  have hc : c ≤ m := by dsimp only [m]; omega
  have hsc : start + c ≤ m := by dsimp only [m]; omega
  have hsc1 : start + c + 1 ≤ m := by dsimp only [m]; omega
  have hTR : T + R ≤ m := by dsimp only [m]; omega
  have hS' : S ≤ m * (12 * m + 25) := hS.trans (Nat.mul_le_mul hc (by omega))
  have hG' : G ≤ 4 * m * (m + 5) :=
    hG.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 4 hc) (by omega))
  have hr : c * (start + c + 1) ≤ m * m := Nat.mul_le_mul hc hsc1
  have hH' : H ≤ 3 * (m * m) + 1 :=
    hH.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hr) 1)
  calc
    _ ≤ (T + R) + m * (12 * m + 25) +
        2 * (4 * m * (m + 5)) + (3 * (m * m) + 1) + 7 := by omega
    _ ≤ m + m * (12 * m + 25) +
        2 * (4 * m * (m + 5)) + (3 * (m * m) + 1) + 7 := by omega
    _ = 23 * m ^ 2 + 66 * m + 8 := by ring
    _ ≤ 25 * m ^ 2 + 80 * m + 20 := by omega

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 25 * Polynomial.X ^ 2 + Polynomial.C 80 * Polynomial.X + Polynomial.C 20

theorem forest_steps_le {ι : Type*} (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) (oldRoots : List Bool) (hw : ∀ i, wire i < start) :
    steps (forestTokens wire es) start (Batch.roots start es).reverse
        (Batch.gates wire start es) oldRoots ≤
      timePolynomial.eval (start + Batch.cost es + (tokenBits (forestTokens wire es)).length +
        oldRoots.length + 1) := by
  simp only [steps, timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  exact forest_cost_quadratic start (Batch.cost es)
    (tokenBits (forestTokens wire es)).length oldRoots.length
    (PostfixMachine.tokensSteps start [] (forestTokens wire es))
    (recordsBits (gateRecords start (Batch.gates wire start es))).length
    (RootRefresh.steps (Batch.roots start es).reverse)
    (PostfixBounds.forest_tokensSteps_le wire es start [] hw (by intro r hr; simp at hr))
    (PostfixBounds.forest_recordsBits_length_le wire es start hw)
    (forest_rootRefresh_le es start)

def localLowerPorts : PostfixMachine.Tape ↪ Tape :=
  ⟨Tape.lower, by intro a b h; exact Tape.lower.inj h⟩

def lowerFill (base : Tape → List Bool) (inner : PostfixMachine.Tape → List Bool) :
    Tape → List Bool
  | .lower tape => inner tape
  | tape => base tape

theorem fill_lower_eq (base : Tape → List Bool) (inner : PostfixMachine.Tape → List Bool) :
    ForestPlacement.fill localLowerPorts base inner = lowerFill base inner := by
  funext tape
  cases tape with
  | lower tape => exact ForestPlacement.fill_at localLowerPorts base inner tape
  | tokens => exact ForestPlacement.fill_other _ _ _ _ (by intro i; simp [localLowerPorts])
  | records => exact ForestPlacement.fill_other _ _ _ _ (by intro i; simp [localLowerPorts])
  | rootTable => exact ForestPlacement.fill_other _ _ _ _ (by intro i; simp [localLowerPorts])

def program {σ : Type} : Label → TM2.Stmt (Alphabet (K := Tape)) Label (State σ)
  | .reverseTokens => Reduction.MachineTransfer.loopAt .tokens (.lower .input) id false
      .reverseTokens (some (.lower .guard))
  | .lower label => ForestPlacement.statement localLowerPorts Label.lower
      (some .reverseRecords) (framedProgram label)
  | .reverseRecords => Reduction.MachineTransfer.loopAt (.lower .output) .records id false
      .reverseRecords (some .drainRoots)
  | .drainRoots => MachineDrain.drain .rootTable .drainRoots (some .rootGuard)
  | .rootGuard => RootRefresh.guard (.lower .roots) .rootStart (some .finish)
  | .rootStart => Hastad.SourceMachine.fieldStart .rootTable .rootLoop
  | .rootLoop => Hastad.SourceMachine.fieldLoop (.lower .roots) .rootTable .rootLoop
      (some .rootGuard)
  | .finish => .push (.lower .remaining) (fun _ => false)
      (.load (fun state => (state.1, none)) .halt)

def extras (oldRecords oldRoots : List Bool) : Tape → List Bool
  | .records => oldRecords
  | .rootTable => oldRoots
  | _ => []

def afterRecords (next : Nat) (roots : List Nat) (records oldRoots : List Bool) :
    Tape → List Bool
  | .lower .current => encodeWord next
  | .lower .roots => encodeWords roots
  | .records => records
  | .rootTable => oldRoots
  | _ => []

theorem localTrace {σ : Type} (ambient : σ × Bool)
    (tokens : List Token) (start next : Nat) (roots : List Nat) (gates : List Gate)
    (oldRecords oldRoots : List Bool)
    (valid : compileTokens start [] tokens = some (next, roots, gates)) :
    (advance (TM2.step program))^[steps tokens start roots gates oldRoots]
      (some ⟨some .reverseTokens, (ambient, none), initialLocal start tokens oldRecords oldRoots⟩) =
      some ⟨none, (ambient, none),
        finalLocal next roots (recordsBits (gateRecords start gates)) oldRecords⟩ := by
  let bits := recordsBits (gateRecords start gates)
  let initial := initialLocal start tokens oldRecords oldRoots
  let ready := lowerFill (extras oldRecords oldRoots) (coreInitial start tokens)
  let compiled := lowerFill (extras oldRecords oldRoots) (coreFinal next roots bits)
  let merged := afterRecords next roots (bits.reverse ++ oldRecords) oldRoots
  let refreshed := afterRecords next roots (bits.reverse ++ oldRecords) []
  let unseeded := Function.update (finalLocal next roots bits oldRecords) (.lower .remaining) []
  have inputTransfer := (Reduction.MachineTransfer.transferAtInTime
    Tape.tokens (.lower .input) (by decide) id false .reverseTokens
    (some (.lower .guard)) program rfl initial ambient none).evals_in_steps
  have inputFrame : Reduction.MachineTransfer.tapesAt Tape.tokens (.lower .input) initial []
      ((initial .tokens).reverse.map id ++ initial (.lower .input)) = ready := by
    funext tape
    cases tape with
    | lower tape => cases tape <;> simp [Reduction.MachineTransfer.tapesAt, initial,
        initialLocal, ready, lowerFill, coreInitial, PostfixMachine.boundaryTapes, coreBase, encodeWords]
    | tokens => simp [Reduction.MachineTransfer.tapesAt, initial, initialLocal, ready, lowerFill, extras]
    | records => simp [Reduction.MachineTransfer.tapesAt, initial, initialLocal, ready, lowerFill, extras]
    | rootTable => simp [Reduction.MachineTransfer.tapesAt, initial, initialLocal, ready, lowerFill, extras]
  change (advance (TM2.step program))^[(initial .tokens).length + 1]
    (some ⟨some .reverseTokens, (ambient, none), initial⟩) =
      some ⟨some (.lower .guard), (ambient, none), _⟩ at inputTransfer
  rw [inputFrame] at inputTransfer
  have hinputLength : (initial .tokens).length = (tokenBits tokens).length := by
    simp [initial, initialLocal]
  rw [hinputLength] at inputTransfer
  have lowering := ForestPlacement.trace localLowerPorts Label.lower (some .reverseRecords)
    (extras oldRecords oldRoots) framedProgram program (fun _ => rfl) _ _ _
    (framed_coreTrace ambient tokens start next roots gates valid)
  change (advance (TM2.step program))^[PostfixMachine.tokensSteps start [] tokens + bits.length + 3]
      (some ⟨some (.lower .guard), (ambient, none),
        ForestPlacement.fill localLowerPorts (extras oldRecords oldRoots) (coreInitial start tokens)⟩) =
      some ⟨some .reverseRecords, (ambient, none),
        ForestPlacement.fill localLowerPorts (extras oldRecords oldRoots) (coreFinal next roots bits)⟩ at lowering
  rw [fill_lower_eq, fill_lower_eq] at lowering
  have recordTransfer := (Reduction.MachineTransfer.transferAtInTime
    (Tape.lower .output) .records (by decide) id false .reverseRecords (some .drainRoots)
    program rfl compiled ambient none).evals_in_steps
  have recordFrame : Reduction.MachineTransfer.tapesAt (Tape.lower .output) .records compiled []
      ((compiled (.lower .output)).reverse.map id ++ compiled .records) = merged := by
    funext tape
    cases tape with
    | lower tape => cases tape <;> simp [Reduction.MachineTransfer.tapesAt, compiled,
        lowerFill, extras, coreFinal, PostfixMachine.finalTapes, merged, afterRecords]
    | tokens => simp [Reduction.MachineTransfer.tapesAt, compiled, lowerFill, extras, merged, afterRecords]
    | records => simp [Reduction.MachineTransfer.tapesAt, compiled, lowerFill, extras,
        coreFinal, PostfixMachine.finalTapes, merged, afterRecords]
    | rootTable => simp [Reduction.MachineTransfer.tapesAt, compiled, lowerFill, extras, merged, afterRecords]
  change (advance (TM2.step program))^[(compiled (.lower .output)).length + 1]
    (some ⟨some .reverseRecords, (ambient, none), compiled⟩) =
      some ⟨some .drainRoots, (ambient, none), _⟩ at recordTransfer
  rw [recordFrame] at recordTransfer
  have hrecordLength : (compiled (.lower .output)).length = bits.length := by
    simp [compiled, lowerFill, coreFinal, PostfixMachine.finalTapes]
  rw [hrecordLength] at recordTransfer
  have draining := MachineDrain.drainTrace Tape.rootTable .drainRoots (some .rootGuard)
    program rfl merged (merged .rootTable) ambient none
  rw [Function.update_eq_self] at draining
  change (advance (TM2.step program))^[(merged .rootTable).length + 1]
    (some ⟨some .drainRoots, (ambient, none), merged⟩) =
      some ⟨some .rootGuard, (ambient, none), Function.update merged .rootTable []⟩ at draining
  have drainFrame : Function.update merged .rootTable [] = refreshed := by
    funext tape
    cases tape with
    | lower tape => cases tape <;> simp [merged, refreshed, afterRecords]
    | tokens => simp [merged, refreshed, afterRecords]
    | records => simp [merged, refreshed, afterRecords]
    | rootTable => simp [merged, refreshed, afterRecords]
  rw [drainFrame] at draining
  have hrootLength : (merged .rootTable).length = oldRoots.length := rfl
  rw [hrootLength] at draining
  have refresh := RootRefresh.refreshTrace (Tape.lower .roots) .rootTable (by decide)
    .rootGuard .rootStart .rootLoop (some .finish) program rfl rfl rfl
    refreshed roots [] ambient none
  have refreshInitial : Hastad.SourceMachine.fieldTapes (Tape.lower .roots) .rootTable
      refreshed (encodeWords roots) [] = refreshed := by
    funext tape
    cases tape with
    | lower tape => cases tape <;> simp [Hastad.SourceMachine.fieldTapes, refreshed, afterRecords]
    | tokens => simp [Hastad.SourceMachine.fieldTapes, refreshed, afterRecords]
    | records => simp [Hastad.SourceMachine.fieldTapes, refreshed, afterRecords]
    | rootTable => simp [Hastad.SourceMachine.fieldTapes, refreshed, afterRecords]
  have refreshFinal : Hastad.SourceMachine.fieldTapes (Tape.lower .roots) .rootTable
      refreshed [] (encodeWords roots.reverse ++ []) = unseeded := by
    funext tape
    cases tape with
    | lower tape => cases tape <;> simp [Hastad.SourceMachine.fieldTapes, refreshed,
        afterRecords, unseeded, finalLocal]
    | tokens => simp [Hastad.SourceMachine.fieldTapes, refreshed, afterRecords, unseeded, finalLocal]
    | records => simp [Hastad.SourceMachine.fieldTapes, refreshed, afterRecords, unseeded, finalLocal]
    | rootTable => simp [Hastad.SourceMachine.fieldTapes, refreshed, unseeded, finalLocal]
  rw [refreshInitial, refreshFinal] at refresh
  have finish : (advance (TM2.step program))^[1]
      (some ⟨some .finish, (ambient, none), unseeded⟩) =
      some ⟨none, (ambient, none), finalLocal next roots bits oldRecords⟩ := by
    change some (TM2.stepAux (program .finish) (ambient, none) unseeded) = _
    simp [program, TM2.stepAux, unseeded, finalLocal, encodeWord, Function.update_idem]
  have total := chain (chain (chain (chain (chain inputTransfer lowering) recordTransfer) draining) refresh) finish
  have cost : (((((tokenBits tokens).length + 1 +
      (PostfixMachine.tokensSteps start [] tokens + bits.length + 3)) +
      (bits.length + 1)) + (oldRoots.length + 1)) + RootRefresh.steps roots) + 1 =
      steps tokens start roots gates oldRoots := by dsimp only [steps, bits]; omega
  simpa only [cost, initial, bits] using total

section Caller

variable {K Λ σ : Type} [DecidableEq K]

def statement (ports : Ports K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  fun label => ForestPlacement.statement ports labels exit (program label)

theorem traceAt (ports : Ports K) (labels : Label → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, target (labels label) = statement ports labels exit label)
    (base : K → List Bool) (ambient : σ × Bool) (tokens : List Token)
    (start next : Nat) (roots : List Nat) (gates : List Gate) (oldRecords oldRoots : List Bool)
    (valid : compileTokens start [] tokens = some (next, roots, gates)) :
    (advance (TM2.step target))^[steps tokens start roots gates oldRoots]
      (some ⟨some (labels .reverseTokens), (ambient, none),
        ForestPlacement.fill ports base (initialLocal start tokens oldRecords oldRoots)⟩) =
      some ⟨exit, (ambient, none), ForestPlacement.fill ports base
        (finalLocal next roots (recordsBits (gateRecords start gates)) oldRecords)⟩ :=
  ForestPlacement.trace ports labels exit base program target atLabels _ _ _
    (localTrace ambient tokens start next roots gates oldRecords oldRoots valid)

theorem forestTraceAt {ι : Type} (ports : Ports K) (labels : Label → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, target (labels label) = statement ports labels exit label)
    (base : K → List Bool) (ambient : σ × Bool) (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) (oldRecords oldRoots : List Bool) :
    (advance (TM2.step target))^[steps (forestTokens wire es) start
        (Batch.roots start es).reverse (Batch.gates wire start es) oldRoots]
      (some ⟨some (labels .reverseTokens), (ambient, none), ForestPlacement.fill ports base
        (initialLocal start (forestTokens wire es) oldRecords oldRoots)⟩) =
      some ⟨exit, (ambient, none), ForestPlacement.fill ports base
        (finalLocal (start + Batch.cost es) (Batch.roots start es).reverse
          (recordsBits (gateRecords start (Batch.gates wire start es))) oldRecords)⟩ := by
  apply traceAt ports labels exit target atLabels base ambient _ _ _ _ _ _ _
  simpa only [List.append_nil] using compile_forestTokens wire es start []

noncomputable def forestInPolynomialTime {ι : Type}
    (ports : Ports K) (labels : Label → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, target (labels label) = statement ports labels exit label)
    (base : K → List Bool) (ambient : σ × Bool) (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) (oldRecords oldRoots : List Bool) (hw : ∀ i, wire i < start) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels .reverseTokens), (ambient, none), ForestPlacement.fill ports base
        (initialLocal start (forestTokens wire es) oldRecords oldRoots)⟩
      (some ⟨exit, (ambient, none), ForestPlacement.fill ports base
        (finalLocal (start + Batch.cost es) (Batch.roots start es).reverse
          (recordsBits (gateRecords start (Batch.gates wire start es))) oldRecords)⟩)
      (timePolynomial.eval (start + Batch.cost es +
        (tokenBits (forestTokens wire es)).length + oldRoots.length + 1)) where
  steps := steps (forestTokens wire es) start (Batch.roots start es).reverse
    (Batch.gates wire start es) oldRoots
  evals_in_steps := forestTraceAt ports labels exit target atLabels base ambient wire es
    start oldRecords oldRoots
  steps_le_m := forest_steps_le wire es start oldRoots hw

def preparedSize (ports : Ports K) (tapes : K → List Bool) : Nat :=
  (tapes (ports (.lower .current))).length +
    (tapes (ports (.lower .remaining))).length + (tapes (ports .tokens)).length +
    (tapes (ports .rootTable)).length

omit [DecidableEq K] in
theorem preparedSize_initial (ports : Ports K) (base : K → List Bool)
    (start : Nat) (tokens : List Token) (oldRecords oldRoots : List Bool) :
    preparedSize ports (ForestPlacement.fill ports base
      (initialLocal start tokens oldRecords oldRoots)) =
      start + tokens.length + (tokenBits tokens).length + oldRoots.length + 2 := by
  simp only [preparedSize, ForestPlacement.fill_at, initialLocal, encodeWord_length,
    List.length_reverse]
  omega

noncomputable def forestInPreparedTime {ι : Type}
    (ports : Ports K) (labels : Label → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, target (labels label) = statement ports labels exit label)
    (base : K → List Bool) (ambient : σ × Bool) (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) (oldRecords oldRoots : List Bool) (hw : ∀ i, wire i < start) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels .reverseTokens), (ambient, none), ForestPlacement.fill ports base
        (initialLocal start (forestTokens wire es) oldRecords oldRoots)⟩
      (some ⟨exit, (ambient, none), ForestPlacement.fill ports base
        (finalLocal (start + Batch.cost es) (Batch.roots start es).reverse
          (recordsBits (gateRecords start (Batch.gates wire start es))) oldRecords)⟩)
      (timePolynomial.eval (preparedSize ports (ForestPlacement.fill ports base
        (initialLocal start (forestTokens wire es) oldRecords oldRoots)))) := by
  let run := forestInPolynomialTime ports labels exit target atLabels base ambient wire es
    start oldRecords oldRoots hw
  have sizeBound : start + Batch.cost es + (tokenBits (forestTokens wire es)).length +
      oldRoots.length + 1 ≤ preparedSize ports (ForestPlacement.fill ports base
        (initialLocal start (forestTokens wire es) oldRecords oldRoots)) := by
    rw [preparedSize_initial, forestTokens_length]
    omega
  exact { toEvalsTo := run.toEvalsTo
          steps_le_m := run.steps_le_m.trans (natPolynomial_eval_mono timePolynomial sizeBound) }

omit [DecidableEq K] in
theorem final_other (ports : Ports K) (base : K → List Bool)
    (next : Nat) (roots : List Nat) (records oldRecords : List Bool)
    (k : K) (outside : ∀ t, ports t ≠ k) :
    ForestPlacement.fill ports base (finalLocal next roots records oldRecords) k = base k :=
  ForestPlacement.fill_other ports base _ k outside

@[simp] theorem final_counter (next : Nat) (roots : List Nat) (records oldRecords : List Bool) :
    finalLocal next roots records oldRecords (.lower .remaining) = encodeWord 0 := rfl

theorem final_lower_clean (next : Nat) (roots : List Nat) (records oldRecords : List Bool)
    (tape : PostfixMachine.Tape) (hc : tape ≠ .current) (hr : tape ≠ .remaining) :
    finalLocal next roots records oldRecords (.lower tape) = [] := by
  cases tape <;> simp_all [finalLocal]

@[simp] theorem final_forest_roots {ι : Type} (start : Nat) (es : List (Expr ι))
    (records oldRecords : List Bool) :
    finalLocal (start + Batch.cost es) (Batch.roots start es).reverse records oldRecords
      .rootTable = encodeWords (Batch.roots start es) := by
  simp [finalLocal]

end Caller

def machine {σ : Type} [Fintype σ] (ambient : σ × Bool) : FinTM2 where
  K := Tape
  k₀ := .tokens
  k₁ := .records
  Γ := Alphabet
  Λ := Label
  main := .reverseTokens
  σ := State σ
  initialState := (ambient, none)
  m := program

theorem machine_alphabet_finite {σ : Type} [Fintype σ] (ambient : σ × Bool) :
    ∀ k, Finite ((machine ambient).Γ k) := by
  intro k
  exact inferInstanceAs (Finite Bool)

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage

end OAI
