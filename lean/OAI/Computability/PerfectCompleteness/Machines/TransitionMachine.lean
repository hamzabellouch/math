import OAI.Computability.PerfectCompleteness.Machines.OutputOrder
import OAI.Computability.PerfectCompleteness.Machines.TermMachine

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionMachine


open Turing MachineComposition TransitionTemplate TermMachine PostfixModel

variable {K Λ σ : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, DecidableEq (Γ k)] [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ]

abbrev Template := Global (Γ := Γ) (Λ := Λ) (σ := σ)

def listTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (terms : List (Template (Γ := Γ) (Λ := Λ) (σ := σ))) (input : Input) : List Token :=
  terms.flatMap fun term => globalTokens indexing term input

def compileList (indexing : ConfigIndex.Indexing Γ Λ σ) :
    (terms : List (Template (Γ := Γ) (Λ := Λ) (σ := σ))) →
      Emitter (RootsValid indexing) (listTokens indexing terms)
  | [] => (Emitter.literal (RootsValid indexing) []).congr (fun _ => rfl)
  | term :: terms => ((compileGlobal indexing term).seq (compileList indexing terms)).congr
      (fun _ => rfl)

def prefixTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (terms : List (Template (Γ := Γ) (Λ := Λ) (σ := σ) × Bool))
    (input : Input) : List Token :=
  terms.flatMap fun term => globalTokens indexing term.1 input ++
    (if term.2 then [.not] else [])

def compilePrefix (indexing : ConfigIndex.Indexing Γ Λ σ) :
    (terms : List (Template (Γ := Γ) (Λ := Λ) (σ := σ) × Bool)) →
      Emitter (RootsValid indexing) (prefixTokens indexing terms)
  | [] => (Emitter.literal (RootsValid indexing) []).congr (fun _ => rfl)
  | term :: terms =>
      (((compileGlobal indexing term.1).seq
        (Emitter.literal (RootsValid indexing) (if term.2 then [.not] else []))).seq
          (compilePrefix indexing terms)).congr (fun _ => rfl)

def withCursor (input : Input) (cursor : Nat) : Input := { input with cursor := cursor }

def cursorTapes (base : Tape → List Bool) (cursor : Nat) : Tape → List Bool :=
  Function.update base .cursor (encodeWord cursor)

@[simp] theorem withCursor_cursor (input : Input) (cursor : Nat) :
    (withCursor input cursor).cursor = cursor := rfl

@[simp] theorem withCursor_capacity (input : Input) (cursor : Nat) :
    (withCursor input cursor).capacity = input.capacity := rfl

@[simp] theorem withCursor_roots (input : Input) (cursor : Nat) :
    (withCursor input cursor).roots = input.roots := rfl

@[simp] theorem withCursor_withCursor (input : Input) (first second : Nat) :
    withCursor (withCursor input first) second = withCursor input second := rfl

theorem Frame.cursor {input : Input} {base : Tape → List Bool}
    (frame : Frame input base) (cursor : Nat) :
    Frame (withCursor input cursor) (cursorTapes base cursor) := by
  refine ⟨by simp [cursorTapes], ?_, ?_, ?_⟩
  · simpa [cursorTapes] using frame.capacityWord
  · simpa [cursorTapes] using frame.rootsWord
  · intro tape ht
    have hc : tape ≠ .cursor := by intro h; subst tape; simp [work] at ht
    simpa [cursorTapes, hc] using frame.clean tape ht

@[simp] theorem cursorTapes_same {input : Input} {base : Tape → List Bool}
    (frame : Frame input base) : cursorTapes base input.cursor = base := by
  simp only [cursorTapes, ← frame.cursorWord, Function.update_eq_self]

@[simp] theorem cursorTapes_twice (base : Tape → List Bool) (first second : Nat) :
    cursorTapes (cursorTapes base first) second = cursorTapes base second := by
  simp [cursorTapes]

theorem emitTapes_cursor (base : Tape → List Bool) (cursor : Nat) (tokens : List Token) :
    emitTapes (cursorTapes base cursor) tokens = cursorTapes (emitTapes base tokens) cursor := by
  funext tape
  cases tape <;> simp [cursorTapes, emitTapes]

structure Plan where
  «prefix» : List (Template (Γ := Γ) (Λ := Λ) (σ := σ) × Bool)
  cells : List (Template (Γ := Γ) (Λ := Λ) (σ := σ))
  carry : Bool

def Valid (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) : Prop :=
  indexing.width input.capacity + (if plan.carry then 1 else 0) ≤ input.roots.length

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [∀ index, DecidableEq (Γ index)]
  [∀ index, Fintype (Γ index)] [DecidableEq Λ] [Fintype Λ] in
theorem Valid.roots {indexing : ConfigIndex.Indexing Γ Λ σ}
    {plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)} {input : Input}
    (h : Valid indexing plan input) : RootsValid indexing input := by
  unfold Valid at h
  unfold RootsValid
  omega

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [∀ index, DecidableEq (Γ index)]
  [∀ index, Fintype (Γ index)] [DecidableEq Λ] [Fintype Λ] in
theorem Valid.withCursor {indexing : ConfigIndex.Indexing Γ Λ σ}
    {plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)} {input : Input}
    (h : Valid indexing plan input) (cursor : Nat) :
    Valid indexing plan (withCursor input cursor) := h

def finalValid (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) : Prop :=
  Valid indexing plan input ∧ input.cursor = input.capacity

def finalTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) : List Token :=
  if plan.carry then [.input (rootLookup input.roots
    (affineAddress .current indexing.symbolCount (indexing.labelCount + indexing.stateCount) input))]
  else []

def finalEmitter (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) :
    Emitter (finalValid indexing plan) (finalTokens indexing plan) := by
  cases hc : plan.carry with
  | false =>
      exact (Emitter.literal (finalValid indexing plan) []).congr (fun input => by
        simp [finalTokens, hc])
  | true =>
      let emitter := Emitter.affineRoot (finalValid indexing plan) .current indexing.symbolCount
        (indexing.labelCount + indexing.stateCount) (by
          intro input hv
          have haddr : affineAddress .current indexing.symbolCount
              (indexing.labelCount + indexing.stateCount) input = indexing.width input.capacity := by
            simp [affineAddress, Position.eval, hv.2, ConfigIndex.Indexing.width,
              Nat.mul_comm, Nat.add_comm, Nat.add_assoc]
          have hlt : indexing.width input.capacity < input.roots.length := by
            have h := hv.1
            simp only [Valid, hc, ite_true] at h
            omega
          rw [haddr]
          simp only [rootLookup, List.getElem?_eq_getElem hlt, Option.getD_some])
      exact emitter.congr (fun input => by simp [finalTokens, hc])

def guard : Selector (testPredicate true .current) := Selector.positionTest true .current

inductive Label (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ))
  | prefix (label : (compilePrefix indexing plan.prefix).Label)
  | test (label : guard.Label)
  | dispatch
  | cells (label : (compileList indexing plan.cells).Label)
  | increment
  | finishTokens (label : (finalEmitter indexing plan).Label)
  | drain | finish
  deriving Fintype

attribute [-instance] instFintypeLabel

instance labelFintype (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) : Fintype (Label indexing plan) :=
  Fintype.ofEquiv
    ((compilePrefix indexing plan.prefix).Label ⊕ guard.Label ⊕ Unit ⊕
      (compileList indexing plan.cells).Label ⊕ Unit ⊕ (finalEmitter indexing plan).Label ⊕ Unit ⊕ Unit)
    (Label.proxyTypeEquiv indexing plan)

def program (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) :
    Label indexing plan → TM2.Stmt Alphabet (Label indexing plan) State
  | .prefix label => MachineSubroutine.statement Label.prefix (some (.test guard.entry))
      ((compilePrefix indexing plan.prefix).program label)
  | .test label => MachineSubroutine.statement Label.test (some .dispatch) (guard.program label)
  | .dispatch => .branch (fun state => state.1.2)
      (.load (fun _ => initialState) (.goto fun _ => .cells (compileList indexing plan.cells).entry))
      (.load (fun _ => initialState) (.goto fun _ => .finishTokens (finalEmitter indexing plan).entry))
  | .cells label => MachineSubroutine.statement Label.cells (some .increment)
      ((compileList indexing plan.cells).program label)
  | .increment => .push .cursor (fun _ => true) (.goto fun _ => .test guard.entry)
  | .finishTokens label => MachineSubroutine.statement Label.finishTokens (some .drain)
      ((finalEmitter indexing plan).program label)
  | .drain => MachineDrain.drain .cursor .drain (some .finish)
  | .finish => .push .cursor (fun _ => false) (.load (fun _ => initialState) .halt)

def machine (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) : FinTM2 := by
  letI := (compilePrefix indexing plan.prefix).finite
  letI := guard.finite
  letI := (compileList indexing plan.cells).finite
  letI := (finalEmitter indexing plan).finite
  exact {
    K := Tape
    k₀ := .cursor
    k₁ := .reversed
    Γ := Alphabet
    Λ := Label indexing plan
    main := .prefix (compilePrefix indexing plan.prefix).entry
    σ := State
    initialState := initialState
    m := program indexing plan }

def cellTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) (cursor : Nat) : List Token :=
  listTokens indexing plan.cells (withCursor input cursor)

def remainingTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) : Nat → Nat → List Token
  | cursor, 0 => finalTokens indexing plan (withCursor input cursor)
  | cursor, remaining + 1 => cellTokens indexing plan input cursor ++
      remainingTokens indexing plan input (cursor + 1) remaining

def loopSteps (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) : Nat → Nat → Nat
  | cursor, 0 => guard.steps (withCursor input cursor) + 1 +
      (finalEmitter indexing plan).steps (withCursor input cursor) + (cursor + 2) + 1
  | cursor, remaining + 1 => guard.steps (withCursor input cursor) + 1 +
      (compileList indexing plan.cells).steps (withCursor input cursor) + 1 +
      loopSteps indexing plan input (cursor + 1) remaining

private theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [∀ index, DecidableEq (Γ index)]
  [∀ index, Fintype (Γ index)] [DecidableEq Λ] [Fintype Λ] in
theorem guardTrace (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input)
    (base : Tape → List Bool) (frame : Frame input base) :
    (advance (TM2.step (program indexing plan)))^[guard.steps input]
      (some ⟨some (.test guard.entry), initialState, base⟩) =
      some ⟨some .dispatch, (((), decide (input.cursor < input.capacity)), none), base⟩ := by
  have h := MachineSubroutine.trace Label.test (some Label.dispatch) guard.program
    (program indexing plan) (fun _ => rfl) (guard.steps input) _ _
    (guard.trace input base frame)
  simpa [MachineSubroutine.configuration, MachineSubroutine.label, testPredicate, Position.eval]
    using! h

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [∀ index, DecidableEq (Γ index)]
  [∀ index, Fintype (Γ index)] [DecidableEq Λ] [Fintype Λ] in
theorem dispatchTrace (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (base : Tape → List Bool) (decision : Bool) :
    (advance (TM2.step (program indexing plan)))^[1]
      (some ⟨some .dispatch, (((), decision), none), base⟩) =
      some ⟨some (if decision then .cells (compileList indexing plan.cells).entry
        else .finishTokens (finalEmitter indexing plan).entry), initialState, base⟩ := by
  cases decision <;> rfl

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [∀ index, DecidableEq (Γ index)]
  [∀ index, Fintype (Γ index)] [DecidableEq Λ] [Fintype Λ] in
theorem incrementTrace (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input)
    (base : Tape → List Bool) (frame : Frame input base) :
    (advance (TM2.step (program indexing plan)))^[1]
      (some ⟨some .increment, initialState, base⟩) =
      some ⟨some (.test guard.entry), initialState, cursorTapes base (input.cursor + 1)⟩ := by
  have hw : true :: base .cursor = encodeWord (input.cursor + 1) := by
    rw [frame.cursorWord]
    simp [encodeWord, List.replicate_succ]
  change some (TM2.stepAux (program indexing plan .increment) initialState base) = _
  simp [program, TM2.stepAux, cursorTapes, hw]

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [∀ index, DecidableEq (Γ index)]
  [∀ index, Fintype (Γ index)] [DecidableEq Λ] [Fintype Λ] in
theorem resetTrace (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input)
    (base : Tape → List Bool) (frame : Frame input base) :
    (advance (TM2.step (program indexing plan)))^[input.cursor + 3]
      (some ⟨some .drain, initialState, base⟩) =
      some ⟨none, initialState, cursorTapes base 0⟩ := by
  have drain := MachineDrain.drainTrace .cursor Label.drain (some Label.finish)
    (program indexing plan) rfl base (encodeWord input.cursor) ((), false) none
  have heq : Function.update base .cursor (encodeWord input.cursor) = base := by
    rw [← frame.cursorWord, Function.update_eq_self]
  rw [heq, encodeWord_length] at drain
  have finish : (advance (TM2.step (program indexing plan)))^[1]
      (some ⟨some .finish, initialState, Function.update base .cursor []⟩) =
      some ⟨none, initialState, cursorTapes base 0⟩ := by
    change some (TM2.stepAux (program indexing plan .finish) initialState _) = _
    simp [program, TM2.stepAux, cursorTapes, encodeWord]
  simpa [Nat.add_assoc, initialState] using trace_trans _ drain finish

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [∀ index, DecidableEq (Γ index)]
  [∀ index, Fintype (Γ index)] [DecidableEq Λ] [Fintype Λ] in
theorem loopTrace (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input)
    (valid : Valid indexing plan input) (cursor remaining : Nat)
    (hcapacity : cursor + remaining = input.capacity)
    (base : Tape → List Bool) (frame : Frame (withCursor input cursor) base) :
    (advance (TM2.step (program indexing plan)))^[loopSteps indexing plan input cursor remaining]
      (some ⟨some (.test guard.entry), initialState, base⟩) =
      some ⟨none, initialState,
        cursorTapes (emitTapes base (remainingTokens indexing plan input cursor remaining)) 0⟩ := by
  induction remaining generalizing cursor base with
  | zero =>
      have hc : cursor = input.capacity := by omega
      have hg := guardTrace indexing plan (withCursor input cursor) base frame
      have hd := dispatchTrace indexing plan base false
      have hfalse : decide ((withCursor input cursor).cursor <
          (withCursor input cursor).capacity) = false := by simp [hc]
      rw [hfalse] at hg
      simp only [Bool.false_eq_true, ite_false] at hd
      have hv : finalValid indexing plan (withCursor input cursor) := ⟨valid.withCursor cursor, hc⟩
      have hf := (finalEmitter indexing plan).traceAt Label.finishTokens (some Label.drain)
        (program indexing plan) (fun _ => rfl) (withCursor input cursor) hv base frame
      have hr := resetTrace indexing plan (withCursor input cursor)
        (emitTapes base (finalTokens indexing plan (withCursor input cursor)))
        (frame.emit (finalTokens indexing plan (withCursor input cursor)))
      have total := trace_trans _ (trace_trans _ (trace_trans _ hg hd) hf) hr
      simpa only [loopSteps, remainingTokens, withCursor_cursor, Nat.add_assoc] using total
  | succ remaining ih =>
      have hc : cursor < input.capacity := by omega
      have hg := guardTrace indexing plan (withCursor input cursor) base frame
      have hd := dispatchTrace indexing plan base true
      have htrue : decide ((withCursor input cursor).cursor <
          (withCursor input cursor).capacity) = true := by simp [hc]
      rw [htrue] at hg
      simp only [ite_true] at hd
      have hb := (compileList indexing plan.cells).traceAt Label.cells (some Label.increment)
        (program indexing plan) (fun _ => rfl) (withCursor input cursor)
        (valid.withCursor cursor).roots base frame
      have hi := incrementTrace indexing plan (withCursor input cursor)
        (emitTapes base (cellTokens indexing plan input cursor))
        (frame.emit (cellTokens indexing plan input cursor))
      have hn := ih (cursor + 1) (by omega)
        (cursorTapes (emitTapes base (cellTokens indexing plan input cursor)) (cursor + 1))
        (by simpa only [withCursor_withCursor] using
          Frame.cursor (frame.emit (cellTokens indexing plan input cursor)) (cursor + 1))
      have total := trace_trans _ (trace_trans _ (trace_trans _ (trace_trans _ hg hd) hb) hi) hn
      simpa only [loopSteps, remainingTokens, cellTokens, withCursor_cursor,
        emitTapes_cursor, cursorTapes_twice, emitTapes_append, Nat.add_assoc] using total

def outputTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) : List Token :=
  prefixTokens indexing plan.prefix (withCursor input 0) ++
    remainingTokens indexing plan input 0 input.capacity

def steps (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) : Nat :=
  (compilePrefix indexing plan.prefix).steps (withCursor input 0) +
    loopSteps indexing plan input 0 input.capacity

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [∀ index, DecidableEq (Γ index)]
  [∀ index, Fintype (Γ index)] [DecidableEq Λ] [Fintype Λ] in
theorem fullTrace (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input)
    (valid : Valid indexing plan input) (base : Tape → List Bool)
    (frame : Frame (withCursor input 0) base) :
    (advance (TM2.step (program indexing plan)))^[steps indexing plan input]
      (some ⟨some (.prefix (compilePrefix indexing plan.prefix).entry), initialState, base⟩) =
      some ⟨none, initialState, emitTapes base (outputTokens indexing plan input)⟩ := by
  have hp := (compilePrefix indexing plan.prefix).traceAt Label.prefix (some (.test guard.entry))
    (program indexing plan) (fun _ => rfl) (withCursor input 0)
    (valid.withCursor 0).roots base frame
  have hl := loopTrace indexing plan input valid 0 input.capacity (by omega)
    (emitTapes base (prefixTokens indexing plan.prefix (withCursor input 0)))
    (frame.emit (prefixTokens indexing plan.prefix (withCursor input 0)))
  have hc : cursorTapes base 0 = base := cursorTapes_same frame
  simpa only [steps, emitTapes_append, ← emitTapes_cursor, hc, outputTokens]
    using trace_trans _ hp hl

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [∀ index, DecidableEq (Γ index)]
  [∀ index, Fintype (Γ index)] [DecidableEq Λ] [Fintype Λ] in
theorem traceAt {Caller : Type} (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ))
    (labels : Label indexing plan → Caller) (exit : Option Caller)
    (target : Caller → TM2.Stmt Alphabet Caller State)
    (code : ∀ label, target (labels label) =
      MachineSubroutine.statement labels exit (program indexing plan label))
    (input : Input) (valid : Valid indexing plan input) (base : Tape → List Bool)
    (frame : Frame (withCursor input 0) base) :
    (advance (TM2.step target))^[steps indexing plan input]
      (some ⟨some (labels (.prefix (compilePrefix indexing plan.prefix).entry)), initialState, base⟩) =
      some ⟨exit, initialState, emitTapes base (outputTokens indexing plan input)⟩ := by
  have h := MachineSubroutine.trace labels exit (program indexing plan) target code
    (steps indexing plan input) _ _ (fullTrace indexing plan input valid base frame)
  simpa only [MachineSubroutine.configuration, MachineSubroutine.label] using h

def loopConstant (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) : Nat :=
  guard.constant + (compileList indexing plan.cells).constant +
    (finalEmitter indexing plan).constant + 5

def dataSize (input : Input) : Nat := input.capacity + (encodeWords input.roots).length

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [∀ index, DecidableEq (Γ index)]
  [∀ index, Fintype (Γ index)] [DecidableEq Λ] [Fintype Λ] in
theorem loopSteps_le (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input)
    (valid : Valid indexing plan input) (cursor remaining : Nat)
    (hcapacity : cursor + remaining = input.capacity) :
    loopSteps indexing plan input cursor remaining ≤
      (remaining + 1) * loopConstant indexing plan *
        (2 * input.capacity + (encodeWords input.roots).length + 1) := by
  let B := 2 * input.capacity + (encodeWords input.roots).length + 1
  have hB : 1 ≤ B := by dsimp [B]; omega
  induction remaining generalizing cursor with
  | zero =>
      have hc : cursor = input.capacity := by omega
      have hs : (withCursor input cursor).size + 1 ≤ B := by simp [Input.size, B]; omega
      have hg := guard.bound (withCursor input cursor)
      have hf := (finalEmitter indexing plan).bound (withCursor input cursor)
        ⟨valid.withCursor cursor, hc⟩
      have hg' := hg.trans (Nat.mul_le_mul_left guard.constant hs)
      have hf' := hf.trans (Nat.mul_le_mul_left (finalEmitter indexing plan).constant hs)
      have hcB : cursor ≤ B := by dsimp [B]; omega
      simp only [loopSteps, Nat.zero_add, Nat.one_mul]
      change _ ≤ loopConstant indexing plan * B
      dsimp [loopConstant]
      nlinarith [Nat.zero_le ((compileList indexing plan.cells).constant * B)]
  | succ remaining ih =>
      have hc : cursor ≤ input.capacity := by omega
      have hs : (withCursor input cursor).size + 1 ≤ B := by simp [Input.size, B]; omega
      have hg := guard.bound (withCursor input cursor)
      have hb := (compileList indexing plan.cells).bound (withCursor input cursor)
        (valid.withCursor cursor).roots
      have hg' := hg.trans (Nat.mul_le_mul_left guard.constant hs)
      have hb' := hb.trans (Nat.mul_le_mul_left (compileList indexing plan.cells).constant hs)
      have hi := ih (cursor + 1) (by omega)
      simp only [loopSteps]
      have hstep : guard.steps (withCursor input cursor) + 1 +
          (compileList indexing plan.cells).steps (withCursor input cursor) + 1 ≤
          loopConstant indexing plan * B := by
        dsimp [loopConstant]
        nlinarith [Nat.zero_le ((finalEmitter indexing plan).constant * B)]
      calc
        _ ≤ loopConstant indexing plan * B + (remaining + 1) * loopConstant indexing plan * B :=
          Nat.add_le_add hstep hi
        _ = _ := by dsimp [B]; ring

def timeConstant (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) : Nat :=
  2 * ((compilePrefix indexing plan.prefix).constant + loopConstant indexing plan)

noncomputable def timePolynomial (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) : Polynomial Nat :=
  Polynomial.C (timeConstant indexing plan) * (Polynomial.X + 1)^2

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [∀ index, DecidableEq (Γ index)]
  [∀ index, Fintype (Γ index)] [DecidableEq Λ] [Fintype Λ] in
theorem steps_le (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input)
    (valid : Valid indexing plan input) :
    steps indexing plan input ≤ timeConstant indexing plan * (dataSize input + 1)^2 := by
  have hp := (compilePrefix indexing plan.prefix).bound (withCursor input 0)
    (valid.withCursor 0).roots
  have hl := loopSteps_le indexing plan input valid 0 input.capacity (by omega)
  have hcap : input.capacity + 1 ≤ dataSize input + 1 := by simp [dataSize]
  have hdata : 2 * input.capacity + (encodeWords input.roots).length + 1 ≤
      2 * (dataSize input + 1) := by unfold dataSize; omega
  have hmul := Nat.mul_le_mul hcap hdata
  have hp' : (compilePrefix indexing plan.prefix).steps (withCursor input 0) ≤
      (compilePrefix indexing plan.prefix).constant * (dataSize input + 1) := by
    simpa [withCursor, Input.size, dataSize] using hp
  have hprod := Nat.mul_le_mul_left (loopConstant indexing plan) hmul
  have hsq : dataSize input + 1 ≤ (dataSize input + 1)^2 := by nlinarith
  have hprefix := Nat.mul_le_mul_left (compilePrefix indexing plan.prefix).constant hsq
  unfold steps timeConstant
  nlinarith

def inPolynomialTime (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input)
    (valid : Valid indexing plan input) (base : Tape → List Bool)
    (frame : Frame (withCursor input 0) base) :
    StateTransition.EvalsToInTime (machine indexing plan).step
      ⟨some (Label.prefix (compilePrefix indexing plan.prefix).entry), initialState, base⟩
      (some ⟨none, initialState, emitTapes base (outputTokens indexing plan input)⟩)
      ((timePolynomial indexing plan).eval (dataSize input)) where
  steps := steps indexing plan input
  evals_in_steps := fullTrace indexing plan input valid base frame
  steps_le_m := by
    simpa only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
      using steps_le indexing plan input valid

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [∀ index, DecidableEq (Γ index)]
  [∀ index, Fintype (Γ index)] [DecidableEq Λ] [Fintype Λ] in
theorem remainingTokens_eq_range (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) (cursor remaining : Nat) :
    remainingTokens indexing plan input cursor remaining =
      ((List.range' cursor remaining).flatMap (cellTokens indexing plan input)) ++
        finalTokens indexing plan (withCursor input (cursor + remaining)) := by
  induction remaining generalizing cursor with
  | zero => simp [remainingTokens]
  | succ remaining ih =>
      simp [remainingTokens, List.range'_succ, ih, List.append_assoc,
        Nat.add_comm, Nat.add_left_comm]

def carriedTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) : List Token :=
  if plan.carry then [.input (rootLookup input.roots (indexing.width input.capacity))] else []

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [∀ index, DecidableEq (Γ index)]
  [∀ index, Fintype (Γ index)] [DecidableEq Λ] [Fintype Λ] in
theorem finalTokens_at_capacity (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) :
    finalTokens indexing plan (withCursor input input.capacity) = carriedTokens indexing plan input := by
  simp [finalTokens, carriedTokens, affineAddress, Position.eval,
    ConfigIndex.Indexing.width, Nat.mul_comm, Nat.add_comm, Nat.add_assoc]

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [∀ index, DecidableEq (Γ index)]
  [∀ index, Fintype (Γ index)] [DecidableEq Λ] [Fintype Λ] in
theorem outputTokens_eq_blocks (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) :
    outputTokens indexing plan input =
      prefixTokens indexing plan.prefix (withCursor input 0) ++
      ((List.finRange input.capacity).flatMap fun cursor =>
        cellTokens indexing plan input cursor.val) ++ carriedTokens indexing plan input := by
  rw [outputTokens, remainingTokens_eq_range]
  simp only [Nat.zero_add, finalTokens_at_capacity]
  rw [← List.range_eq_range', ← List.map_coe_finRange_eq_range, List.flatMap_map]
  simp only [List.append_assoc]

def transitionPrefixKinds (indexing : ConfigIndex.Indexing Γ Λ σ) : List (OutputKind Γ Λ σ) :=
  ((List.finRange indexing.labelCount).map fun i => .inl (indexing.labels.symm i)) ++
    ((List.finRange indexing.stateCount).map fun i => .inr (.inl (indexing.states.symm i)))

def transitionCellKinds (indexing : ConfigIndex.Indexing Γ Λ σ) : List (OutputKind Γ Λ σ) :=
  (List.finRange indexing.symbolCount).map fun i => .inr (.inr (indexing.symbols.symm i))

noncomputable def transitionPlan (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) : Plan (Γ := Γ) (Λ := Λ) (σ := σ) where
  «prefix» := (transitionPrefixKinds indexing).map fun kind => (sticky machineProgram kind, false)
  cells := (transitionCellKinds indexing).map (sticky machineProgram)
  carry := true

theorem transition_outputTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (input : Input) :
    outputTokens indexing (transitionPlan indexing machineProgram) input =
      TransitionTemplate.forestTokens indexing input.roots input.capacity machineProgram ++
        [.input (rootLookup input.roots (indexing.width input.capacity))] := by
  rw [outputTokens_eq_blocks]
  simp [transitionPlan, transitionPrefixKinds, transitionCellKinds,
    prefixTokens, listTokens, cellTokens, globalTokens, carriedTokens,
    TransitionTemplate.forestTokens, OutputOrder.outputOrder_eq_blocks,
    List.flatMap_append, List.flatMap_map, List.flatMap_assoc, withCursor, bitKind, bitCursor,
    List.append_assoc]

noncomputable def transitionInPolynomialTime (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (input : Input)
    (valid : indexing.width input.capacity + 1 ≤ input.roots.length)
    (base : Tape → List Bool) (frame : Frame (withCursor input 0) base) :
    StateTransition.EvalsToInTime (machine indexing (transitionPlan indexing machineProgram)).step
      ⟨some (Label.prefix (compilePrefix indexing (transitionPlan indexing machineProgram).prefix).entry),
        initialState, base⟩
      (some ⟨none, initialState, emitTapes base
        (TransitionTemplate.forestTokens indexing input.roots input.capacity machineProgram ++
          [.input (rootLookup input.roots (indexing.width input.capacity))])⟩)
      ((timePolynomial indexing (transitionPlan indexing machineProgram)).eval (dataSize input)) := by
  have hv : Valid indexing (transitionPlan indexing machineProgram) input := by
    simpa only [Valid, transitionPlan, ite_true] using valid
  simpa only [transition_outputTokens] using
    inPolynomialTime indexing (transitionPlan indexing machineProgram) input hv base frame

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionMachine

end OAI
