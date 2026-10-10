import OAI.Computability.BinPacking.CookLevin.ClashMachine
import OAI.Computability.BinPacking.CookLevin.TransitionArena

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceTemplate

open StatementCircuit VerifierCircuit PostfixModel PostfixAlignment InitializationTemplate

local instance (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

def headMask (V : NPVerifier) (k : V.computation.tm.K)
    (symbol : Option (V.computation.tm.Γ k)) : Bool := by
  by_cases h : k = V.computation.tm.k₁
  · subst k
    exact decide (some (V.computation.outputAlphabet.invFun true) = symbol)
  · exact decide ((none : Option (V.computation.tm.Γ k)) = symbol)

theorem accepting_label (V : NPVerifier) (S : Nat) (label : Option V.computation.tm.Λ) :
    configEncoding S (accepting V) (.inl label) = decide (none = label) := rfl

theorem accepting_state (V : NPVerifier) (S : Nat) (state : V.computation.tm.σ) :
    configEncoding S (accepting V) (.inr (.inl state)) =
      decide (V.computation.tm.initialState = state) := rfl

theorem accepting_cell (V : NPVerifier) (S : Nat) (k : V.computation.tm.K)
    (i : Fin S) (symbol : Option (V.computation.tm.Γ k)) :
    configEncoding S (accepting V) (.inr (.inr ⟨k, i, symbol⟩)) =
      if i.val = 0 then headMask V k symbol else decide ((none : Option (V.computation.tm.Γ k)) = symbol) := by
  by_cases hk : k = V.computation.tm.k₁
  · subst k
    rcases i with ⟨i, hi⟩
    cases i <;> simp [configEncoding, inputEncoding, accepting, Turing.haltList,
      StackEncoding.encode, headMask]
  · simp [configEncoding, inputEncoding, accepting, Turing.haltList, hk,
      StackEncoding.encode, headMask]

def targetBit (V : NPVerifier) (input : List Bool) (j : Fin (width V input)) : Bool :=
  configEncoding (capacity V input.length) (accepting V) ((bitEquiv V input).symm j)

def mismatchTokens (expected : Bool) (wire : Nat) : List Token :=
  if expected then [.input wire, .not] else [.input wire]

def tokens (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) : List Token :=
  [.input (wire (Fin.last (width V input)))] ++
    (List.ofFn fun j : Fin (width V input) =>
      mismatchTokens (targetBit V input j) (wire j.castSucc)).flatten ++
    closeOr (width V input) ++ [.not, .and]

theorem mismatchTokens_eq (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) (j : Fin (width V input)) :
    mismatchTokens (targetBit V input j) (wire j.castSucc) =
      exprTokens wire (mismatchExpr V input j) := by
  by_cases h : configEncoding (capacity V input.length) (accepting V)
      ((bitEquiv V input).symm j) = true
  · simp [mismatchTokens, targetBit, mismatchExpr, exprTokens, h]
  · simp [mismatchTokens, targetBit, mismatchExpr, exprTokens, h]

theorem tokens_eq (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) :
    tokens V input wire = exprTokens wire (acceptanceExpr V input) := by
  simp only [acceptanceExpr, exprTokens, exprTokens_disjoin,
    forestTokens_ofFn, List.length_ofFn]
  simp [tokens, mismatchTokens_eq, List.append_assoc]

theorem compile_tokens (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) (start : Nat) (oldRoots : List Nat) :
    compileTokens start oldRoots (tokens V input wire) =
      some (start + (acceptanceExpr V input).size,
        (acceptanceExpr V input).root start :: oldRoots,
        (acceptanceExpr V input).gates wire start) := by
  rw [tokens_eq]
  exact compile_exprTokens wire (acceptanceExpr V input) start oldRoots

theorem tokens_length_le (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) :
    (tokens V input wire).length ≤ 3 * width V input + 4 := by
  rw [tokens_eq, exprTokens_length]
  exact acceptanceExpr_size_le V input

end BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceTemplate

namespace BinPackingGames.Foundations.Complexity.CookLevin.TransitionMachine

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

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem Valid.roots {indexing : ConfigIndex.Indexing Γ Λ σ}
    {plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)} {input : Input}
    (h : Valid indexing plan input) : RootsValid indexing input := by
  unfold Valid at h
  unfold RootsValid
  omega

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
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

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
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

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem dispatchTrace (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (base : Tape → List Bool) (decision : Bool) :
    (advance (TM2.step (program indexing plan)))^[1]
      (some ⟨some .dispatch, (((), decision), none), base⟩) =
      some ⟨some (if decision then .cells (compileList indexing plan.cells).entry
        else .finishTokens (finalEmitter indexing plan).entry), initialState, base⟩ := by
  cases decision <;> rfl

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
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

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
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

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
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

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
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

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
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

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
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

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
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

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
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

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem finalTokens_at_capacity (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) :
    finalTokens indexing plan (withCursor input input.capacity) = carriedTokens indexing plan input := by
  simp [finalTokens, carriedTokens, affineAddress, Position.eval,
    ConfigIndex.Indexing.width, Nat.mul_comm, Nat.add_comm, Nat.add_assoc]

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
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

end BinPackingGames.Foundations.Complexity.CookLevin.TransitionMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.AcceptancePlan

open StatementCircuit TransitionTemplate AcceptanceTemplate
open PostfixModel VerifierCircuit TermMachine

local instance (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

def negateIf {K σ : Type} {Γ : K → Type} (condition : Bool) (e : Term Γ σ) : Term Γ σ :=
  if condition then .not e else e

def stateTemplate (V : NPVerifier) (state : V.computation.tm.σ) :
    Global (Γ := V.computation.tm.Γ) (Λ := V.computation.tm.Λ) (σ := V.computation.tm.σ) :=
  .data (negateIf (decide (V.computation.tm.initialState = state)) (.state state))

def cellTemplate (V : NPVerifier) (k : V.computation.tm.K)
    (symbol : Option (V.computation.tm.Γ k)) :
    Global (Γ := V.computation.tm.Γ) (Λ := V.computation.tm.Λ) (σ := V.computation.tm.σ) :=
  .data (.atZero .current
    (negateIf (headMask V k symbol) (.cell k .current symbol))
    (negateIf (decide ((none : Option (V.computation.tm.Γ k)) = symbol))
      (.cell k .current symbol)))

def plan (V : NPVerifier) :
    TransitionMachine.Plan (Γ := V.computation.tm.Γ) (Λ := V.computation.tm.Λ)
      (σ := V.computation.tm.σ) where
  «prefix» :=
    ((List.finRange (indexing V).labelCount).map fun i =>
      (Global.label ((indexing V).labels.symm i),
        decide ((none : Option V.computation.tm.Λ) = (indexing V).labels.symm i))) ++
    ((List.finRange (indexing V).stateCount).map fun i =>
      (stateTemplate V ((indexing V).states.symm i), false))
  cells := (List.finRange (indexing V).symbolCount).map fun i =>
    let symbol := (indexing V).symbols.symm i
    cellTemplate V symbol.1 symbol.2
  carry := false

def mismatchForest (V : NPVerifier) (roots : List Nat) (S : Nat) : List Token :=
  (outputOrder (indexing V) S).flatMap fun bit =>
    mismatchTokens (configEncoding S (accepting V) bit)
      (configWire (indexing V) roots S bit)

theorem label_tokens (V : NPVerifier) (roots : List Nat) (S cursor : Nat)
    (label : Option V.computation.tm.Λ) :
    (Global.label label).tokens (indexing V) roots S cursor ++
      (if decide ((none : Option V.computation.tm.Λ) = label) then [.not] else []) =
    mismatchTokens (configEncoding S (accepting V) (.inl label))
      (configWire (indexing V) roots S (.inl label)) := by
  rw [accepting_label]
  by_cases h : (none : Option V.computation.tm.Λ) = label
  · simp [Global.tokens, configWire, mismatchTokens, h]
  · simp [Global.tokens, configWire, mismatchTokens, h]

theorem state_tokens (V : NPVerifier) (roots : List Nat) (S cursor : Nat)
    (state : V.computation.tm.σ) :
    (stateTemplate V state).tokens (indexing V) roots S cursor =
      mismatchTokens (configEncoding S (accepting V) (.inr (.inl state)))
        (configWire (indexing V) roots S (.inr (.inl state))) := by
  rw [accepting_state]
  by_cases h : V.computation.tm.initialState = state
  · simp [stateTemplate, negateIf, Global.tokens, Term.tokens, configWire, mismatchTokens, h]
  · simp [stateTemplate, negateIf, Global.tokens, Term.tokens, configWire, mismatchTokens, h]

theorem cell_tokens (V : NPVerifier) (roots : List Nat) (S : Nat)
    (i : Fin S) (k : V.computation.tm.K) (symbol : Option (V.computation.tm.Γ k)) :
    (cellTemplate V k symbol).tokens (indexing V) roots S i.val =
      mismatchTokens (configEncoding S (accepting V) (.inr (.inr ⟨k, i, symbol⟩)))
        (configWire (indexing V) roots S (.inr (.inr ⟨k, i, symbol⟩))) := by
  rw [accepting_cell]
  have hS : 0 < S := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  by_cases hi : i.val = 0
  · cases hb : headMask V k symbol <;>
      simp [cellTemplate, negateIf, Global.tokens, Term.tokens, Position.eval,
        hS, hi, hb, mismatchTokens, configWire]
  · by_cases hs : (none : Option (V.computation.tm.Γ k)) = symbol
    · simp [cellTemplate, negateIf, Global.tokens, Term.tokens, Position.eval,
        i.isLt, hi, hs, mismatchTokens, configWire]
    · simp [cellTemplate, negateIf, Global.tokens, Term.tokens, Position.eval,
        i.isLt, hi, hs, mismatchTokens, configWire]

theorem outputTokens_eq (V : NPVerifier) (input : TermMachine.Input) :
    TransitionMachine.outputTokens (indexing V) (plan V) input =
      mismatchForest V input.roots input.capacity := by
  rw [TransitionMachine.outputTokens_eq_blocks]
  simp only [mismatchForest, OutputOrder.outputOrder_eq_blocks, List.flatMap_append,
    List.flatMap_map, List.flatMap_assoc]
  simp only [plan, TransitionMachine.prefixTokens, List.flatMap_append, List.flatMap_map,
    TransitionMachine.cellTokens, TransitionMachine.listTokens,
    TermMachine.globalTokens, TransitionMachine.withCursor_roots,
    TransitionMachine.withCursor_capacity, TransitionMachine.withCursor_cursor,
    TransitionMachine.carriedTokens, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  congr 1
  · congr 1
    · apply List.flatMap_congr
      intro i _
      exact label_tokens V input.roots input.capacity 0 ((indexing V).labels.symm i)
    · apply List.flatMap_congr
      intro i _
      simpa using state_tokens V input.roots input.capacity 0 ((indexing V).states.symm i)
  · apply List.flatMap_congr
    intro i _
    apply List.flatMap_congr
    intro j _
    exact cell_tokens V input.roots input.capacity i
      ((indexing V).symbols.symm j).1 ((indexing V).symbols.symm j).2

theorem mismatchForest_circuit (V : NPVerifier) (input : List Bool) (roots : List Nat) :
    mismatchForest V roots (capacity V input.length) =
      (List.ofFn fun j : Fin (width V input) =>
        mismatchTokens (targetBit V input j) (rootLookup roots j.val)).flatten := by
  simp only [mismatchForest, outputOrder, List.flatMap_def,
    Function.comp_def, configWire, Equiv.apply_symm_apply, targetBit,
    ← List.ofFn_eq_map, List.map_ofFn, bitEquiv]

theorem fullTokens_eq (V : NPVerifier) (input : List Bool) (roots : List Nat) :
    AcceptanceTemplate.tokens V input (fun j => rootLookup roots j.val) =
      [.input (rootLookup roots (width V input))] ++
      TransitionMachine.outputTokens (indexing V) (plan V)
        ⟨0, capacity V input.length, roots⟩ ++
      InitializationTemplate.closeOr (width V input) ++ [.not, .and] := by
  rw [outputTokens_eq, mismatchForest_circuit]
  rfl

end BinPackingGames.Foundations.Complexity.CookLevin.AcceptancePlan

namespace BinPackingGames.Foundations.Complexity.CookLevin.TransitionIteration

open Turing MachineComposition StatementCircuit CircuitBatch TransitionTemplate

open TransitionArena

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

end BinPackingGames.Foundations.Complexity.CookLevin.TransitionIteration

end

end OAI
