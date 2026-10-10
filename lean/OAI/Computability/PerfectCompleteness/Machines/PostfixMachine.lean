import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import OAI.Computability.PerfectCompleteness.Machines.PositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineCopy
import OAI.Computability.UniqueGames.Machines.MachineDrain
import OAI.Computability.UniqueGames.Machines.MachineInitialHeaders
import OAI.Computability.UniqueGames.Machines.MachineLemmas
import OAI.Computability.UniqueGames.PCP.SourceMachine

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.PostfixMachine

open Turing PostfixModel Hastad


inductive Tape
  | input | current | remaining | roots | left | right | reversed | output | scratch
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .current, .remaining, .roots, .left,
  .right, .reversed, .output, .scratch]

protected theorem Tape.enumList_getElem?_ctorIdx_eq (x : Tape) :
    Tape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Tape) := Bool
abbrev State := Unit × Option Bool

inductive Label
  | headerStart (slot : Fin 2) | headerLoop (slot : Fin 2)
  | guard | decode
  | readStart (tag : Fin 6) (pass : Fin 2) | readLoop (tag : Fin 6) (pass : Fin 2)
  | emitTag (tag : Fin 6)
  | field (tag : Fin 6) (slot : Fin 3)
  | restore (tag : Fin 6) (slot : Fin 3)
  | closeField (tag : Fin 6) (slot : Fin 3)
  | rootDrain | rootFork | increment | clearLeft | clearRight | finish | finalReverse
  deriving DecidableEq, Fintype

def initialState : State := ((), none)

def headerTape (slot : Fin 2) : Tape := if slot.val = 0 then .current else .remaining

def binary (tag : Fin 6) : Bool := decide (tag.val = 3 ∨ tag.val = 4)

def readSource (tag : Fin 6) : Tape := if tag.val = 5 then .input else .roots

def readDestination (tag : Fin 6) (pass : Fin 2) : Tape :=
  if binary tag && decide (pass.val = 0) then .right else .left

def readNext (tag : Fin 6) (pass : Fin 2) : Label :=
  if binary tag && decide (pass.val = 0) then .readStart tag 1 else .emitTag tag

def prepare (tag : Fin 6) : Label :=
  if tag.val < 2 then .emitTag tag else .readStart tag 0

def gateTag (tag : Fin 6) : Nat := if tag.val = 5 then 4 else tag.val

def fieldSource (tag : Fin 6) (slot : Fin 3) : Tape :=
  if slot.val = 0 then .current
  else if slot.val = 1 ∨ tag.val = 5 then .left else .right

def fieldUnused (tag : Fin 6) (slot : Fin 3) : Bool :=
  decide (slot.val ≠ 0 ∧ (tag.val < 2 ∨ (tag.val = 2 ∧ slot.val = 2)))

def fieldNext (tag : Fin 6) (slot : Fin 3) : Label :=
  if h : slot.val + 1 < 3 then .field tag ⟨slot.val + 1, h⟩ else .rootDrain

def resetGoto (label : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => initialState) (.goto fun _ => label)

def tagDecoder : Nat → Fin 6 → TM2.Stmt Alphabet Label State
  | 0, tag => .pop .input (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false) (.halt) (resetGoto (prepare tag)))
  | fuel + 1, tag => .pop .input (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (tagDecoder fuel ⟨min (tag.val + 1) 5, by omega⟩) (resetGoto (prepare tag)))

def program : Label → TM2.Stmt Alphabet Label State
  | .headerStart slot => SourceMachine.fieldStart (headerTape slot) (.headerLoop slot)
  | .headerLoop slot => SourceMachine.fieldLoop .input (headerTape slot) (.headerLoop slot)
      (some (if slot.val = 0 then .headerStart 1 else .guard))
  | .guard => MachineUnaryCounter.guard .remaining .decode .finish
  | .decode => tagDecoder 5 0
  | .readStart tag pass => SourceMachine.fieldStart (readDestination tag pass) (.readLoop tag pass)
  | .readLoop tag pass => SourceMachine.fieldLoop (readSource tag) (readDestination tag pass)
      (.readLoop tag pass) (some (readNext tag pass))
  | .emitTag tag => Reduction.MachineSubstitution.pushWord .reversed (encodeWord (gateTag tag))
      (.goto fun _ => .field tag 0)
  | .field tag slot =>
      if fieldUnused tag slot then
        .push .reversed (fun _ => false) (.goto fun _ => fieldNext tag slot)
      else MachineInitialHeaders.prefixScan (fieldSource tag slot) .scratch .reversed 1
        (.field tag slot) (.restore tag slot)
  | .restore tag slot => Reduction.MachineTransfer.loopAt .scratch (fieldSource tag slot)
      id false (.restore tag slot) (some (.closeField tag slot))
  | .closeField tag slot => .push .reversed (fun _ => false) (.goto fun _ => fieldNext tag slot)
  | .rootDrain => Reduction.MachineTransfer.loopAt .current .scratch id false
      .rootDrain (some .rootFork)
  | .rootFork => MachineCopy.forkLoop .scratch .current .roots false .rootFork (some .increment)
  | .increment => .push .current (fun _ => true) (.goto fun _ => .clearLeft)
  | .clearLeft => MachineDrain.drain .left .clearLeft (some .clearRight)
  | .clearRight => MachineDrain.drain .right .clearRight (some .guard)
  | .finish => .pop .remaining (fun _ _ => initialState) (.goto fun _ => .finalReverse)
  | .finalReverse => Reduction.MachineTransfer.loopAt .reversed .output id false .finalReverse none

def machine : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .headerStart 0
  σ := State
  initialState := initialState
  m := program

private abbrev advance := MachineComposition.advance (TM2.step program)

def outputTapes (base : Tape → List Bool) (bits : List Bool) : Tape → List Bool :=
  Function.update base .reversed (bits ++ base .reversed)

@[simp] theorem outputTapes_reversed (base : Tape → List Bool) (bits : List Bool) :
    outputTapes base bits .reversed = bits ++ base .reversed := by simp [outputTapes]

theorem outputTapes_other (base : Tape → List Bool) (bits : List Bool) (tape : Tape)
    (h : tape ≠ .reversed) : outputTapes base bits tape = base tape := by
  simp [outputTapes, h]

@[simp] theorem outputTapes_twice (base : Tape → List Bool) (first second : List Bool) :
    outputTapes (outputTapes base first) second = outputTapes base (second ++ first) := by
  funext tape
  by_cases h : tape = .reversed
  · subst tape; simp [List.append_assoc]
  · simp [outputTapes, h]

private theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem readSource_ne_destination (tag : Fin 6) (pass : Fin 2) :
    readSource tag ≠ readDestination tag pass := by
  unfold readSource readDestination
  split <;> split <;> decide

theorem fieldSource_ne_scratch (tag : Fin 6) (slot : Fin 3) :
    fieldSource tag slot ≠ .scratch := by
  unfold fieldSource
  split <;> first | decide | (split <;> decide)

theorem fieldSource_ne_reversed (tag : Fin 6) (slot : Fin 3) :
    fieldSource tag slot ≠ .reversed := by
  unfold fieldSource
  split <;> first | decide | (split <;> decide)

theorem decodeTrace (tag : Fin 6) (base : Tape → List Bool) (suffix : List Bool)
    (hinput : base .input = encodeWord tag.val ++ suffix) :
    advance^[1] (some ⟨some .decode, initialState, base⟩) =
      some ⟨some (prepare tag), initialState, Function.update base .input suffix⟩ := by
  change some (TM2.stepAux (program .decode) initialState base) = _
  fin_cases tag <;>
    simp [program, tagDecoder, TM2.stepAux, hinput, encodeWord, resetGoto, initialState]

theorem readTrace (tag : Fin 6) (pass : Fin 2) (base : Tape → List Bool)
    (value : Nat) (suffix : List Bool)
    (hinput : base (readSource tag) = encodeWord value ++ suffix) :
    advance^[value + 2] (some ⟨some (.readStart tag pass), initialState, base⟩) =
      some ⟨some (readNext tag pass), initialState,
        SourceMachine.fieldTapes (readSource tag) (readDestination tag pass) base suffix
          (encodeWord value ++ base (readDestination tag pass))⟩ := by
  have h := (SourceMachine.fieldInTime (K := Tape) (Λ := Label) (σ := Unit)
    (readSource tag) (readDestination tag pass)
    (readSource_ne_destination tag pass) (.readStart tag pass) (.readLoop tag pass)
    (some (readNext tag pass)) program rfl rfl base value suffix hinput () none).evals_in_steps
  change advance^[value + 2]
    (some ⟨some (.readStart tag pass), initialState, base⟩) =
    some ⟨some (readNext tag pass), initialState,
      SourceMachine.fieldTapes (readSource tag) (readDestination tag pass) base suffix
        (encodeWord value ++ base (readDestination tag pass))⟩ at h
  exact h

theorem emitTagTrace (tag : Fin 6) (base : Tape → List Bool) :
    advance^[1] (some ⟨some (.emitTag tag), initialState, base⟩) =
      some ⟨some (.field tag 0), initialState,
        outputTapes base (encodeWord (gateTag tag)).reverse⟩ :=
  MachineInitialHeaders.literalTrace .reversed (encodeWord (gateTag tag))
    (.emitTag tag) (some (.field tag 0)) program rfl base () none

def FieldReady (tag : Fin 6) (slot : Fin 3) (base : Tape → List Bool) (value : Nat) : Prop :=
  (fieldUnused tag slot = true → value = 0) ∧
    (fieldUnused tag slot = false → base (fieldSource tag slot) = encodeWord value)

theorem FieldReady.output (tag : Fin 6) (slot : Fin 3) (base : Tape → List Bool)
    (value : Nat) (h : FieldReady tag slot base value) (bits : List Bool) :
    FieldReady tag slot (outputTapes base bits) value := by
  refine ⟨h.1, ?_⟩
  intro used
  rw [outputTapes_other base bits _ (fieldSource_ne_reversed tag slot)]
  exact h.2 used

def fieldSteps (tag : Fin 6) (slot : Fin 3) (value : Nat) : Nat :=
  if fieldUnused tag slot then 1 else 2 * value + 3

theorem fieldTrace (tag : Fin 6) (slot : Fin 3) (base : Tape → List Bool)
    (value : Nat) (ready : FieldReady tag slot base value) (hscratch : base .scratch = []) :
    advance^[fieldSteps tag slot value]
      (some ⟨some (.field tag slot), initialState, base⟩) =
      some ⟨some (fieldNext tag slot), initialState,
        outputTapes base (encodeWord value).reverse⟩ := by
  cases hu : fieldUnused tag slot with
  | true =>
      have hz := ready.1 hu
      subst value
      simp only [fieldSteps, hu, ↓reduceIte]
      change some (TM2.stepAux (program (.field tag slot)) initialState base) = _
      simp only [program, hu, ↓reduceIte, TM2.stepAux, encodeWord, List.replicate_zero,
        List.nil_append, List.reverse_singleton, outputTapes, List.singleton_append]
  | false =>
      have hcopy := (MachineInitialHeaders.prefixInTime (fieldSource tag slot) .scratch .reversed
        (fieldSource_ne_scratch tag slot) (fieldSource_ne_reversed tag slot) (by decide)
        1 (.field tag slot) (.restore tag slot) (some (.closeField tag slot)) program
        (by simp only [program, hu, Bool.false_eq_true, ↓reduceIte]) rfl base value []
        (by simpa using ready.2 hu) hscratch () none).evals_in_steps
      let copied := outputTapes base (List.replicate value true)
      change advance^[2 * value + 2]
        (some ⟨some (.field tag slot), initialState, base⟩) =
        some ⟨some (.closeField tag slot), initialState,
          outputTapes base (List.replicate (1 * value) true)⟩ at hcopy
      simp only [Nat.one_mul] at hcopy
      have hclose : advance^[1]
          (some ⟨some (.closeField tag slot), initialState, copied⟩) =
          some ⟨some (fieldNext tag slot), initialState, outputTapes copied [false]⟩ := by
        change some (TM2.stepAux (program (.closeField tag slot)) initialState copied) = _
        rfl
      have total := trace_trans _ hcopy hclose
      simpa only [fieldSteps, hu, Bool.false_eq_true, ↓reduceIte, copied, outputTapes_twice,
        encodeWord, List.reverse_append, List.reverse_singleton, List.reverse_replicate,
        show 2 * value + 2 + 1 = 2 * value + 3 by omega] using total

theorem rootPushTrace (base : Tape → List Bool) (current : Nat)
    (hcurrent : base .current = encodeWord current) (hscratch : base .scratch = []) :
    advance^[2 * current + 4]
      (some ⟨some .rootDrain, initialState, base⟩) =
      some ⟨some .increment, initialState,
        Function.update base .roots (encodeWord current ++ base .roots)⟩ := by
  have h := MachineCopy.copyTrace Tape.current Tape.roots Tape.scratch
    (by decide) (by decide) (by decide) false .rootDrain .rootFork (some .increment)
    program rfl rfl base hscratch () none
  simpa only [hcurrent, encodeWord_length, advance, initialState,
    show 2 * (current + 1 + 1) = 2 * current + 4 by omega] using h

theorem incrementTrace (base : Tape → List Bool) (current : Nat)
    (hcurrent : base .current = encodeWord current) :
    advance^[1] (some ⟨some .increment, initialState, base⟩) =
      some ⟨some .clearLeft, initialState,
        Function.update base .current (encodeWord (current + 1))⟩ := by
  change some (TM2.stepAux (program .increment) initialState base) = _
  simp only [program, TM2.stepAux, hcurrent, encodeWord, List.replicate_succ,
    List.cons_append]

def recordSteps (tag : Fin 6) (values : Fin 3 → Nat) : Nat :=
  1 + fieldSteps tag 0 (values 0) + fieldSteps tag 1 (values 1) + fieldSteps tag 2 (values 2)

theorem recordTrace (tag : Fin 6) (base : Tape → List Bool) (values : Fin 3 → Nat)
    (ready : ∀ slot, FieldReady tag slot base (values slot)) (hscratch : base .scratch = []) :
    advance^[recordSteps tag values]
      (some ⟨some (.emitTag tag), initialState, base⟩) =
      some ⟨some .rootDrain, initialState,
        outputTapes base (encodeWords [gateTag tag, values 0, values 1, values 2]).reverse⟩ := by
  let first := outputTapes base (encodeWord (gateTag tag)).reverse
  let second := outputTapes first (encodeWord (values 0)).reverse
  let third := outputTapes second (encodeWord (values 1)).reverse
  have readyFirst : ∀ slot, FieldReady tag slot first (values slot) :=
    fun slot => FieldReady.output tag slot base (values slot) (ready slot)
      (encodeWord (gateTag tag)).reverse
  have readySecond : ∀ slot, FieldReady tag slot second (values slot) :=
    fun slot => FieldReady.output tag slot first (values slot) (readyFirst slot)
      (encodeWord (values 0)).reverse
  have readyThird : ∀ slot, FieldReady tag slot third (values slot) :=
    fun slot => FieldReady.output tag slot second (values slot) (readySecond slot)
      (encodeWord (values 1)).reverse
  have ht := emitTagTrace tag base
  have h0 := fieldTrace tag 0 first (values 0) (readyFirst 0)
    (by simpa [first, outputTapes] using hscratch)
  have h1 := fieldTrace tag 1 second (values 1) (readySecond 1)
    (by simpa [second, first, outputTapes] using hscratch)
  have h2 := fieldTrace tag 2 third (values 2) (readyThird 2)
    (by simpa [third, second, first, outputTapes] using hscratch)
  change advance^[fieldSteps tag 0 (values 0)]
    (some ⟨some (.field tag 0), initialState, first⟩) =
    some ⟨some (.field tag 1), initialState, second⟩ at h0
  change advance^[fieldSteps tag 1 (values 1)]
    (some ⟨some (.field tag 1), initialState, second⟩) =
    some ⟨some (.field tag 2), initialState, third⟩ at h1
  change advance^[fieldSteps tag 2 (values 2)]
    (some ⟨some (.field tag 2), initialState, third⟩) =
    some ⟨some .rootDrain, initialState,
      outputTapes third (encodeWord (values 2)).reverse⟩ at h2
  have total := trace_trans _ (trace_trans _ (trace_trans _ ht h0) h1) h2
  simpa only [recordSteps, third, second, first, outputTapes_twice, encodeWords,
    List.append_nil, List.reverse_append, List.append_assoc] using total

def clearTapes (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update base .left []) .right []

theorem clearTrace (base : Tape → List Bool) :
    advance^[(base .left).length + (base .right).length + 2]
      (some ⟨some .clearLeft, initialState, base⟩) =
      some ⟨some .guard, initialState, clearTapes base⟩ := by
  let first := Function.update base .left []
  have h1 := (MachineDrain.drainInTime Tape.left .clearLeft (some .clearRight)
    program rfl base () none).evals_in_steps
  have h2 := (MachineDrain.drainInTime Tape.right .clearRight (some .guard)
    program rfl first () none).evals_in_steps
  change advance^[(base .left).length + 1]
    (some ⟨some .clearLeft, initialState, base⟩) =
    some ⟨some .clearRight, initialState, first⟩ at h1
  change advance^[(first .right).length + 1]
    (some ⟨some .clearRight, initialState, first⟩) =
    some ⟨some .guard, initialState, clearTapes base⟩ at h2
  have total := trace_trans _ h1 h2
  simpa only [first, Function.update_of_ne (by decide : Tape.right ≠ .left),
    show (base .left).length + 1 + ((base .right).length + 1) =
      (base .left).length + (base .right).length + 2 by omega] using total

def finishTapes (base : Tape → List Bool) (current : Nat) : Tape → List Bool :=
  clearTapes (Function.update
    (Function.update base .roots (encodeWord current ++ base .roots))
    .current (encodeWord (current + 1)))

theorem finishNodeTrace (base : Tape → List Bool) (current : Nat)
    (hcurrent : base .current = encodeWord current) (hscratch : base .scratch = []) :
    advance^[2 * current + (base .left).length + (base .right).length + 7]
      (some ⟨some .rootDrain, initialState, base⟩) =
      some ⟨some .guard, initialState, finishTapes base current⟩ := by
  let pushed := Function.update base .roots (encodeWord current ++ base .roots)
  let incremented := Function.update pushed .current (encodeWord (current + 1))
  have h1 := rootPushTrace base current hcurrent hscratch
  have h2 := incrementTrace pushed current (by simpa [pushed] using hcurrent)
  have h3 := clearTrace incremented
  have total := trace_trans _ (trace_trans _ h1 h2) h3
  simpa only [finishTapes, incremented, pushed,
    Function.update_of_ne (by decide : Tape.left ≠ .current),
    Function.update_of_ne (by decide : Tape.right ≠ .current),
    Function.update_of_ne (by decide : Tape.left ≠ .roots),
    Function.update_of_ne (by decide : Tape.right ≠ .roots),
    show (2 * current + 4) + 1 + ((base .left).length + (base .right).length + 2) =
      2 * current + (base .left).length + (base .right).length + 7 by omega] using total

theorem emitPreparedTrace (tag : Fin 6) (base : Tape → List Bool)
    (current : Nat) (gate : Gate)
    (htag : gateTag tag = (gateRecord current gate).tag.val)
    (ready : ∀ slot, FieldReady tag slot base ((gateRecord current gate).slot slot))
    (hcurrent : base .current = encodeWord current) (hscratch : base .scratch = []) :
    advance^[recordSteps tag (gateRecord current gate).slot +
      (2 * current + (base .left).length + (base .right).length + 7)]
      (some ⟨some (.emitTag tag), initialState, base⟩) =
      some ⟨some .guard, initialState,
        finishTapes (outputTapes base (gateRecord current gate).bits.reverse) current⟩ := by
  have hrecord := recordTrace tag base (gateRecord current gate).slot ready hscratch
  have hwords : [gateTag tag, (gateRecord current gate).slot 0,
      (gateRecord current gate).slot 1, (gateRecord current gate).slot 2] =
      (gateRecord current gate).words := by
    rw [htag]
    rfl
  rw [hwords] at hrecord
  let emitted := outputTapes base (gateRecord current gate).bits.reverse
  have hfinish := finishNodeTrace emitted current
    (by simpa [emitted, outputTapes] using hcurrent)
    (by simpa [emitted, outputTapes] using hscratch)
  have total := trace_trans _ hrecord hfinish
  simpa only [emitted, outputTapes_other base _ .left (by decide),
    outputTapes_other base _ .right (by decide)] using total

def boundaryTapes (base : Tape → List Bool) (current : Nat)
    (roots : List Nat) (input : List Bool) : Tape → List Bool
  | .input => input
  | .current => encodeWord current
  | .roots => encodeWords roots
  | .left | .right | .scratch => []
  | tape => base tape

def preparedTapes (base : Tape → List Bool) (current : Nat)
    (roots : List Nat) (input left right : List Bool) : Tape → List Bool
  | .input => input
  | .current => encodeWord current
  | .roots => encodeWords roots
  | .left => left
  | .right => right
  | .scratch => []
  | tape => base tape

def operandFields : Token → Gate → List Bool × List Bool
  | .const _, _ => ([], [])
  | .input wire, _ => (encodeWord wire, [])
  | .not, .not arg => (encodeWord arg, [])
  | .and, .and left right | .or, .or left right => (encodeWord left, encodeWord right)
  | _, _ => ([], [])

def operandSteps : Token → Gate → Nat
  | .const _, _ => 0
  | .input wire, _ => wire + 2
  | .not, .not arg => arg + 2
  | .and, .and left right | .or, .or left right => left + right + 4
  | _, _ => 0

def tokenSteps (current : Nat) (token : Token) (gate : Gate) : Nat :=
  1 + operandSteps token gate + recordSteps token.tag (gateRecord current gate).slot +
    (2 * current + (operandFields token gate).1.length +
      (operandFields token gate).2.length + 7)

def tokensSteps (current : Nat) (roots : List Nat) : List Token → Nat
  | [] => 0
  | token :: tokens => match token.takeGate roots with
      | none => 0
      | some (gate, rest) =>
          1 + tokenSteps current token gate + tokensSteps (current + 1) (current :: rest) tokens

def argumentBits : Token → List Bool
  | .input wire => encodeWord wire
  | _ => []

theorem token_bits (token : Token) : token.bits = encodeWord token.tag.val ++ argumentBits token := by
  cases token with
  | const value => cases value <;> simp [Token.bits, Token.words, Token.tag, argumentBits, encodeWords]
  | not | and | or | input _ => simp [Token.bits, Token.words, Token.tag, argumentBits, encodeWords]

theorem prepareInputTrace (base : Tape → List Bool) (current wire : Nat)
    (roots : List Nat) (suffix : List Bool) :
    advance^[wire + 2]
      (some ⟨some (.readStart 5 0), initialState,
        boundaryTapes base current roots (encodeWord wire ++ suffix)⟩) =
      some ⟨some (.emitTag 5), initialState,
        preparedTapes base current roots suffix (encodeWord wire) []⟩ := by
  let first := boundaryTapes base current roots (encodeWord wire ++ suffix)
  have h := readTrace 5 0 first wire suffix rfl
  have hout : SourceMachine.fieldTapes (readSource 5) (readDestination 5 0) first suffix
      (encodeWord wire ++ first (readDestination 5 0)) =
      preparedTapes base current roots suffix (encodeWord wire) [] := by
    funext tape
    cases tape <;> simp [SourceMachine.fieldTapes, first, boundaryTapes, preparedTapes,
      readSource, readDestination, binary]
  rw [hout] at h
  exact h

theorem prepareUnaryTrace (base : Tape → List Bool) (current arg : Nat)
    (roots : List Nat) (suffix : List Bool) :
    advance^[arg + 2]
      (some ⟨some (.readStart 2 0), initialState,
        boundaryTapes base current (arg :: roots) suffix⟩) =
      some ⟨some (.emitTag 2), initialState,
        preparedTapes base current roots suffix (encodeWord arg) []⟩ := by
  let first := boundaryTapes base current (arg :: roots) suffix
  have h := readTrace 2 0 first arg (encodeWords roots) rfl
  have hout : SourceMachine.fieldTapes (readSource 2) (readDestination 2 0) first
      (encodeWords roots) (encodeWord arg ++ first (readDestination 2 0)) =
      preparedTapes base current roots suffix (encodeWord arg) [] := by
    funext tape
    cases tape <;> simp [SourceMachine.fieldTapes, first, boundaryTapes, preparedTapes,
      readSource, readDestination, binary]
  rw [hout] at h
  exact h

theorem prepareBinaryTrace (tag : Fin 6) (hb : binary tag = true) (hinput : tag.val ≠ 5)
    (base : Tape → List Bool) (current left right : Nat) (roots : List Nat) (suffix : List Bool) :
    advance^[left + right + 4]
      (some ⟨some (.readStart tag 0), initialState,
        boundaryTapes base current (right :: left :: roots) suffix⟩) =
      some ⟨some (.emitTag tag), initialState,
        preparedTapes base current roots suffix (encodeWord left) (encodeWord right)⟩ := by
  let first := boundaryTapes base current (right :: left :: roots) suffix
  let second := preparedTapes base current (left :: roots) suffix [] (encodeWord right)
  have h1 := readTrace tag 0 first right (encodeWords (left :: roots))
    (by simp [first, readSource, hinput, boundaryTapes, encodeWords])
  have frame1 : SourceMachine.fieldTapes (readSource tag) (readDestination tag 0) first
      (encodeWords (left :: roots)) (encodeWord right ++ first (readDestination tag 0)) = second := by
    funext tape
    cases tape <;> simp [SourceMachine.fieldTapes, first, second, boundaryTapes, preparedTapes,
      readSource, readDestination, hb, hinput]
  rw [frame1] at h1
  have h2 := readTrace tag 1 second left (encodeWords roots)
    (by simp [second, readSource, hinput, preparedTapes, encodeWords])
  have frame2 : SourceMachine.fieldTapes (readSource tag) (readDestination tag 1) second
      (encodeWords roots) (encodeWord left ++ second (readDestination tag 1)) =
      preparedTapes base current roots suffix (encodeWord left) (encodeWord right) := by
    funext tape
    cases tape <;> simp [SourceMachine.fieldTapes, second, preparedTapes,
      readSource, readDestination, hb, hinput]
  rw [frame2] at h2
  simp only [readNext, hb, Fin.val_zero, Fin.val_one, decide_true, Bool.and_true,
    Nat.one_ne_zero, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at h1 h2
  have total := trace_trans _ h1 h2
  simpa only [show (right + 2) + (left + 2) = left + right + 4 by omega] using total

theorem prepareTrace (base : Tape → List Bool) (current : Nat) (token : Token)
    (roots rest : List Nat) (gate : Gate) (suffix : List Bool)
    (htake : token.takeGate roots = some (gate, rest)) :
    advance^[operandSteps token gate]
      (some ⟨some (prepare token.tag), initialState,
        boundaryTapes base current roots (argumentBits token ++ suffix)⟩) =
      some ⟨some (.emitTag token.tag), initialState,
        preparedTapes base current rest suffix
          (operandFields token gate).1 (operandFields token gate).2⟩ := by
  cases token with
  | const value =>
      simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
      rcases htake with ⟨rfl, rfl⟩
      cases value <;>
        simp [Token.tag, operandSteps, operandFields, argumentBits, prepare] <;>
        funext tape <;> cases tape <;> rfl
  | input wire =>
      simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
      rcases htake with ⟨rfl, rfl⟩
      simpa [Token.tag, operandSteps, operandFields, argumentBits, prepare] using
        prepareInputTrace base current wire roots suffix
  | not =>
      cases roots with
      | nil => simp [Token.takeGate] at htake
      | cons arg roots =>
          simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
          rcases htake with ⟨rfl, rfl⟩
          simpa [Token.tag, operandSteps, operandFields, argumentBits, prepare] using
            prepareUnaryTrace base current arg roots suffix
  | and =>
      cases roots with
      | nil => simp [Token.takeGate] at htake
      | cons right roots =>
          cases roots with
          | nil => simp [Token.takeGate] at htake
          | cons left roots =>
              simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
              rcases htake with ⟨rfl, rfl⟩
              simpa [Token.tag, operandSteps, operandFields, argumentBits, prepare] using
                prepareBinaryTrace 3 (by decide) (by decide) base current left right roots suffix
  | or =>
      cases roots with
      | nil => simp [Token.takeGate] at htake
      | cons right roots =>
          cases roots with
          | nil => simp [Token.takeGate] at htake
          | cons left roots =>
              simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
              rcases htake with ⟨rfl, rfl⟩
              simpa [Token.tag, operandSteps, operandFields, argumentBits, prepare] using
                prepareBinaryTrace 4 (by decide) (by decide) base current left right roots suffix

theorem preparedReady (base : Tape → List Bool) (current : Nat) (token : Token)
    (roots rest : List Nat) (gate : Gate) (suffix : List Bool)
    (htake : token.takeGate roots = some (gate, rest)) :
    gateTag token.tag = (gateRecord current gate).tag.val ∧
      ∀ slot, FieldReady token.tag slot
        (preparedTapes base current rest suffix
          (operandFields token gate).1 (operandFields token gate).2)
        ((gateRecord current gate).slot slot) := by
  cases token with
  | const value =>
      simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
      rcases htake with ⟨rfl, rfl⟩
      cases value <;> refine ⟨rfl, ?_⟩ <;> intro slot <;> fin_cases slot <;>
        simp [FieldReady, Token.tag, fieldUnused, fieldSource, preparedTapes, operandFields,
          gateRecord, CircuitProducerModel.Record.slot]
  | input wire =>
      simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
      rcases htake with ⟨rfl, rfl⟩
      refine ⟨rfl, ?_⟩
      intro slot
      fin_cases slot <;> simp [FieldReady, Token.tag, fieldUnused, fieldSource, preparedTapes,
        operandFields, gateRecord, CircuitProducerModel.Record.slot]
  | not =>
      cases roots with
      | nil => simp [Token.takeGate] at htake
      | cons arg roots =>
          simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
          rcases htake with ⟨rfl, rfl⟩
          refine ⟨rfl, ?_⟩
          intro slot
          fin_cases slot <;> simp [FieldReady, Token.tag, fieldUnused, fieldSource, preparedTapes,
            operandFields, gateRecord, CircuitProducerModel.Record.slot]
  | and =>
      cases roots with
      | nil => simp [Token.takeGate] at htake
      | cons right roots =>
          cases roots with
          | nil => simp [Token.takeGate] at htake
          | cons left roots =>
              simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
              rcases htake with ⟨rfl, rfl⟩
              refine ⟨rfl, ?_⟩
              intro slot
              fin_cases slot <;> simp [FieldReady, Token.tag, fieldUnused, fieldSource, preparedTapes,
                operandFields, gateRecord, CircuitProducerModel.Record.slot]
  | or =>
      cases roots with
      | nil => simp [Token.takeGate] at htake
      | cons right roots =>
          cases roots with
          | nil => simp [Token.takeGate] at htake
          | cons left roots =>
              simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
              rcases htake with ⟨rfl, rfl⟩
              refine ⟨rfl, ?_⟩
              intro slot
              fin_cases slot <;> simp [FieldReady, Token.tag, fieldUnused, fieldSource, preparedTapes,
                operandFields, gateRecord, CircuitProducerModel.Record.slot]

theorem tokenTrace (base : Tape → List Bool) (current : Nat) (token : Token)
    (roots rest : List Nat) (gate : Gate) (suffix : List Bool)
    (htake : token.takeGate roots = some (gate, rest)) :
    advance^[tokenSteps current token gate]
      (some ⟨some .decode, initialState,
        boundaryTapes base current roots (token.bits ++ suffix)⟩) =
      some ⟨some .guard, initialState,
        boundaryTapes (outputTapes base (gateRecord current gate).bits.reverse)
          (current + 1) (current :: rest) suffix⟩ := by
  let first := boundaryTapes base current roots (token.bits ++ suffix)
  let decoded := boundaryTapes base current roots (argumentBits token ++ suffix)
  let prepared := preparedTapes base current rest suffix
    (operandFields token gate).1 (operandFields token gate).2
  have hd := decodeTrace token.tag first (argumentBits token ++ suffix)
    (by simp only [first, boundaryTapes, token_bits, List.append_assoc])
  have decodedFrame : Function.update first .input (argumentBits token ++ suffix) = decoded := by
    funext tape
    cases tape <;> simp [first, decoded, boundaryTapes]
  rw [decodedFrame] at hd
  have hp := prepareTrace base current token roots rest gate suffix htake
  have ready := preparedReady base current token roots rest gate suffix htake
  have he := emitPreparedTrace token.tag prepared current gate ready.1 ready.2 rfl rfl
  have total := trace_trans _ (trace_trans _ hd hp) he
  have finishedFrame : finishTapes (outputTapes prepared (gateRecord current gate).bits.reverse)
      current = boundaryTapes (outputTapes base (gateRecord current gate).bits.reverse)
        (current + 1) (current :: rest) suffix := by
    funext tape
    cases tape <;> simp [finishTapes, clearTapes, prepared, preparedTapes, boundaryTapes,
      outputTapes, encodeWords]
  rw [finishedFrame] at total
  simpa only [tokenSteps, first, prepared, preparedTapes, Nat.add_assoc] using total

theorem tokenBits_cons (token : Token) (tokens : List Token) :
    tokenBits (token :: tokens) = token.bits ++ tokenBits tokens := by
  simp [tokenBits, tokenWords, Token.bits]

theorem boundary_remaining (base : Tape → List Bool) (current : Nat)
    (roots : List Nat) (input : List Bool) (count : Nat) :
    Function.update (boundaryTapes base current roots input) .remaining (encodeWord count) =
      boundaryTapes (Function.update base .remaining (encodeWord count)) current roots input := by
  funext tape
  cases tape <;> simp [boundaryTapes]

theorem guardPositiveTrace (base : Tape → List Bool) (count : Nat)
    (hcount : base .remaining = encodeWord (count + 1)) :
    advance^[1] (some ⟨some .guard, initialState, base⟩) =
      some ⟨some .decode, initialState, Function.update base .remaining (encodeWord count)⟩ := by
  change some (TM2.stepAux (program .guard) initialState base) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux, hcount, encodeWord,
    List.replicate_succ, initialState]

theorem tokensTrace (tokens : List Token) (base : Tape → List Bool) (current : Nat)
    (roots : List Nat) (next : Nat) (finalRoots : List Nat) (gates : List Gate)
    (suffix : List Bool)
    (hcompile : compileTokens current roots tokens = some (next, finalRoots, gates))
    (hcount : base .remaining = encodeWord tokens.length) :
    advance^[tokensSteps current roots tokens]
      (some ⟨some .guard, initialState,
        boundaryTapes base current roots (tokenBits tokens ++ suffix)⟩) =
      some ⟨some .guard, initialState,
        boundaryTapes
          (outputTapes (Function.update base .remaining (encodeWord 0))
            (recordsBits (gateRecords current gates)).reverse)
          next finalRoots suffix⟩ := by
  induction tokens generalizing base current roots next finalRoots gates with
  | nil =>
      simp only [compileTokens, Option.some.injEq, Prod.mk.injEq] at hcompile
      rcases hcompile with ⟨rfl, rfl, rfl⟩
      have hsame : Function.update base .remaining (encodeWord 0) = base := by
        change base .remaining = encodeWord 0 at hcount
        rw [← hcount]
        exact Function.update_eq_self _ _
      simp [tokensSteps, tokenBits, tokenWords, gateRecords, recordsBits, recordsWords,
        encodeWords, hsame, outputTapes]
  | cons token tokens ih =>
      cases htake : token.takeGate roots with
      | none => simp [compileTokens, htake] at hcompile
      | some result =>
          rcases result with ⟨gate, rest⟩
          cases htail : compileTokens (current + 1) (current :: rest) tokens with
          | none => simp [compileTokens, htake, htail] at hcompile
          | some result =>
              rcases result with ⟨next', finalRoots', gates'⟩
              simp [compileTokens, htake, htail] at hcompile
              obtain ⟨hnext, hroots, hgates⟩ := hcompile
              subst next
              subst finalRoots
              subst gates
              let decremented := Function.update base .remaining (encodeWord tokens.length)
              let following := outputTapes decremented (gateRecord current gate).bits.reverse
              have hg := guardPositiveTrace
                (boundaryTapes base current roots (tokenBits (token :: tokens) ++ suffix))
                tokens.length (by simpa [boundaryTapes] using hcount)
              rw [boundary_remaining] at hg
              have ht := tokenTrace decremented current token roots rest gate
                (tokenBits tokens ++ suffix) htake
              have hi := ih following (current + 1) (current :: rest)
                next' finalRoots' gates' htail
                (by simp [following, decremented, outputTapes])
              have hg' : advance^[1]
                  (some ⟨some .guard, initialState,
                    boundaryTapes base current roots (tokenBits (token :: tokens) ++ suffix)⟩) =
                  some ⟨some .decode, initialState,
                    boundaryTapes decremented current roots (token.bits ++ (tokenBits tokens ++ suffix))⟩ := by
                simpa only [tokenBits_cons, List.append_assoc] using hg
              have total := trace_trans _ (trace_trans _ hg' ht) hi
              have frame :
                  outputTapes (Function.update following .remaining (encodeWord 0))
                    (recordsBits (gateRecords (current + 1) gates')).reverse =
                  outputTapes (Function.update base .remaining (encodeWord 0))
                    (recordsBits (gateRecords current (gate :: gates'))).reverse := by
                funext tape
                cases tape <;>
                  simp [following, decremented, outputTapes, gateRecords, recordsBits_cons,
                    List.reverse_append, List.append_assoc]
              rw [frame] at total
              simpa only [tokensSteps, htake] using total

def initialTapes (base : Tape → List Bool) (roots : List Nat)
    (input : List Bool) : Tape → List Bool
  | .input => input
  | .roots => encodeWords roots
  | .current | .remaining | .left | .right | .scratch => []
  | tape => base tape

theorem headersTrace (base : Tape → List Bool) (roots : List Nat)
    (start count : Nat) (suffix : List Bool) :
    advance^[start + count + 4]
      (some ⟨some (.headerStart 0), initialState,
        initialTapes base roots (encodeWords [start, count] ++ suffix)⟩) =
      some ⟨some .guard, initialState,
        boundaryTapes (Function.update base .remaining (encodeWord count)) start roots suffix⟩ := by
  let first := initialTapes base roots (encodeWords [start, count] ++ suffix)
  let second := Function.update
    (Function.update first .input (encodeWord count ++ suffix)) .current (encodeWord start)
  have h1 := (SourceMachine.fieldInTime Tape.input Tape.current (by decide)
    (.headerStart 0) (.headerLoop 0) (some (.headerStart 1)) program rfl rfl
    first start (encodeWord count ++ suffix)
    (by simp [first, initialTapes, encodeWords, List.append_assoc]) () none).evals_in_steps
  have frame1 : SourceMachine.fieldTapes Tape.input Tape.current first
      (encodeWord count ++ suffix) (encodeWord start ++ first .current) = second := by
    simp [SourceMachine.fieldTapes, first, initialTapes, second]
  change advance^[start + 2]
    (some ⟨some (.headerStart 0), initialState, first⟩) =
    some ⟨some (.headerStart 1), initialState,
      SourceMachine.fieldTapes Tape.input Tape.current first
        (encodeWord count ++ suffix) (encodeWord start ++ first .current)⟩ at h1
  rw [frame1] at h1
  have h2 := (SourceMachine.fieldInTime Tape.input Tape.remaining (by decide)
    (.headerStart 1) (.headerLoop 1) (some .guard) program rfl rfl
    second count suffix (by simp [second]) () none).evals_in_steps
  have frame2 : SourceMachine.fieldTapes Tape.input Tape.remaining second suffix
      (encodeWord count ++ second .remaining) =
      boundaryTapes (Function.update base .remaining (encodeWord count)) start roots suffix := by
    funext tape
    cases tape <;> simp [SourceMachine.fieldTapes, second, first, initialTapes, boundaryTapes]
  change advance^[count + 2]
    (some ⟨some (.headerStart 1), initialState, second⟩) =
    some ⟨some .guard, initialState,
      SourceMachine.fieldTapes Tape.input Tape.remaining second suffix
        (encodeWord count ++ second .remaining)⟩ at h2
  rw [frame2] at h2
  have total := trace_trans _ h1 h2
  simpa only [show (start + 2) + (count + 2) = start + count + 4 by omega] using total

def reversedTapes (base : Tape → List Bool) (bits : List Bool) : Tape → List Bool :=
  Function.update (Function.update (Function.update base .remaining []) .reversed [])
    .output (bits ++ base .output)

theorem reverseTrace (base : Tape → List Bool) (bits : List Bool)
    (hzero : base .remaining = encodeWord 0) (hbits : base .reversed = bits.reverse) :
    advance^[bits.length + 3] (some ⟨some .guard, initialState, base⟩) =
      some ⟨none, initialState, reversedTapes base bits⟩ := by
  have hguard : advance^[1] (some ⟨some .guard, initialState, base⟩) =
      some ⟨some .finish, initialState, base⟩ := by
    change some (TM2.stepAux (program .guard) initialState base) = _
    simp [program, MachineUnaryCounter.guard, TM2.stepAux, hzero, encodeWord, initialState]
  let cleared := Function.update base .remaining []
  have hclear : advance^[1] (some ⟨some .finish, initialState, base⟩) =
      some ⟨some .finalReverse, initialState, cleared⟩ := by
    change some (TM2.stepAux (program .finish) initialState base) = _
    simp [program, TM2.stepAux, hzero, encodeWord, cleared, initialState]
  have htransfer := (Reduction.MachineTransfer.transferAtInTime
    Tape.reversed Tape.output (by decide) id false .finalReverse none program rfl
    cleared () none).evals_in_steps
  change advance^[(cleared .reversed).length + 1]
    (some ⟨some .finalReverse, initialState, cleared⟩) =
    some ⟨none, initialState,
      Reduction.MachineTransfer.tapesAt .reversed .output cleared []
        ((cleared .reversed).reverse.map id ++ cleared .output)⟩ at htransfer
  have hlength : (cleared .reversed).length = bits.length := by
    simp [cleared, hbits]
  have frame : Reduction.MachineTransfer.tapesAt Tape.reversed Tape.output cleared []
      ((cleared .reversed).reverse.map id ++ cleared .output) = reversedTapes base bits := by
    simp [Reduction.MachineTransfer.tapesAt, cleared, reversedTapes, hbits]
  rw [hlength, frame] at htransfer
  have total := trace_trans _ (trace_trans _ hguard hclear) htransfer
  simpa only [show 1 + 1 + (bits.length + 1) = bits.length + 3 by omega] using total

def finalTapes (base : Tape → List Bool) (next : Nat) (roots : List Nat)
    (suffix output : List Bool) : Tape → List Bool
  | .input => suffix
  | .current => encodeWord next
  | .roots => encodeWords roots
  | .output => output ++ base .output
  | _ => []

theorem compileTrace (tokens : List Token) (base : Tape → List Bool) (start : Nat)
    (roots : List Nat) (next : Nat) (finalRoots : List Nat) (gates : List Gate)
    (suffix : List Bool)
    (hcompile : compileTokens start roots tokens = some (next, finalRoots, gates)) :
    advance^[start + tokens.length + 4 + tokensSteps start roots tokens +
      (base .reversed).length + (recordsBits (gateRecords start gates)).length + 3]
      (some ⟨some (.headerStart 0), initialState,
        initialTapes base roots (inputBits start tokens ++ suffix)⟩) =
      some ⟨none, initialState, finalTapes base next finalRoots suffix
        ((base .reversed).reverse ++ recordsBits (gateRecords start gates))⟩ := by
  let headerBase := Function.update base .remaining (encodeWord tokens.length)
  let finished := boundaryTapes
    (outputTapes (Function.update headerBase .remaining (encodeWord 0))
      (recordsBits (gateRecords start gates)).reverse) next finalRoots suffix
  let emitted := (base .reversed).reverse ++ recordsBits (gateRecords start gates)
  have hh := headersTrace base roots start tokens.length (tokenBits tokens ++ suffix)
  have ht := tokensTrace tokens headerBase start roots next finalRoots gates suffix hcompile
    (by simp [headerBase])
  have hr := reverseTrace finished emitted
    (by simp [finished, boundaryTapes, outputTapes])
    (by simp [finished, emitted, boundaryTapes, outputTapes, headerBase, List.reverse_append])
  have total := trace_trans _ (trace_trans _ hh ht) hr
  have frame : reversedTapes finished emitted = finalTapes base next finalRoots suffix emitted := by
    funext tape
    cases tape <;> simp [reversedTapes, finished, finalTapes, boundaryTapes, outputTapes, headerBase]
  rw [frame] at total
  simpa only [inputBits, List.append_assoc, emitted, List.length_append, List.length_reverse,
    Nat.add_assoc] using total

def compileInTime (tokens : List Token) (base : Tape → List Bool) (start : Nat)
    (roots : List Nat) (next : Nat) (finalRoots : List Nat) (gates : List Gate)
    (suffix : List Bool)
    (hcompile : compileTokens start roots tokens = some (next, finalRoots, gates)) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.headerStart 0), initialState, initialTapes base roots (inputBits start tokens ++ suffix)⟩
      (some ⟨none, initialState, finalTapes base next finalRoots suffix
        ((base .reversed).reverse ++ recordsBits (gateRecords start gates))⟩)
      (start + tokens.length + 4 + tokensSteps start roots tokens +
        (base .reversed).length + (recordsBits (gateRecords start gates)).length + 3) where
  steps := start + tokens.length + 4 + tokensSteps start roots tokens +
    (base .reversed).length + (recordsBits (gateRecords start gates)).length + 3
  evals_in_steps := compileTrace tokens base start roots next finalRoots gates suffix hcompile
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.PostfixMachine

end OAI
