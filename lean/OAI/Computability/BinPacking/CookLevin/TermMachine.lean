import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import OAI.Computability.BinPacking.Computation.MachineExpanderRowDivision
import OAI.Computability.BinPacking.CookLevin.OutputOrder

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.TermMachine

open Turing MachineComposition TransitionTemplate PostfixModel

inductive Tape
  | cursor | capacity | roots | count | reversed
  | position | address | value | scratch | copy | saveLeft | saveRight
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.cursor, .capacity, .roots, .count, .reversed,
  .position, .address, .value, .scratch, .copy, .saveLeft, .saveRight]

protected theorem Tape.enumList_getElem?_ctorIdx_eq (x : Tape) :
    Tape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Tape) := Bool
abbrev State := (Unit × Bool) × Option Bool

def initialState : State := (((), false), none)

structure Input where
  cursor : Nat
  capacity : Nat
  roots : List Nat

def Input.size (input : Input) : Nat :=
  input.cursor + input.capacity + (encodeWords input.roots).length

def work : Tape → Bool
  | .cursor | .capacity | .roots | .count | .reversed => false
  | _ => true

structure Frame (input : Input) (base : Tape → List Bool) : Prop where
  cursorWord : base .cursor = encodeWord input.cursor
  capacityWord : base .capacity = encodeWord input.capacity
  rootsWord : base .roots = encodeWords input.roots
  clean : ∀ tape, work tape = true → base tape = []

def emitTapes (base : Tape → List Bool) (tokens : List Token) : Tape → List Bool :=
  Function.update
    (Function.update base .reversed ((tokenBits tokens).reverse ++ base .reversed))
    .count (List.replicate tokens.length true ++ base .count)

@[simp] theorem emitTapes_reversed (base : Tape → List Bool) (tokens : List Token) :
    emitTapes base tokens .reversed = (tokenBits tokens).reverse ++ base .reversed := by
  simp [emitTapes]

@[simp] theorem emitTapes_count (base : Tape → List Bool) (tokens : List Token) :
    emitTapes base tokens .count = List.replicate tokens.length true ++ base .count := by
  simp [emitTapes]

theorem emitTapes_other (base : Tape → List Bool) (tokens : List Token) (tape : Tape)
    (hc : tape ≠ .count) (ho : tape ≠ .reversed) :
    emitTapes base tokens tape = base tape := by
  simp [emitTapes, hc, ho]

theorem Frame.emit {input : Input} {base : Tape → List Bool}
    (frame : Frame input base) (tokens : List Token) : Frame input (emitTapes base tokens) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [emitTapes] using frame.cursorWord
  · simpa [emitTapes] using frame.capacityWord
  · simpa [emitTapes] using frame.rootsWord
  · intro tape ht
    have hc : tape ≠ .count := by intro h; subst tape; simp [work] at ht
    have ho : tape ≠ .reversed := by intro h; subst tape; simp [work] at ht
    rw [emitTapes_other base tokens tape hc ho]
    exact frame.clean tape ht

@[simp] theorem tokenBits_append (first second : List Token) :
    tokenBits (first ++ second) = tokenBits first ++ tokenBits second := by
  simp [tokenBits, tokenWords, List.flatMap_append, encodeWords_append]

theorem emitTapes_append (base : Tape → List Bool) (first second : List Token) :
    emitTapes (emitTapes base first) second = emitTapes base (first ++ second) := by
  funext tape
  by_cases hc : tape = .count
  · subst tape
    simp only [emitTapes_count, List.length_append]
    rw [← List.append_assoc, ← List.replicate_add, Nat.add_comm second.length first.length]
  · cases tape <;>
      simp [emitTapes, List.length_append, List.reverse_append, List.append_assoc] at *

theorem emitTapes_count_word (base : Tape → List Bool) (tokens : List Token)
    (count : Nat) (suffix : List Bool) (h : base .count = encodeWord count ++ suffix) :
    emitTapes base tokens .count = encodeWord (count + tokens.length) ++ suffix := by
  rw [emitTapes_count, h]
  simpa only [Nat.add_comm] using
    MachineUnaryAffineAt.prepend_replicate_word tokens.length count suffix

structure Emitter (valid : Input → Prop) (output : Input → List Token) where
  Label : Type
  finite : Fintype Label
  entry : Label
  program : Label → TM2.Stmt Alphabet Label State
  steps : Input → Nat
  constant : Nat
  trace : ∀ (input : Input), valid input → ∀ (base : Tape → List Bool), Frame input base →
    (advance (TM2.step program))^[steps input]
      (some ⟨some entry, initialState, base⟩) =
      some ⟨none, initialState, emitTapes base (output input)⟩
  bound : ∀ input, valid input → steps input ≤ constant * (input.size + 1)

attribute [instance] Emitter.finite

namespace Emitter

variable {valid : Input → Prop} {output first second : Input → List Token}

def machine (emitter : Emitter valid output) : FinTM2 where
  K := Tape
  k₀ := .cursor
  k₁ := .reversed
  Γ := Alphabet
  Λ := emitter.Label
  main := emitter.entry
  σ := State
  initialState := initialState
  m := emitter.program

def literalProgram (tokens : List Token) : Unit → TM2.Stmt Alphabet Unit State :=
  fun _ => Reduction.MachineSubstitution.pushWord .reversed (tokenBits tokens)
    (Reduction.MachineSubstitution.pushWord .count (List.replicate tokens.length true)
      (.load (fun _ => initialState) .halt))

theorem literalTrace (tokens : List Token) (base : Tape → List Bool) :
    (advance (TM2.step (literalProgram tokens)))^[1]
      (some ⟨some (), initialState, base⟩) =
      some ⟨none, initialState, emitTapes base tokens⟩ := by
  change some (TM2.stepAux (literalProgram tokens ()) initialState base) = _
  simp [literalProgram, Reduction.MachineSubstitution.stepAux_pushWord,
    TM2.stepAux, emitTapes]

def literal (valid : Input → Prop) (tokens : List Token) :
    Emitter valid (fun _ => tokens) where
  Label := Unit
  finite := inferInstance
  entry := ()
  program := literalProgram tokens
  steps := fun _ => 1
  constant := 1
  trace _ _ base _ := literalTrace tokens base
  bound input _ := by simp

def seqProgram (left : Emitter valid first) (right : Emitter valid second) :
    left.Label ⊕ right.Label → TM2.Stmt Alphabet (left.Label ⊕ right.Label) State
  | .inl l => MachineSubroutine.statement Sum.inl (some (.inr right.entry)) (left.program l)
  | .inr l => MachineSubroutine.statement Sum.inr none (right.program l)

def seq (left : Emitter valid first) (right : Emitter valid second) :
    Emitter valid (fun input => first input ++ second input) where
  Label := left.Label ⊕ right.Label
  finite := inferInstance
  entry := .inl left.entry
  program := seqProgram left right
  steps input := left.steps input + right.steps input
  constant := left.constant + right.constant
  trace input hv base frame := by
    have hl := MachineSubroutine.trace Sum.inl (some (.inr right.entry))
      left.program (seqProgram left right) (fun _ => rfl)
      (left.steps input) _ _ (left.trace input hv base frame)
    have hr := MachineSubroutine.trace Sum.inr none
      right.program (seqProgram left right) (fun _ => rfl)
      (right.steps input) _ _ (right.trace input hv (emitTapes base (first input))
        (frame.emit (first input)))
    simp only [MachineSubroutine.configuration, MachineSubroutine.label] at hl hr
    rw [Nat.add_comm (left.steps input), Function.iterate_add_apply, hl, hr,
      emitTapes_append]
  bound input hv := by
    have h := Nat.add_le_add (left.bound input hv) (right.bound input hv)
    simpa only [Nat.add_mul] using h

def congr (emitter : Emitter valid first) (equality : ∀ input, first input = second input) :
    Emitter valid second where
  Label := emitter.Label
  finite := emitter.finite
  entry := emitter.entry
  program := emitter.program
  steps := emitter.steps
  constant := emitter.constant
  trace input hv base frame := by
    simpa only [equality input] using emitter.trace input hv base frame
  bound := emitter.bound

theorem traceAt {Λ' : Type} (emitter : Emitter valid output)
    (labels : emitter.Label → Λ') (exit : Option Λ')
    (target : Λ' → TM2.Stmt Alphabet Λ' State)
    (code : ∀ label, target (labels label) =
      MachineSubroutine.statement labels exit (emitter.program label))
    (input : Input) (hv : valid input) (base : Tape → List Bool) (frame : Frame input base) :
    (advance (TM2.step target))^[emitter.steps input]
      (some ⟨some (labels emitter.entry), initialState, base⟩) =
      some ⟨exit, initialState, emitTapes base (output input)⟩ := by
  have h := MachineSubroutine.trace labels exit emitter.program target code
    (emitter.steps input) _ _ (emitter.trace input hv base frame)
  simpa only [MachineSubroutine.configuration, MachineSubroutine.label] using h

end Emitter

def lookupTapes : Fin 5 → Tape
  | 0 => .roots
  | 1 => .address
  | 2 => .copy
  | 3 => .value
  | 4 => .scratch

theorem lookupTapes_injective : Function.Injective lookupTapes := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [lookupTapes]

inductive LookupLabel
  | start
  | lookup (label : MachinePreservingLookupClean.Label)
  | tag | move | finish
  deriving DecidableEq, Fintype

def lookupProgram (address : Nat) : LookupLabel → TM2.Stmt Alphabet LookupLabel State
  | .start => Reduction.MachineSubstitution.pushWord .address (encodeWord address).reverse
      (.goto fun _ => .lookup (.run .copyFirst))
  | .lookup label => MachinePreservingLookupClean.statement lookupTapes LookupLabel.lookup
      (some .tag) label
  | .tag => Reduction.MachineSubstitution.pushWord .reversed (encodeWord 5)
      (.goto fun _ => .move)
  | .move => Reduction.MachineTransfer.loopAt .value .reversed id false .move (some .finish)
  | .finish => .pop .address (fun _ _ => initialState)
      (.push .count (fun _ => true) .halt)

def lookupSteps (input : Input) (address : Nat) : Nat :=
  MachinePreservingLookupClean.steps input.roots address +
    (rootLookup input.roots address) + 5

private theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem lookupTailTrace (seedAddress : Nat) (input : Input) (address : Nat)
    (selected : input.roots[address]? = some (rootLookup input.roots address))
    (base : Tape → List Bool) (frame : Frame input base) :
    (advance (TM2.step (lookupProgram seedAddress)))^[
      MachinePreservingLookupClean.steps input.roots address +
        rootLookup input.roots address + 4]
      (some ⟨some (.lookup (.run .copyFirst)), initialState,
        Function.update base .address (encodeWord address)⟩) =
      some ⟨none, initialState,
        emitTapes base [.input (rootLookup input.roots address)]⟩ := by
  let wire := rootLookup input.roots address
  let seeded := Function.update base .address (encodeWord address)
  let found := Function.update (Function.update base .address (encodeWord 0))
    .value (encodeWord wire)
  let tagged := Function.update found .reversed ((encodeWord 5).reverse ++ base .reversed)
  let moved := Function.update (Function.update base .address (encodeWord 0))
    .reversed ((encodeWord wire).reverse ++ (encodeWord 5).reverse ++ base .reversed)
  have haddress := frame.clean .address (by rfl)
  have hvalue := frame.clean .value (by rfl)
  have hcopy := frame.clean .copy (by rfl)
  have hscratch := frame.clean .scratch (by rfl)
  have lookup := MachinePreservingLookupClean.traceAt_fromTapes
    lookupTapes lookupTapes_injective LookupLabel.lookup (some .tag)
    (lookupProgram seedAddress) (fun _ => rfl) seeded input.roots
    (by simpa [seeded, lookupTapes] using frame.rootsWord)
    (by simpa [seeded, lookupTapes] using hscratch)
    address wire selected []
    (by simp [seeded, lookupTapes])
    (by simpa [seeded, lookupTapes] using hcopy) ((), false) none
  have lookupFrame : MachinePreservingLookup.initialTapes lookupTapes seeded 0 [] []
      (encodeWord wire ++ seeded (lookupTapes 3)) = found := by
    funext tape
    cases tape <;> simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes,
      lookupTapes, seeded, found, hvalue, hcopy]
  rw [lookupFrame] at lookup
  have tag : (advance (TM2.step (lookupProgram seedAddress)))^[1]
      (some ⟨some .tag, initialState, found⟩) =
      some ⟨some .move, initialState, tagged⟩ := by
    change some (TM2.stepAux (lookupProgram seedAddress .tag) initialState found) = _
    simp [lookupProgram, Reduction.MachineSubstitution.stepAux_pushWord,
      TM2.stepAux, tagged, found]
  have move := Reduction.MachineTransfer.transferAt_fromTapes
    (Γ := Alphabet) .value .reversed (by decide) id false LookupLabel.move
    (some LookupLabel.finish) (lookupProgram seedAddress) rfl tagged ((), false) none
  have valueWord : tagged .value = encodeWord wire := by simp [tagged, found]
  have moveFrame : Reduction.MachineTransfer.tapesAt .value .reversed tagged []
      ((tagged .value).reverse.map id ++ tagged .reversed) = moved := by
    funext tape
    cases tape <;> simp [Reduction.MachineTransfer.tapesAt, tagged, found, moved,
      hvalue, List.append_assoc]
  rw [moveFrame, valueWord, encodeWord_length] at move
  have finish : (advance (TM2.step (lookupProgram seedAddress)))^[1]
      (some ⟨some .finish, initialState, moved⟩) =
      some ⟨none, initialState, emitTapes base [.input wire]⟩ := by
    change some (TM2.stepAux (lookupProgram seedAddress .finish) initialState moved) = _
    simp only [lookupProgram, TM2.stepAux]
    congr 2
    funext tape
    cases tape <;> simp [moved, emitTapes, tokenBits, tokenWords, Token.words,
      encodeWords, encodeWord, haddress, List.reverse_append, List.append_assoc]
  have total := trace_trans _ (trace_trans _ lookup tag) move
  have result := trace_trans _ total finish
  have time : ((MachinePreservingLookupClean.steps input.roots address + 1) +
      (wire + 1 + 1)) + 1 =
      MachinePreservingLookupClean.steps input.roots address + rootLookup input.roots address + 4 := by
    dsimp [wire]
    omega
  rw [time] at result
  exact result

theorem lookupTrace (input : Input) (address : Nat)
    (selected : input.roots[address]? = some (rootLookup input.roots address))
    (base : Tape → List Bool) (frame : Frame input base) :
    (advance (TM2.step (lookupProgram address)))^[lookupSteps input address]
      (some ⟨some .start, initialState, base⟩) =
      some ⟨none, initialState,
        emitTapes base [.input (rootLookup input.roots address)]⟩ := by
  have haddress := frame.clean .address (by rfl)
  have start : (advance (TM2.step (lookupProgram address)))^[1]
      (some ⟨some .start, initialState, base⟩) =
      some ⟨some (.lookup (.run .copyFirst)), initialState,
        Function.update base .address (encodeWord address)⟩ := by
    change some (TM2.stepAux (lookupProgram address .start) initialState base) = _
    simp [lookupProgram, Reduction.MachineSubstitution.stepAux_pushWord,
      TM2.stepAux, haddress]
  have tail := lookupTailTrace address input address selected base frame
  have h := trace_trans _ start tail
  have time : 1 + (MachinePreservingLookupClean.steps input.roots address +
      rootLookup input.roots address + 4) = lookupSteps input address := by
    unfold lookupSteps
    omega
  rw [time] at h
  exact h

theorem lookupSteps_le (input : Input) (address : Nat)
    (selected : input.roots[address]? = some (rootLookup input.roots address)) :
    lookupSteps input address ≤ 10 * (input.size + 1) := by
  have hl := MachinePreservingLookupClean.steps_le input.roots address _ selected
  have hw := MachineLookupSpec.output_length_le input.roots address _ selected
  rw [encodeWord_length] at hw
  unfold lookupSteps Input.size
  omega

def Emitter.root (valid : Input → Prop) (address : Nat)
    (present : ∀ input, valid input →
      input.roots[address]? = some (rootLookup input.roots address)) :
    Emitter valid (fun input => [.input (rootLookup input.roots address)]) where
  Label := LookupLabel
  finite := inferInstance
  entry := .start
  program := lookupProgram address
  steps input := lookupSteps input address
  constant := 10
  trace input hv base frame := lookupTrace input address (present input hv) base frame
  bound input hv := lookupSteps_le input address (present input hv)

def positionDepth : Position → Nat
  | .current | .zero => 0
  | .succ p | .pred p => positionDepth p + 1

theorem position_le (p : Position) (cursor : Nat) :
    p.eval cursor ≤ cursor + positionDepth p := by
  induction p with
  | current => simp [Position.eval, positionDepth]
  | zero => simp [Position.eval, positionDepth]
  | succ p ih => simp only [Position.eval, positionDepth]; omega
  | pred p ih => simp only [Position.eval, positionDepth]; omega

structure Selector (predicate : Input → Bool) where
  Label : Type
  finite : Fintype Label
  entry : Label
  program : Label → TM2.Stmt Alphabet Label State
  steps : Input → Nat
  constant : Nat
  trace : ∀ (input : Input) (base : Tape → List Bool), Frame input base →
    (advance (TM2.step program))^[steps input]
      (some ⟨some entry, initialState, base⟩) =
      some ⟨none, (((), predicate input), none), base⟩
  bound : ∀ input, steps input ≤ constant * (input.size + 1)

attribute [instance] Selector.finite

def compareTape : Fin 4 → Tape
  | 0 => .position
  | 1 => .capacity
  | 2 => .saveLeft
  | 3 => .saveRight

def compareSlots : Fin 4 ↪ Tape where
  toFun := compareTape
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all [compareTape]

@[simp] theorem compareSlots_apply (i : Fin 4) : compareSlots i = compareTape i := rfl

inductive TestLabel
  | position (label : PositionMachine.Label)
  | compare (label : MachineUnaryLessAt.Label)
  | atZero | drain
  deriving DecidableEq, Fintype

def testPredicate (within : Bool) (p : Position) (input : Input) : Bool :=
  if within then decide (p.eval input.cursor < input.capacity)
  else decide (p.eval input.cursor = 0)

def testProgram (within : Bool) (p : Position) :
    TestLabel → TM2.Stmt Alphabet TestLabel State
  | .position label => PositionMachine.statement .cursor .scratch .position p
      TestLabel.position (some (if within then .compare .scan else .atZero)) label
  | .compare label => MachineUnaryLessAt.statement compareSlots TestLabel.compare
      (some .drain) label
  | .atZero => .peek .position (fun _ head => (((), !(head.getD false)), none))
      (.goto fun _ => .drain)
  | .drain => MachineDrain.drain .position .drain none

def testSteps (within : Bool) (p : Position) (input : Input) : Nat :=
  PositionMachine.steps p input.cursor +
    (if within then MachineUnaryLessAt.steps (p.eval input.cursor) input.capacity else 1) +
    (p.eval input.cursor + 2)

theorem testTrace (within : Bool) (p : Position) (input : Input)
    (base : Tape → List Bool) (frame : Frame input base) :
    (advance (TM2.step (testProgram within p)))^[testSteps within p input]
      (some ⟨some (.position .start), initialState, base⟩) =
      some ⟨none, (((), testPredicate within p input), none), base⟩ := by
  let prepared := Function.update base .position (encodeWord (p.eval input.cursor))
  have hp := frame.clean .position (by rfl)
  have hs := frame.clean .scratch (by rfl)
  have position := PositionMachine.positionTrace .cursor .scratch .position
    (by decide) (by decide) (by decide) p TestLabel.position
    (some (if within then .compare .scan else .atZero)) (testProgram within p)
    (fun _ => rfl) base input.cursor [] (by simpa using frame.cursorWord) hs ((), false) none
  simp only [hp, List.append_nil] at position
  have test : (advance (TM2.step (testProgram within p)))^[
      if within then MachineUnaryLessAt.steps (p.eval input.cursor) input.capacity else 1]
      (some ⟨some (if within then .compare .scan else .atZero), initialState, prepared⟩) =
      some ⟨some .drain, (((), testPredicate within p input), none), prepared⟩ := by
    cases within with
    | false =>
      change some (TM2.stepAux (testProgram false p .atZero) initialState prepared) = _
      cases hv : p.eval input.cursor <;>
        simp [testProgram, testPredicate, TM2.stepAux, prepared, hv, encodeWord,
          List.replicate_succ]
    | true =>
      have hl := frame.clean .saveLeft (by rfl)
      have hr := frame.clean .saveRight (by rfl)
      have cmp := MachineUnaryLessAt.lessThanTrace compareSlots TestLabel.compare
        (some TestLabel.drain) (testProgram true p) (fun _ => rfl) prepared
        (p.eval input.cursor) input.capacity [] []
        (by simp [prepared, compareSlots_apply, compareTape])
        (by simpa [prepared, compareSlots_apply, compareTape] using frame.capacityWord)
        (by simpa [prepared, compareSlots_apply, compareTape] using hl)
        (by simpa [prepared, compareSlots_apply, compareTape] using hr) () false none
      simpa [testPredicate, initialState] using cmp
  have drain := MachineDrain.drainTrace .position TestLabel.drain none
    (testProgram within p) rfl base (encodeWord (p.eval input.cursor))
    ((), testPredicate within p input) none
  have finish : Function.update base .position [] = base := by
    rw [← hp, Function.update_eq_self]
  rw [encodeWord_length, finish] at drain
  exact trace_trans _ (trace_trans _ position test) drain

theorem testSteps_le (within : Bool) (p : Position) (input : Input) :
    testSteps within p input ≤ (10 + 4 * positionDepth p) * (input.size + 1) := by
  have he := PositionMachine.steps_le_time p input.cursor
  simp only [PositionMachine.timePolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at he
  have hp := position_le p input.cursor
  have hn := Nat.min_le_left (p.eval input.cursor) input.capacity
  have hs : input.cursor ≤ input.size := by simp [Input.size]; omega
  have hd : positionDepth p ≤ positionDepth p * (input.size + 1) := by
    exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  cases within <;> simp only [testSteps, Bool.false_eq_true,
    ite_false, ite_true, MachineUnaryLessAt.steps] <;> nlinarith

def Selector.positionTest (within : Bool) (p : Position) : Selector (testPredicate within p) where
  Label := TestLabel
  finite := inferInstance
  entry := .position .start
  program := testProgram within p
  steps := testSteps within p
  constant := 10 + 4 * positionDepth p
  trace := testTrace within p
  bound := testSteps_le within p

inductive AffineLabel
  | position (label : PositionMachine.Label)
  | seed | scan | restore | drain
  | lookup (label : LookupLabel)
  deriving DecidableEq, Fintype

def affineProgram (p : Position) (coefficient offset : Nat) :
    AffineLabel → TM2.Stmt Alphabet AffineLabel State
  | .position label => PositionMachine.statement .cursor .scratch .position p
      AffineLabel.position (some .seed) label
  | .seed => MachineUnaryAffineAt.seed .address offset .scan
  | .scan => MachineUnaryAffineAt.scan .position .scratch .address coefficient .scan .restore
  | .restore => Reduction.MachineTransfer.loopAt .scratch .position id false .restore (some .drain)
  | .drain => MachineDrain.drain .position .drain (some (.lookup (.lookup (.run .copyFirst))))
  | .lookup label => MachineSubroutine.statement AffineLabel.lookup none (lookupProgram 0 label)

def affineAddress (p : Position) (coefficient offset : Nat) (input : Input) : Nat :=
  coefficient * p.eval input.cursor + offset

def affineSteps (p : Position) (coefficient offset : Nat) (input : Input) : Nat :=
  PositionMachine.steps p input.cursor + (2 * (p.eval input.cursor + 1) + 1) +
    (p.eval input.cursor + 2) +
      (MachinePreservingLookupClean.steps input.roots (affineAddress p coefficient offset input) +
        rootLookup input.roots (affineAddress p coefficient offset input) + 4)

theorem affineTrace (p : Position) (coefficient offset : Nat) (input : Input)
    (present : input.roots[affineAddress p coefficient offset input]? =
      some (rootLookup input.roots (affineAddress p coefficient offset input)))
    (base : Tape → List Bool) (frame : Frame input base) :
    (advance (TM2.step (affineProgram p coefficient offset)))^[affineSteps p coefficient offset input]
      (some ⟨some (.position .start), initialState, base⟩) =
      some ⟨none, initialState, emitTapes base
        [.input (rootLookup input.roots (affineAddress p coefficient offset input))]⟩ := by
  let pos := p.eval input.cursor
  let addr := affineAddress p coefficient offset input
  let prepared := Function.update base .position (encodeWord pos)
  let addressed := Function.update base .address (encodeWord addr)
  have hp := frame.clean .position (by rfl)
  have ha := frame.clean .address (by rfl)
  have hs := frame.clean .scratch (by rfl)
  have position := PositionMachine.positionTrace .cursor .scratch .position
    (by decide) (by decide) (by decide) p AffineLabel.position (some .seed)
    (affineProgram p coefficient offset) (fun _ => rfl) base input.cursor []
    (by simpa using frame.cursorWord) hs ((), false) none
  simp only [hp, List.append_nil] at position
  have address := MachineUnaryAffineAt.seededAffineTrace .position .scratch .address
    (by decide) (by decide) (by decide) coefficient offset AffineLabel.seed
    AffineLabel.scan AffineLabel.restore (some AffineLabel.drain)
    (affineProgram p coefficient offset) rfl rfl rfl prepared pos []
    (by simp [prepared]) (by simpa [prepared] using hs) ((), false) none
  have haddressed : Function.update prepared .address
      (encodeWord (coefficient * pos + offset) ++ prepared .address) =
      Function.update addressed .position (encodeWord pos) := by
    funext tape
    cases tape <;> simp [prepared, addressed, addr, affineAddress, pos, ha]
  rw [haddressed] at address
  have drain := MachineDrain.drainTrace .position AffineLabel.drain
    (some (.lookup (.lookup (.run .copyFirst)))) (affineProgram p coefficient offset)
    rfl addressed (encodeWord pos) ((), false) none
  have hclean : Function.update addressed .position [] = addressed := by
    have h : addressed .position = [] := by simpa [addressed] using hp
    rw [← h, Function.update_eq_self]
  rw [encodeWord_length, hclean] at drain
  have source := lookupTailTrace 0 input addr present base frame
  have lookup := MachineSubroutine.trace AffineLabel.lookup none (lookupProgram 0)
    (affineProgram p coefficient offset) (fun _ => rfl)
    (MachinePreservingLookupClean.steps input.roots addr + rootLookup input.roots addr + 4)
    _ _ source
  simp only [MachineSubroutine.configuration, MachineSubroutine.label] at lookup
  exact trace_trans _ (trace_trans _ (trace_trans _ position address) drain) lookup

theorem affineSteps_le (p : Position) (coefficient offset : Nat) (input : Input)
    (present : input.roots[affineAddress p coefficient offset input]? =
      some (rootLookup input.roots (affineAddress p coefficient offset input))) :
    affineSteps p coefficient offset input ≤ (30 + 3 * positionDepth p) * (input.size + 1) := by
  have he := PositionMachine.steps_le_time p input.cursor
  simp only [PositionMachine.timePolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at he
  have hp := position_le p input.cursor
  have hl := MachinePreservingLookupClean.steps_le input.roots
    (affineAddress p coefficient offset input) _ present
  have hw := MachineLookupSpec.output_length_le input.roots
    (affineAddress p coefficient offset input) _ present
  rw [encodeWord_length] at hw
  have hs : input.cursor + (encodeWords input.roots).length ≤ input.size := by
    simp [Input.size]
  have hd : positionDepth p ≤ positionDepth p * (input.size + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  unfold affineSteps
  nlinarith

def Emitter.affineRoot (valid : Input → Prop) (p : Position) (coefficient offset : Nat)
    (present : ∀ input, valid input →
      input.roots[affineAddress p coefficient offset input]? =
        some (rootLookup input.roots (affineAddress p coefficient offset input))) :
    Emitter valid (fun input => [.input
      (rootLookup input.roots (affineAddress p coefficient offset input))]) where
  Label := AffineLabel
  finite := inferInstance
  entry := .position .start
  program := affineProgram p coefficient offset
  steps := affineSteps p coefficient offset
  constant := 30 + 3 * positionDepth p
  trace input hv base frame := affineTrace p coefficient offset input (present input hv) base frame
  bound input hv := affineSteps_le p coefficient offset input (present input hv)

namespace Emitter

variable {valid validLeft validRight : Input → Prop}
variable {yes no : Input → List Token} {predicate : Input → Bool}

abbrev ChoiceLabel (test : Selector predicate) (left : Emitter validLeft yes)
    (right : Emitter validRight no) := test.Label ⊕ (Unit ⊕ (left.Label ⊕ right.Label))

def choiceProgram (test : Selector predicate) (left : Emitter validLeft yes)
    (right : Emitter validRight no) : ChoiceLabel test left right →
      TM2.Stmt Alphabet (ChoiceLabel test left right) State
  | .inl l => MachineSubroutine.statement Sum.inl (some (.inr (.inl ()))) (test.program l)
  | .inr (.inl _) => .branch (fun s => s.1.2)
      (.load (fun _ => initialState) (.goto fun _ => .inr (.inr (.inl left.entry))))
      (.load (fun _ => initialState) (.goto fun _ => .inr (.inr (.inr right.entry))))
  | .inr (.inr (.inl l)) => MachineSubroutine.statement
      (fun label => .inr (.inr (.inl label))) none (left.program l)
  | .inr (.inr (.inr l)) => MachineSubroutine.statement
      (fun label => .inr (.inr (.inr label))) none (right.program l)

def choice (test : Selector predicate) (left : Emitter validLeft yes)
    (right : Emitter validRight no)
    (leftValid : ∀ input, valid input → predicate input = true → validLeft input)
    (rightValid : ∀ input, valid input → predicate input = false → validRight input) :
    Emitter valid (fun input => if predicate input then yes input else no input) where
  Label := ChoiceLabel test left right
  finite := inferInstance
  entry := .inl test.entry
  program := choiceProgram test left right
  steps input := test.steps input + 1 +
    (if predicate input then left.steps input else right.steps input)
  constant := test.constant + 1 + left.constant + right.constant
  trace input hv base frame := by
    have ht := MachineSubroutine.trace Sum.inl (some (.inr (.inl ())))
      test.program (choiceProgram test left right) (fun _ => rfl)
      (test.steps input) _ _ (test.trace input base frame)
    simp only [MachineSubroutine.configuration, MachineSubroutine.label] at ht
    cases hpred : predicate input with
    | false =>
      have dispatch : (advance (TM2.step (choiceProgram test left right)))^[1]
          (some ⟨some (.inr (.inl ())), (((), predicate input), none), base⟩) =
          some ⟨some (.inr (.inr (.inr right.entry))), initialState, base⟩ := by
        change some (TM2.stepAux _ _ _) = _
        simp [choiceProgram, TM2.stepAux, hpred]
      have body := MachineSubroutine.trace (fun label => .inr (.inr (.inr label))) none
        right.program (choiceProgram test left right) (fun _ => rfl)
        (right.steps input) _ _ (right.trace input (rightValid input hv hpred) base frame)
      simp only [MachineSubroutine.configuration, MachineSubroutine.label] at body
      simpa only [hpred, Bool.false_eq_true, ite_false] using
        trace_trans _ (trace_trans _ ht dispatch) body
    | true =>
      have dispatch : (advance (TM2.step (choiceProgram test left right)))^[1]
          (some ⟨some (.inr (.inl ())), (((), predicate input), none), base⟩) =
          some ⟨some (.inr (.inr (.inl left.entry))), initialState, base⟩ := by
        change some (TM2.stepAux _ _ _) = _
        simp [choiceProgram, TM2.stepAux, hpred]
      have body := MachineSubroutine.trace (fun label => .inr (.inr (.inl label))) none
        left.program (choiceProgram test left right) (fun _ => rfl)
        (left.steps input) _ _ (left.trace input (leftValid input hv hpred) base frame)
      simp only [MachineSubroutine.configuration, MachineSubroutine.label] at body
      simpa only [hpred, ite_true] using
        trace_trans _ (trace_trans _ ht dispatch) body
  bound input hv := by
    have ht := test.bound input
    have hs : 0 < input.size + 1 := Nat.succ_pos _
    cases hpred : predicate input with
    | false =>
      have hr := right.bound input (rightValid input hv hpred)
      simp only [Bool.false_eq_true, ite_false]
      nlinarith
    | true =>
      have hl := left.bound input (leftValid input hv hpred)
      simp only [ite_true]
      nlinarith

end Emitter

variable {K Λ σ : Type} {Γ : K → Type} [∀ k, DecidableEq (Γ k)]
variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ]

def RootsValid (indexing : ConfigIndex.Indexing Γ Λ σ) (input : Input) : Prop :=
  indexing.width input.capacity ≤ input.roots.length

def termTokens (indexing : ConfigIndex.Indexing Γ Λ σ) (term : Term Γ σ)
    (input : Input) : List Token :=
  term.tokens indexing input.roots input.capacity input.cursor

def compileCell (indexing : ConfigIndex.Indexing Γ Λ σ) (k : K) (p : Position)
    (symbol : Option (Γ k)) :
    Emitter (RootsValid indexing) (termTokens indexing (.cell k p symbol)) := by
  let leftValid : Input → Prop := fun input =>
    RootsValid indexing input ∧ p.eval input.cursor < input.capacity
  let addressOffset := indexing.labelCount + indexing.stateCount + (indexing.symbols ⟨k, symbol⟩).val
  let left := Emitter.affineRoot leftValid p indexing.symbolCount addressOffset (by
    intro input hv
    apply rootLookup_present indexing input.roots input.capacity hv.1
    simpa only [affineAddress, addressOffset, Nat.mul_comm, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm] using
      cellAddress_lt_width indexing input.capacity k (p.eval input.cursor) symbol hv.2)
  let right := Emitter.literal (RootsValid indexing) [.const (decide ((none : Option (Γ k)) = symbol))]
  let branch := Emitter.choice (Selector.positionTest true p) left right
    (valid := RootsValid indexing)
    (fun input hv ht => ⟨hv, by simpa [testPredicate] using ht⟩)
    (fun _ hv _ => hv)
  exact branch.congr (fun input => by
    by_cases hp : p.eval input.cursor < input.capacity <;>
      simp [termTokens, Term.tokens, testPredicate, hp, affineAddress, addressOffset,
        Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm])

def compile (indexing : ConfigIndex.Indexing Γ Λ σ) :
    (term : Term Γ σ) → Emitter (RootsValid indexing) (termTokens indexing term)
  | .state v => Emitter.root (RootsValid indexing) (indexing.labelCount + (indexing.states v).val)
      (fun input hv => rootLookup_present indexing input.roots input.capacity hv _
        (stateAddress_lt_width indexing input.capacity v))
  | .cell k p a => compileCell indexing k p a
  | .const b => Emitter.literal (RootsValid indexing) [.const b]
  | .not e => ((compile indexing e).seq (Emitter.literal (RootsValid indexing) [.not])).congr
      (fun input => rfl)
  | .and e f => ((compile indexing e).seq
      ((compile indexing f).seq (Emitter.literal (RootsValid indexing) [.and]))).congr
        (fun input => by simp [termTokens, Term.tokens, List.append_assoc])
  | .or e f => ((compile indexing e).seq
      ((compile indexing f).seq (Emitter.literal (RootsValid indexing) [.or]))).congr
        (fun input => by simp [termTokens, Term.tokens, List.append_assoc])
  | .atZero p yes no =>
      (Emitter.choice (Selector.positionTest false p) (compile indexing yes) (compile indexing no)
        (fun _ hv _ => hv) (fun _ hv _ => hv)).congr
          (fun input => by simp [termTokens, Term.tokens, testPredicate])
  | .within p yes no =>
      (Emitter.choice (Selector.positionTest true p) (compile indexing yes) (compile indexing no)
        (fun _ hv _ => hv) (fun _ hv _ => hv)).congr
          (fun input => by simp [termTokens, Term.tokens, testPredicate])

noncomputable def timePolynomial (indexing : ConfigIndex.Indexing Γ Λ σ) (term : Term Γ σ) :
    Polynomial Nat := Polynomial.C (compile indexing term).constant * (Polynomial.X + 1)

def termInPolynomialTime (indexing : ConfigIndex.Indexing Γ Λ σ) (term : Term Γ σ)
    (input : Input) (valid : RootsValid indexing input) (base : Tape → List Bool)
    (frame : Frame input base) :
    StateTransition.EvalsToInTime (compile indexing term).machine.step
      ⟨some (compile indexing term).entry, initialState, base⟩
      (some ⟨none, initialState, emitTapes base
        (term.tokens indexing input.roots input.capacity input.cursor)⟩)
      ((timePolynomial indexing term).eval input.size) where
  steps := (compile indexing term).steps input
  evals_in_steps := (compile indexing term).trace input valid base frame
  steps_le_m := by
    simpa only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] using
      (compile indexing term).bound input valid

def globalTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (term : Global (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) : List Token :=
  term.tokens indexing input.roots input.capacity input.cursor

def compileGlobal (indexing : ConfigIndex.Indexing Γ Λ σ) :
    (term : Global (Γ := Γ) (Λ := Λ) (σ := σ)) →
      Emitter (RootsValid indexing) (globalTokens indexing term)
  | .label label => Emitter.root (RootsValid indexing) (indexing.labels label).val
      (fun input hv => rootLookup_present indexing input.roots input.capacity hv _
        (labelAddress_lt_width indexing input.capacity label))
  | .data term => compile indexing term
  | .const b => Emitter.literal (RootsValid indexing) [.const b]
  | .and e f => ((compileGlobal indexing e).seq
      ((compileGlobal indexing f).seq (Emitter.literal (RootsValid indexing) [.and]))).congr
        (fun input => by simp [globalTokens, Global.tokens, List.append_assoc])
  | .or e f => ((compileGlobal indexing e).seq
      ((compileGlobal indexing f).seq (Emitter.literal (RootsValid indexing) [.or]))).congr
        (fun input => by simp [globalTokens, Global.tokens, List.append_assoc])

def globalInLinearTime (indexing : ConfigIndex.Indexing Γ Λ σ)
    (term : Global (Γ := Γ) (Λ := Λ) (σ := σ))
    (input : Input) (valid : RootsValid indexing input) (base : Tape → List Bool)
    (frame : Frame input base) :
    StateTransition.EvalsToInTime (compileGlobal indexing term).machine.step
      ⟨some (compileGlobal indexing term).entry, initialState, base⟩
      (some ⟨none, initialState, emitTapes base
        (term.tokens indexing input.roots input.capacity input.cursor)⟩)
      ((compileGlobal indexing term).constant * (input.size + 1)) where
  steps := (compileGlobal indexing term).steps input
  evals_in_steps := (compileGlobal indexing term).trace input valid base frame
  steps_le_m := (compileGlobal indexing term).bound input valid

end BinPackingGames.Foundations.Complexity.CookLevin.TermMachine

end OAI
