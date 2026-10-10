import Mathlib
import OAI.Computability.MaxCut.Machines.MachineTemplateAddress

namespace OAI

namespace MaxCutGames.Reduction.MachineRhsLoad

open Turing
open MaxCutGames.Foundations.Complexity

abbrev State (k : Nat) (σ : Type) := (((Fin k → Bool) × σ) × Unit) × Option Bool
abbrev Alphabet {K : Type} (_ : K) := Bool

def rhs {k σ} (state : State k σ) : Fin k → Bool := state.1.1.1

def setRhs {k σ} (state : State k σ) (values : Fin k → Bool) : State k σ :=
  (((values, state.1.1.2), state.1.2), state.2)

@[simp] theorem rhs_setRhs {k σ} (state : State k σ) (values : Fin k → Bool) :
    rhs (setRhs state values) = values := rfl

@[simp] theorem setRhs_setRhs {k σ} (state : State k σ)
    (first second : Fin k → Bool) : setRhs (setRhs state first) second = setRhs state second := rfl

@[simp] theorem setRhs_same {k σ} (state : State k σ) : setRhs state (rhs state) = state := rfl

def fill {k : Nat} (values initial : Fin k → Bool) (cells : List (Fin k)) : Fin k → Bool :=
  cells.foldl (fun current i => Function.update current i (values i)) initial

theorem fill_apply {k : Nat} (values initial : Fin k → Bool) (cells : List (Fin k))
    (i : Fin k) : fill values initial cells i = if i ∈ cells then values i else initial i := by
  induction cells generalizing initial with
  | nil => simp [fill]
  | cons j cells ih =>
    change fill values (Function.update initial j (values j)) cells i = _
    rw [ih]
    by_cases hi : i ∈ cells
    · simp [hi]
    · by_cases hij : i = j
      · subst j; simp [hi]
      · simp [hi, hij]

theorem fill_all {k : Nat} (values initial : Fin k → Bool) :
    fill values initial (List.finRange k) = values := by
  funext i
  rw [fill_apply]
  simp only [List.mem_finRange, ↓reduceIte]

variable {k : Nat} {K Λ σ : Type} [DecidableEq K]

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State k σ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def peekChain (field : Fin k → K) (exit : Option Λ) :
    List (Fin k) → TM2.Stmt (Alphabet (K := K)) Λ (State k σ)
  | [] => finish exit
  | i :: rest =>
    .peek (field i) (fun state head =>
      setRhs state (Function.update (rhs state) i (head.getD false)))
      (peekChain field exit rest)

def statement (field : Fin k → K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State k σ) := peekChain field exit (List.finRange k)

def readRhs (field : Fin k → K) (tapes : K → List Bool) : Fin k → Bool :=
  fun i => (tapes (field i)).head?.getD false

theorem stepAux_peekChain (field : Fin k → K) (exit : Option Λ)
    (cells : List (Fin k)) (state : State k σ) (tapes : K → List Bool) :
    TM2.stepAux (peekChain field exit cells) state tapes =
      ⟨exit, setRhs state (fill (readRhs field tapes) (rhs state) cells), tapes⟩ := by
  induction cells generalizing state with
  | nil => cases exit <;> rfl
  | cons i rest ih =>
    simp only [peekChain, TM2.stepAux]
    rw [ih]
    rfl

theorem stepAux_statement (field : Fin k → K) (exit : Option Λ)
    (state : State k σ) (tapes : K → List Bool) :
    TM2.stepAux (statement field exit) state tapes =
      ⟨exit, setRhs state (readRhs field tapes), tapes⟩ := by
  rw [statement, stepAux_peekChain, fill_all]

omit [DecidableEq K] in
theorem readRhs_of_unary (field : Fin k → K) (tapes : K → List Bool)
    (values : Fin k → Bool) (suffix : Fin k → List Bool)
    (encoded : ∀ i, tapes (field i) = encodeWord (if values i then 1 else 0) ++ suffix i) :
    readRhs field tapes = values := by
  funext i
  rw [readRhs, encoded]
  cases values i <;> rfl

/-- One actual transition loads every RHS register while preserving all tapes,
caller registers, and the existing optional head register. -/
theorem loadStep (field : Fin k → K) (entry : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atEntry : program entry = statement field exit)
    (state : State k σ) (tapes : K → List Bool) (values : Fin k → Bool)
    (suffix : Fin k → List Bool)
    (encoded : ∀ i, tapes (field i) = encodeWord (if values i then 1 else 0) ++ suffix i) :
    TM2.step program ⟨some entry, state, tapes⟩ =
      some ⟨exit, setRhs state values, tapes⟩ := by
  change some (TM2.stepAux (program entry) state tapes) = _
  rw [atEntry, stepAux_statement, readRhs_of_unary field tapes values suffix encoded]

def loadInTime (field : Fin k → K) (entry : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atEntry : program entry = statement field exit)
    (state : State k σ) (tapes : K → List Bool) (values : Fin k → Bool)
    (suffix : Fin k → List Bool)
    (encoded : ∀ i, tapes (field i) = encodeWord (if values i then 1 else 0) ++ suffix i) :
    StateTransition.EvalsToInTime (TM2.step program) ⟨some entry, state, tapes⟩
      (some ⟨exit, setRhs state values, tapes⟩) 1 where
  steps := 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[1] _ = _
    simpa only [Function.iterate_one, MachineComposition.advance_some] using
      loadStep field entry exit program atEntry state tapes values suffix encoded
  steps_le_m := Nat.le_refl _

omit [DecidableEq K] in
theorem peekChain_pushBound (field : Fin k → K) (exit : Option Λ) (cells : List (Fin k)) :
    Runtime.statementPushBound (peekChain (σ := σ) field exit cells) = 0 := by
  induction cells with
  | nil => cases exit <;> rfl
  | cons i rest ih => exact ih

omit [DecidableEq K] in
theorem statement_pushBound (field : Fin k → K) (exit : Option Λ) :
    Runtime.statementPushBound (statement (σ := σ) field exit) = 0 :=
  peekChain_pushBound field exit (List.finRange k)

end MaxCutGames.Reduction.MachineRhsLoad

/-! Execute all fixed outcome rows after the existing RHS loader. A single
dispatcher freezes the loaded finite RHS vector into labels. Every row is an
actual address-edge phase; no row-run or whole-loop execution is assumed.
Program definitions contain only fixed templates, literal permutations, and
tape/label placement. Numeric names, radix, and capacity occur only in tapes
and the semantic correctness hypotheses. -/

namespace MaxCutGames.Reduction.MachineOutcomeRows

open Turing
open MaxCutGames.Foundations.Complexity

structure Spec (q width : Nat) where
  left : List (MachineFieldTemplate.Token q)
  right : List (MachineFieldTemplate.Token q)
  permutation : List Bool

/-- Numeric interpretations are proof-side data, separate from the program. -/
structure Values (width : Nat) where
  left : List Nat
  right : List Nat
  left_length : left.length = width
  right_length : right.length = width

abbrev Rhs (k : Nat) := Fin k → Bool
abbrev Row (k q width : Nat) := Rhs k → Spec q width
abbrev State (k : Nat) (σ : Type) := MachineRhsLoad.State k σ
abbrev Alphabet {K : Type} (_ : K) := Bool

variable {k q width : Nat} {K Λ σ : Type} [DecidableEq K]

abbrev LocalLabel (slots : MachineAddressEdge.Tape q width ↪ K) (row : Spec q width) :=
  MachineAddressEdge.Label row.left.length row.right.length width
    (MachineTemplateAddress.chosen (MachineAddressEdge.addressSlots slots))

def localMain (slots : MachineAddressEdge.Tape q width ↪ K) (row : Spec q width) :
    LocalLabel slots row :=
  MachineAddressEdge.leftLabel (MachineTemplateAddress.emitLabel
    (MachineFieldTemplate.startAt row.left.length 0))

def localInstruction (slots : MachineAddressEdge.Tape q width ↪ K)
    (row : Spec q width) (place : LocalLabel slots row → Λ) (exit : Option Λ) :
    LocalLabel slots row → TM2.Stmt (Alphabet (K := K)) Λ (MachineAddressEdge.State σ) :=
  MachineAddressEdge.instruction row.left row.right row.permutation slots place exit

def payload (B C : Nat) (values : Spec q width → Values width) (row : Spec q width) :
    List Bool :=
  MachineAddressEdge.edgeBits B C (values row).left (values row).right row.permutation

def rowResult (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (row : Spec q width)
    (base : K → List Bool) : K → List Bool :=
  MachineAddressEdge.appended slots base (payload B C values row)

def rowCost (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (row : Spec q width)
    (base : K → List Bool) : Nat :=
  MachineAddressEdge.phaseSteps row.left row.right slots base B C
    (values row).left (values row).right

/-- Exact per-row costs at their actual accumulated output frames. -/
def rowCosts (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) :
    List (Spec q width) → (K → List Bool) → List Nat
  | [], _ => []
  | row :: rows, base => rowCost slots B C values row base ::
      rowCosts slots B C values rows (rowResult slots B C values row base)

theorem rowCosts_length (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width)
    (rows : List (Spec q width)) (base : K → List Bool) :
    (rowCosts slots B C values rows base).length = rows.length := by
  induction rows generalizing base with
  | nil => rfl
  | cons row rows ih => simp only [rowCosts, List.length_cons, ih]

structure Invariant (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) : Prop where
  clean : MachineAddressEdge.Clean slots base
  radix : base (MachineAddressEdge.addressSlots slots .radix) = encodeWord B
  capacity : base (MachineAddressEdge.capacityTape slots) = encodeWord C
  correct : ∀ row ∈ rows,
    MachineFieldTemplate.templateOutput row.left
      (fun j => base (MachineAddressEdge.addressSlots slots (.field j))) =
        encodeWords (values row).left ∧
    MachineFieldTemplate.templateOutput row.right
      (fun j => base (MachineAddressEdge.addressSlots slots (.field j))) =
        encodeWords (values row).right

theorem Invariant.appended (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) (valid : Invariant slots B C values rows base) (bits : List Bool) :
    Invariant slots B C values rows (MachineAddressEdge.appended slots base bits) := by
  constructor
  · exact MachineAddressEdge.Clean.appended slots base valid.clean bits
  · simpa only [MachineAddressEdge.appended_address] using valid.radix
  · simpa only [MachineAddressEdge.appended_capacity] using valid.capacity
  · intro row hrow
    simpa only [MachineAddressEdge.appended_address] using valid.correct row hrow

theorem appended_nil (slots : MachineAddressEdge.Tape q width ↪ K) (base : K → List Bool) :
    MachineAddressEdge.appended slots base [] = base := by
  simp [MachineAddressEdge.appended, MachineFieldTemplate.outputTapes]

theorem sequence_result (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) :
    MachineFiniteSequence.resultOf (rowResult slots B C values) rows base =
      MachineAddressEdge.appended slots base (rows.flatMap (payload B C values)) := by
  induction rows generalizing base with
  | nil => simpa only [MachineFiniteSequence.resultOf, List.flatMap_nil] using
      (appended_nil slots base).symm
  | cons row rows ih =>
    rw [MachineFiniteSequence.resultOf, ih]
    exact MachineAddressEdge.appended_append slots base _ _

theorem sequence_steps (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) :
    MachineFiniteSequence.steps (rowResult slots B C values) (rowCost slots B C values)
      rows base = (rowCosts slots B C values rows base).sum := by
  induction rows generalizing base with
  | nil => rfl
  | cons row rows ih => simp only [MachineFiniteSequence.steps, rowCosts, List.sum_cons, ih]

def sequenceInstruction (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width))
    (place : MachineFiniteSequence.Label (LocalLabel slots) rows → Λ) (exit : Option Λ) :=
  MachineFiniteSequence.instruction (LocalLabel slots) (localMain slots)
    (localInstruction (σ := σ) slots) rows place exit

/-- The generic finite-sequence local obligation is discharged by the concrete
edge program, including its address arithmetic and capacity restoration. -/
theorem sequenceTrace (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width))
    (place : MachineFiniteSequence.Label (LocalLabel slots) rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (MachineAddressEdge.State σ))
    (atInstruction : ∀ label, P (place label) = sequenceInstruction slots rows place exit label)
    (base : K → List Bool) (B C : Nat) (values : Spec q width → Values width)
    (valid : Invariant slots B C values rows base) (ambient : σ) :
    (MachineComposition.advance (TM2.step P))^[(rowCosts slots B C values rows base).sum]
      (some ⟨MachineFiniteSequence.entry (LocalLabel slots) (localMain slots) rows place exit,
        ((ambient, ()), none), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        MachineAddressEdge.appended slots base (rows.flatMap (payload B C values))⟩ := by
  have h := MachineFiniteSequence.trace (LocalLabel slots) (localMain slots)
    (localInstruction (σ := σ) slots) (rowResult slots B C values) (rowCost slots B C values)
    P (Invariant slots B C values rows) (fun _ => ((ambient, ()), none)) id rows
    (by
      intro row _ frame hframe
      exact Invariant.appended slots B C values rows frame hframe (payload B C values row))
    (by
      intro row hrow labels next placement frame hframe
      exact MachineAddressEdge.phaseTrace row.left row.right row.permutation slots
        labels next P placement frame B C (values row).left (values row).right
        (values row).left_length (values row).right_length hframe.clean hframe.radix
        hframe.capacity (hframe.correct row hrow).1 (hframe.correct row hrow).2 ambient none)
    place exit atInstruction base valid
  simpa only [sequence_steps, sequence_result, id_eq] using h

def selected (rows : List (Row k q width)) (rhs : Rhs k) : List (Spec q width) :=
  rows.map (fun row => row rhs)

@[simp] theorem selected_length (rows : List (Row k q width)) (rhs : Rhs k) :
    (selected rows rhs).length = rows.length := by simp [selected]

abbrev Label (slots : MachineAddressEdge.Tape q width ↪ K) (rows : List (Row k q width)) :=
  Unit ⊕ (Σ rhs : Rhs k, MachineFiniteSequence.Label (LocalLabel slots) (selected rows rhs))

instance localLabelFintype (slots : MachineAddressEdge.Tape q width ↪ K) (row : Spec q width) :
    Fintype (LocalLabel slots row) := by unfold LocalLabel; infer_instance

instance localLabelDecidableEq (slots : MachineAddressEdge.Tape q width ↪ K) (row : Spec q width) :
    DecidableEq (LocalLabel slots row) := by
  letI : DecidableEq (MachineTemplateAddress.Label row.left.length width
      (MachineTemplateAddress.chosen (MachineAddressEdge.addressSlots slots))) := by
    infer_instance
  letI : DecidableEq (MachineTemplateAddress.Label row.right.length width
      (MachineTemplateAddress.chosen (MachineAddressEdge.addressSlots slots))) := by
    infer_instance
  dsimp only [LocalLabel, MachineAddressEdge.Label]
  infer_instance

instance labelFintype (slots : MachineAddressEdge.Tape q width ↪ K) (rows : List (Row k q width)) :
    Fintype (Label slots rows) := by unfold Label; infer_instance

instance labelDecidableEq (slots : MachineAddressEdge.Tape q width ↪ K) (rows : List (Row k q width)) :
    DecidableEq (Label slots rows) := by unfold Label; infer_instance

def sequenceEntry (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (rhs : Rhs k)
    (place : Label slots rows → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry (LocalLabel slots) (localMain slots) (selected rows rhs)
    (fun label => place (.inr ⟨rhs, label⟩)) exit

/-- Reuse the RHS vector already loaded by `MachineRhsLoad`; dispatch takes
one real transition, and resets only the optional temporary bit. -/
def dispatcher (slots : MachineAddressEdge.Tape q width ↪ K) :
    (rows : List (Row k q width)) → (Label slots rows → Λ) → Option Λ →
      TM2.Stmt (Alphabet (K := K)) Λ (State k σ)
  | [], _, exit => .load MachineFieldTemplate.reset (MachineFieldTemplate.jump exit)
  | row :: _rows, place, _ => .load MachineFieldTemplate.reset
      (.goto fun state => place (.inr ⟨MachineRhsLoad.rhs state,
        .inl (localMain slots (row (MachineRhsLoad.rhs state)))⟩))

def instruction (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ) :
    Label slots rows → TM2.Stmt (Alphabet (K := K)) Λ (State k σ)
  | .inl _ => dispatcher slots rows place exit
  | .inr ⟨rhs, label⟩ => sequenceInstruction slots (selected rows rhs)
      (fun l => place (.inr ⟨rhs, l⟩)) exit label

def program (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (exit : Option (Label slots rows)) :=
  instruction (σ := σ) slots rows id exit

theorem dispatcherStep (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atDispatcher : P (place (.inl ())) = dispatcher slots rows place exit)
    (base : K → List Bool) (rhs : Rhs k) (ambient : σ) (register : Option Bool) :
    TM2.step P ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩ =
      some ⟨sequenceEntry slots rows rhs place exit, (((rhs, ambient), ()), none), base⟩ := by
  change some (TM2.stepAux (P (place (.inl ()))) (((rhs, ambient), ()), register) base) = _
  rw [atDispatcher]
  cases rows with
  | nil => cases exit <;> rfl
  | cons row rows => rfl

theorem phaseTrace (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atInstruction : ∀ label, P (place label) = instruction slots rows place exit label)
    (base : K → List Bool) (rhs : Rhs k) (ambient : σ) (register : Option Bool)
    (B C : Nat) (values : Spec q width → Values width)
    (valid : Invariant slots B C values (selected rows rhs) base) :
    (MachineComposition.advance (TM2.step P))^[
      (rowCosts slots B C values (selected rows rhs) base).sum + 1]
      (some ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩) =
      some ⟨exit, (((rhs, ambient), ()), none), MachineAddressEdge.appended slots base
        ((selected rows rhs).flatMap (payload B C values))⟩ := by
  have first := dispatcherStep slots rows place exit P (atInstruction (.inl ()))
    base rhs ambient register
  have rest := sequenceTrace slots (selected rows rhs) (fun l => place (.inr ⟨rhs, l⟩))
    exit P (fun l => atInstruction (.inr ⟨rhs, l⟩)) base B C values valid (rhs, ambient)
  rw [Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step P))^[_]
    (TM2.step P ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩) = _
  rw [first]
  exact rest

def phaseInTime (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atInstruction : ∀ label, P (place label) = instruction slots rows place exit label)
    (base : K → List Bool) (rhs : Rhs k) (ambient : σ) (register : Option Bool)
    (B C : Nat) (values : Spec q width → Values width)
    (valid : Invariant slots B C values (selected rows rhs) base) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩
      (some ⟨exit, (((rhs, ambient), ()), none), MachineAddressEdge.appended slots base
        ((selected rows rhs).flatMap (payload B C values))⟩)
      ((rowCosts slots B C values (selected rows rhs) base).sum + 1) where
  steps := (rowCosts slots B C values (selected rows rhs) base).sum + 1
  evals_in_steps := phaseTrace slots rows place exit P atInstruction base rhs ambient register
    B C values valid
  steps_le_m := Nat.le_refl _

theorem emitted_output (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (rhs : Rhs k) (base : K → List Bool)
    (B C : Nat) (values : Spec q width → Values width) :
    MachineAddressEdge.appended slots base ((selected rows rhs).flatMap (payload B C values))
        (MachineAddressEdge.outputTape slots) =
      ((selected rows rhs).flatMap (payload B C values)).reverse ++
        base (MachineAddressEdge.outputTape slots) :=
  MachineAddressEdge.appended_output slots base _

theorem exact_row_count (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (rhs : Rhs k) (base : K → List Bool)
    (B C : Nat) (values : Spec q width → Values width) :
    (rowCosts slots B C values (selected rows rhs) base).length = rows.length := by
  rw [rowCosts_length, selected_length]

/-- Sum of fixed row polynomials; the additional constant is the dispatcher.
This proof-side polynomial contains no runtime input field values. -/
noncomputable def timePolynomial (rows : List (Spec q width)) : Polynomial Nat :=
  (rows.map (fun row => MachineAddressEdge.timePolynomial
    row.left.length row.right.length width)).sum + 1

theorem rowCosts_sum_le (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width)) (base : K → List Bool)
    (B C : Nat) (values : Spec q width → Values width) (M : Nat)
    (clean : MachineAddressEdge.Clean slots base)
    (fieldsBound : ∀ j, (base (MachineAddressEdge.addressSlots slots (.field j))).length ≤ M)
    (radixBound : B ≤ M) (capacityBound : C ≤ M)
    (valuesBound : ∀ row ∈ rows,
      (encodeWords (values row).left).length ≤ M ∧
      (encodeWords (values row).right).length ≤ M ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).left i ≤ M) ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).right i ≤ M)) :
    (rowCosts slots B C values rows base).sum ≤
      ((rows.map (fun row => MachineAddressEdge.timePolynomial
        row.left.length row.right.length width)).sum).eval M := by
  induction rows generalizing base with
  | nil => simp [rowCosts]
  | cons row rows ih =>
    have bounds := valuesBound row (by simp)
    have first := MachineAddressEdge.phaseSteps_le_timePolynomial row.left row.right
      slots base B C (values row).left (values row).right
      (values row).left_length (values row).right_length clean M fieldsBound
      bounds.1 bounds.2.1 radixBound capacityBound bounds.2.2.1 bounds.2.2.2
    have rest := ih (rowResult slots B C values row base)
      (MachineAddressEdge.Clean.appended slots base clean (payload B C values row))
      (by simpa only [rowResult, MachineAddressEdge.appended_address] using fieldsBound)
      (fun r hr => valuesBound r (List.mem_cons_of_mem row hr))
    simpa only [rowCosts, List.sum_cons, List.map_cons, Polynomial.eval_add, rowCost] using
      Nat.add_le_add first rest

/-- The actual dispatcher-and-rows count is bounded by a fixed polynomial in
explicit tape and digit magnitudes, using the checked edge arithmetic bound. -/
theorem phaseCost_le_timePolynomial (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width)) (base : K → List Bool)
    (B C : Nat) (values : Spec q width → Values width) (M : Nat)
    (clean : MachineAddressEdge.Clean slots base)
    (fieldsBound : ∀ j, (base (MachineAddressEdge.addressSlots slots (.field j))).length ≤ M)
    (radixBound : B ≤ M) (capacityBound : C ≤ M)
    (valuesBound : ∀ row ∈ rows,
      (encodeWords (values row).left).length ≤ M ∧
      (encodeWords (values row).right).length ≤ M ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).left i ≤ M) ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).right i ≤ M)) :
    (rowCosts slots B C values rows base).sum + 1 ≤ (timePolynomial rows).eval M := by
  have h := rowCosts_sum_le slots rows base B C values M clean fieldsBound
    radixBound capacityBound valuesBound
  simpa only [timePolynomial, Polynomial.eval_add, Polynomial.eval_one] using
    Nat.add_le_add_right h 1

end MaxCutGames.Reduction.MachineOutcomeRows

end OAI
