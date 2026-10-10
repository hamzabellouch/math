import Mathlib.Tactic.DeriveFintype
import OAI.Computability.UniqueGames.Machines.MachineLemmas
import OAI.Computability.UniqueGames.Machines.MachineTransducerCopy
import OAI.Computability.UniqueGames.PCP.SourceMachine
import OAI.Computability.UniqueGames.Reduction.CanonicalBodyTemplateLemmas
import OAI.Computability.UniqueGames.Reduction.MachineTransducer

namespace OAI

section

/-!
The literal four-word row used by the hundred-clone finite machine. The
natural-number triple is a fixed program parameter; its bounds and distinctness
are needed only when identifying the output with the typed parity instance.
-/

namespace UniqueGamesTheorem.Explicit.MachineClone100Table

open UniqueGamesTheorem.Reduction

def cloneEquationWords {n : Nat} (e : CloneGap.Equation (Fin n))
    (t : Nat × Nat × Nat) : List Nat :=
  [t.1 + 100 * e.first.val, t.2.1 + 100 * e.second.val,
    t.2.2 + 100 * e.third.val, if e.rhs then 1 else 0]

end UniqueGamesTheorem.Explicit.MachineClone100Table

end

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Model

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad

inductive Tape
  | input | header | counter | field (slot : Fin 4) | scratch | reversed | output
  deriving DecidableEq, Fintype

abbrev Context (D : Nat) := Fin 2 ⊕ (Fin D × Fin 4)
abbrev State (D : Nat) := (Unit × Context D) × Option Bool
abbrev Alphabet (_ : Tape) := Bool

inductive Label (D : Nat)
  | headerStart (slot : Fin 2)
  | headerLoop (slot : Fin 2)
  | setup (context : Context D)
  | scan (context : Context D)
  | emit (context control : Context D) (symbol : Bool)
  | restore (context : Context D)
  | clearHeader
  | guard
  | fieldStart (slot : Fin 4)
  | fieldLoop (slot : Fin 4)
  | cleanup (slot : Fin 4)
  | finalCounter
  | finalReverse
  deriving DecidableEq, Fintype

def defaultControl (D : Nat) : Context D := .inl 0
def initialState (D : Nat) : State D := (((), defaultControl D), none)

def headerTape (j : Fin 2) : Tape := if j.val = 0 then .header else .counter

def contextSource {D : Nat} : Context D → Tape
  | .inl j => headerTape j
  | .inr p => .field p.2

def contextScale {D : Nat} : Context D → Nat
  | .inl j => if j.val = 0 then 100 else D
  | .inr p => if p.2.val < 3 then 100 else 1

def tripleField (t : Nat × Nat × Nat) (j : Fin 4) : Nat :=
  match j.val with
  | 0 => t.1
  | 1 => t.2.1
  | 2 => t.2.2
  | _ => 0

def contextOffset (triples : List (Nat × Nat × Nat)) : Context triples.length → Nat
  | .inl _ => 0
  | .inr p => tripleField (triples.get p.1) p.2

def affineEmit (scale offset : Nat) : Bool → List Bool
  | true => List.replicate scale true
  | false => encodeWord offset

def emission (triples : List (Nat × Nat × Nat)) (c : Context triples.length) :
    Bool → List Bool := affineEmit (contextScale c) (contextOffset triples c)

def contextNext {D : Nat} : Context D → Option (Label D)
  | .inl j => if j.val = 0 then some (.setup (.inl 1)) else some .clearHeader
  | .inr (i, j) =>
      if hj : j.val + 1 < 4 then some (.setup (.inr (i, ⟨j.val + 1, hj⟩)))
      else if hi : i.val + 1 < D then some (.setup (.inr (⟨i.val + 1, hi⟩, 0)))
      else some (.cleanup 0)

def cleanupNext {D : Nat} (j : Fin 4) : Label D :=
  if hj : j.val + 1 < 4 then .cleanup ⟨j.val + 1, hj⟩ else .guard

def drain {D : Nat} (tape : Tape) (again next : Label D) :
    TM2.Stmt Alphabet (Label D) (State D) :=
  .pop tape (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.goto fun _ => again)
      (.load (fun state => (state.1, none)) (.goto fun _ => next)))

def program (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ []) :
    Label triples.length → TM2.Stmt Alphabet (Label triples.length) (State triples.length)
  | .headerStart j => SourceMachine.fieldStart (headerTape j) (.headerLoop j)
  | .headerLoop j => SourceMachine.fieldLoop .input (headerTape j) (.headerLoop j)
      (if j.val = 0 then some (.headerStart 1) else some (.setup (.inl 0)))
  | .setup c => .load (fun _ => (((), c), none)) (.goto fun _ => .scan c)
  | .scan c => MachineTransducerCopy.scanLoop (contextSource c) .scratch
      (defaultControl _) (fun q b => .emit c q b) (.restore c)
  | .emit c q b => MachineTransducerCopy.emitter .reversed (fun q _ => q)
      (emission triples) (.scan c) q b
  | .restore c => MachineTransfer.loopAt .scratch (contextSource c) id false
      (.restore c) (contextNext c)
  | .clearHeader => drain .header .clearHeader .guard
  | .guard => MachineUnaryCounter.guard .counter (.fieldStart 0) .finalCounter
  | .fieldStart j => SourceMachine.fieldStart (.field j) (.fieldLoop j)
  | .fieldLoop j => SourceMachine.fieldLoop .input (.field j) (.fieldLoop j)
      (SourceMachine.fieldNext Label.fieldStart
        (some (.setup (.inr (⟨0, List.length_pos_iff.mpr nonempty⟩, 0)))) j)
  | .cleanup j => drain (.field j) (.cleanup j) (cleanupNext j)
  | .finalCounter => .pop .counter (fun state _ => (state.1, none))
      (.goto fun _ => .finalReverse)
  | .finalReverse => MachineTransfer.loopAt .reversed .output id false .finalReverse none

def machine (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ []) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label triples.length
  main := .headerStart 0
  σ := State triples.length
  initialState := initialState _
  m := program triples nonempty

end UniqueGamesTheorem.Explicit.MachineClone100Model

end

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Affine

open UniqueGamesTheorem.Reduction

open UniqueGamesTheorem.Foundations.Complexity
open MachineClone100Model

/-- Identity control transitions reduce exactly to fixed symbol substitution. -/
theorem output_eq_flatMap {Q : Type} [Fintype Q]
    (emit : Q → Bool → List Bool) (q : Q) (input : List Bool) :
    MachineTransducer.output (fun state _ => state) emit q input =
      input.flatMap (emit q) := by
  induction input with
  | nil => rfl
  | cons b input ih =>
    simp only [MachineTransducer.output, List.flatMap_cons, ih]

theorem output_append {Q : Type} [Fintype Q]
    (emit : Q → Bool → List Bool) (q : Q) (first rest : List Bool) :
    MachineTransducer.output (fun state _ => state) emit q (first ++ rest) =
      MachineTransducer.output (fun state _ => state) emit q first ++
        MachineTransducer.output (fun state _ => state) emit q rest := by
  simp only [output_eq_flatMap, List.flatMap_append]

theorem affineEmit_replicate_true (scale offset v : Nat) :
    (List.replicate v true).flatMap (affineEmit scale offset) =
      List.replicate (scale * v) true := by
  rw [List.flatMap_replicate]
  change (List.replicate v (List.replicate scale true)).flatten = _
  rw [List.flatten_replicate_replicate, Nat.mul_comm v scale]

/-- This includes zero scale and zero offset, with no positivity assumptions. -/
theorem affineEmit_word (scale offset v : Nat) :
    (encodeWord v).flatMap (affineEmit scale offset) =
      encodeWord (offset + scale * v) := by
  simp only [encodeWord, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, affineEmit_replicate_true, affineEmit]
  rw [← List.append_assoc, List.replicate_append_replicate, Nat.add_comm (scale * v) offset]

theorem affineEmit_word_append (scale offset v : Nat) (rest : List Bool) :
    (encodeWord v ++ rest).flatMap (affineEmit scale offset) =
      encodeWord (offset + scale * v) ++ rest.flatMap (affineEmit scale offset) := by
  rw [List.flatMap_append, affineEmit_word]

theorem affineEmit_words (scale offset : Nat) (vs : List Nat) :
    (encodeWords vs).flatMap (affineEmit scale offset) =
      encodeWords (vs.map (fun v => offset + scale * v)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [encodeWords, List.flatMap_append, List.map_cons, affineEmit_word, ih]

/-- Exact symbolic context transform used by the shared clone-table machine. -/
theorem output_word (triples : List (Nat × Nat × Nat))
    (c : Context triples.length) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) c (encodeWord v) =
      encodeWord (contextOffset triples c + contextScale c * v) := by
  rw [output_eq_flatMap]
  exact affineEmit_word (contextScale c) (contextOffset triples c) v

theorem output_word_append (triples : List (Nat × Nat × Nat))
    (c : Context triples.length) (v : Nat) (rest : List Bool) :
    MachineTransducer.output (fun q _ => q) (emission triples) c (encodeWord v ++ rest) =
      encodeWord (contextOffset triples c + contextScale c * v) ++
        MachineTransducer.output (fun q _ => q) (emission triples) c rest := by
  rw [output_append, output_word]

theorem output_words (triples : List (Nat × Nat × Nat))
    (c : Context triples.length) (vs : List Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) c (encodeWords vs) =
      encodeWords (vs.map (fun v => contextOffset triples c + contextScale c * v)) := by
  rw [output_eq_flatMap]
  exact affineEmit_words (contextScale c) (contextOffset triples c) vs

theorem output_header_variables (triples : List (Nat × Nat × Nat)) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inl 0) (encodeWord v) =
      encodeWord (100 * v) := by
  simpa [contextOffset, contextScale] using output_word triples (.inl 0) v

/-- The equation-count multiplier remains the arbitrary symbolic table length. -/
theorem output_header_count (triples : List (Nat × Nat × Nat)) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inl 1) (encodeWord v) =
      encodeWord (triples.length * v) := by
  simpa [contextOffset, contextScale] using output_word triples (.inl 1) v

theorem output_field (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (j : Fin 4) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inr (i, j)) (encodeWord v) =
      encodeWord (tripleField (triples.get i) j + (if j.val < 3 then 100 else 1) * v) := by
  exact output_word triples (.inr (i, j)) v

theorem output_first_field (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inr (i, 0)) (encodeWord v) =
      encodeWord ((triples.get i).1 + 100 * v) := by
  simpa [tripleField] using output_field triples i 0 v

theorem output_second_field (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inr (i, 1)) (encodeWord v) =
      encodeWord ((triples.get i).2.1 + 100 * v) := by
  simpa [tripleField] using output_field triples i 1 v

theorem output_third_field (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inr (i, 2)) (encodeWord v) =
      encodeWord ((triples.get i).2.2 + 100 * v) := by
  simpa [tripleField] using output_field triples i 2 v

/-- RHS words are copied exactly, including both legal Boolean values. -/
theorem output_rhs_field (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inr (i, 3)) (encodeWord v) =
      encodeWord v := by
  simpa [tripleField] using output_field triples i 3 v

end UniqueGamesTheorem.Explicit.MachineClone100Affine

end

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Cleanup

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineClone100Model

variable {D : Nat}

/-- The finite drain statement pops one symbol and retains the ambient control. -/
theorem drainStep_cons (tape : Tape) (again next : Label D)
    (program : Label D → TM2.Stmt Alphabet (Label D) (State D))
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (bit : Bool) (input : List Bool)
    (control : Unit × Context D) (register : Option Bool) :
    TM2.step program
      ⟨some again, (control, register), Function.update base tape (bit :: input)⟩ =
      some ⟨some again, (control, some bit), Function.update base tape input⟩ := by
  change some (TM2.stepAux (program again) (control, register)
    (Function.update base tape (bit :: input))) = _
  rw [atAgain]
  simp [drain, TM2.stepAux]

/-- The exit transition observes the empty tape and resets the optional bit. -/
theorem drainStep_nil (tape : Tape) (again next : Label D)
    (program : Label D → TM2.Stmt Alphabet (Label D) (State D))
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (control : Unit × Context D) (register : Option Bool) :
    TM2.step program
      ⟨some again, (control, register), Function.update base tape []⟩ =
      some ⟨some next, (control, none), Function.update base tape []⟩ := by
  change some (TM2.stepAux (program again) (control, register)
    (Function.update base tape [])) = _
  rw [atAgain]
  simp [drain, TM2.stepAux]

/-- Direct list induction gives exactly one transition per symbol plus the
empty-tape exit; no whole execution trace is assumed. -/
theorem drainTrace (tape : Tape) (again next : Label D)
    (program : Label D → TM2.Stmt Alphabet (Label D) (State D))
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (input : List Bool)
    (control : Unit × Context D) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[input.length + 1]
      (some ⟨some again, (control, register), Function.update base tape input⟩) =
      some ⟨some next, (control, none), Function.update base tape []⟩ := by
  induction input generalizing register with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some] using
      drainStep_nil tape again next program atAgain base control register
  | cons bit input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[input.length + 1]
      (TM2.step program ⟨some again, (control, register),
        Function.update base tape (bit :: input)⟩) = _
    rw [drainStep_cons tape again next program atAgain, ih]

/-- Caller form: the selected tape's initial contents are read from the frame. -/
theorem drainTrace_base (tape : Tape) (again next : Label D)
    (program : Label D → TM2.Stmt Alphabet (Label D) (State D))
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (control : Unit × Context D) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[(base tape).length + 1]
      (some ⟨some again, (control, register), base⟩) =
      some ⟨some next, (control, none), Function.update base tape []⟩ := by
  simpa only [Function.update_eq_self] using
    drainTrace tape again next program atAgain base (base tape) control register

def drainInTime (tape : Tape) (again next : Label D)
    (program : Label D → TM2.Stmt Alphabet (Label D) (State D))
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (control : Unit × Context D) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (control, register), base⟩
      (some ⟨some next, (control, none), Function.update base tape []⟩)
      ((base tape).length + 1) where
  steps := (base tape).length + 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[_] _ = _
    exact drainTrace_base tape again next program atAgain base control register
  steps_le_m := Nat.le_refl _

theorem clearHeaderTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (control : Unit × Context triples.length)
    (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[(base .header).length + 1]
      (some ⟨some .clearHeader, (control, register), base⟩) =
      some ⟨some .guard, (control, none), Function.update base .header []⟩ :=
  drainTrace_base .header .clearHeader .guard (program triples nonempty) rfl base control register

def clearHeaderInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (control : Unit × Context triples.length)
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some .clearHeader, (control, register), base⟩
      (some ⟨some .guard, (control, none), Function.update base .header []⟩)
      ((base .header).length + 1) :=
  drainInTime .header .clearHeader .guard (program triples nonempty) rfl base control register

/-- The four explicit updates made by the successive cleanup labels. -/
def clearFields (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (.field 0) []) (.field 1) []) (.field 2) []) (.field 3) []

@[simp] theorem clearFields_field (base : Tape → List Bool) (j : Fin 4) :
    clearFields base (.field j) = [] := by
  fin_cases j <;> simp [clearFields]

theorem clearFields_other (base : Tape → List Bool) (tape : Tape)
    (other : ∀ j, tape ≠ .field j) : clearFields base tape = base tape := by
  simp [clearFields, other]

@[simp] theorem clearFields_input (base : Tape → List Bool) :
    clearFields base .input = base .input := by simp [clearFields]
@[simp] theorem clearFields_header (base : Tape → List Bool) :
    clearFields base .header = base .header := by simp [clearFields]
@[simp] theorem clearFields_counter (base : Tape → List Bool) :
    clearFields base .counter = base .counter := by simp [clearFields]
@[simp] theorem clearFields_scratch (base : Tape → List Bool) :
    clearFields base .scratch = base .scratch := by simp [clearFields]
@[simp] theorem clearFields_reversed (base : Tape → List Bool) :
    clearFields base .reversed = base .reversed := by simp [clearFields]
@[simp] theorem clearFields_output (base : Tape → List Bool) :
    clearFields base .output = base .output := by simp [clearFields]

theorem clearFields_eq_self (base : Tape → List Bool)
    (empty : ∀ j, base (.field j) = []) : clearFields base = base := by
  funext tape
  cases tape <;> simp [empty]

@[simp] theorem clearFields_idempotent (base : Tape → List Bool) :
    clearFields (clearFields base) = clearFields base :=
  clearFields_eq_self (clearFields base) (clearFields_field base)

def cleanupSteps (base : Tape → List Bool) : Nat :=
  (base (.field 0)).length + (base (.field 1)).length +
    (base (.field 2)).length + (base (.field 3)).length + 4

theorem cleanupTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (slot : Fin 4) (base : Tape → List Bool)
    (control : Unit × Context triples.length) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[
      (base (.field slot)).length + 1]
      (some ⟨some (.cleanup slot), (control, register), base⟩) =
      some ⟨some (cleanupNext slot), (control, none), Function.update base (.field slot) []⟩ :=
  drainTrace_base (.field slot) (.cleanup slot) (cleanupNext slot)
    (program triples nonempty) rfl base control register

/-- All four field stacks are consumed by the actual cleanup program. -/
theorem cleanupFourTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (control : Unit × Context triples.length)
    (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[cleanupSteps base]
      (some ⟨some (.cleanup 0), (control, register), base⟩) =
      some ⟨some .guard, (control, none), clearFields base⟩ := by
  let t₀ := Function.update base (.field 0) []
  let t₁ := Function.update t₀ (.field 1) []
  let t₂ := Function.update t₁ (.field 2) []
  have h₀ := cleanupTrace triples nonempty 0 base control register
  have h₁ := cleanupTrace triples nonempty 1 t₀ control none
  have h₂ := cleanupTrace triples nonempty 2 t₁ control none
  have h₃ := cleanupTrace triples nonempty 3 t₂ control none
  have hn₀ : cleanupNext (D := triples.length) 0 = .cleanup 1 := by simp [cleanupNext]
  have hn₁ : cleanupNext (D := triples.length) 1 = .cleanup 2 := by simp [cleanupNext]
  have hn₂ : cleanupNext (D := triples.length) 2 = .cleanup 3 := by simp [cleanupNext]
  have hn₃ : cleanupNext (D := triples.length) 3 = .guard := by simp [cleanupNext]
  rw [hn₀] at h₀
  rw [hn₁] at h₁
  rw [hn₂] at h₂
  rw [hn₃] at h₃
  have ht₁ : t₀ (.field 1) = base (.field 1) := by simp [t₀]
  have ht₂ : t₁ (.field 2) = base (.field 2) := by simp [t₁, t₀]
  have ht₃ : t₂ (.field 3) = base (.field 3) := by simp [t₂, t₁, t₀]
  rw [ht₁] at h₁
  rw [ht₂] at h₂
  rw [ht₃] at h₃
  have time : cleanupSteps base =
      ((base (.field 3)).length + 1) +
      (((base (.field 2)).length + 1) +
      (((base (.field 1)).length + 1) + ((base (.field 0)).length + 1))) := by
    unfold cleanupSteps
    omega
  rw [time, Function.iterate_add_apply]
  rw [Function.iterate_add_apply (m := (base (.field 2)).length + 1)]
  rw [Function.iterate_add_apply (m := (base (.field 1)).length + 1)]
  rw [h₀, h₁, h₂, h₃]
  rfl

def cleanupFourInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (control : Unit × Context triples.length)
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some (.cleanup 0), (control, register), base⟩
      (some ⟨some .guard, (control, none), clearFields base⟩)
      (cleanupSteps base) where
  steps := cleanupSteps base
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step (program triples nonempty)))^[_] _ = _
    exact cleanupFourTrace triples nonempty base control register
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Explicit.MachineClone100Cleanup

end

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Context

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineClone100Model

theorem contextSource_ne_scratch {D : Nat} (context : Context D) :
    contextSource context ≠ Tape.scratch := by
  cases context with
  | inl slot =>
    simp only [contextSource, headerTape]
    split <;> simp
  | inr pair => simp [contextSource]

theorem contextSource_ne_reversed {D : Nat} (context : Context D) :
    contextSource context ≠ Tape.reversed := by
  cases context with
  | inl slot =>
    simp only [contextSource, headerTape]
    split <;> simp
  | inr pair => simp [contextSource]

def contextTapes (triples : List (Nat × Nat × Nat)) (context : Context triples.length)
    (base : Tape → List Bool) : Tape → List Bool :=
  Function.update base .reversed
    ((MachineTransducer.output (fun control _ => control) (emission triples)
      context (base (contextSource context))).reverse ++ base .reversed)

@[simp] theorem contextTapes_reversed (triples : List (Nat × Nat × Nat))
    (context : Context triples.length) (base : Tape → List Bool) :
    contextTapes triples context base .reversed =
      (MachineTransducer.output (fun control _ => control) (emission triples)
        context (base (contextSource context))).reverse ++ base .reversed := by
  simp [contextTapes]

theorem contextTapes_other (triples : List (Nat × Nat × Nat))
    (context : Context triples.length) (base : Tape → List Bool) (tape : Tape)
    (different : tape ≠ .reversed) :
    contextTapes triples context base tape = base tape := by
  simp [contextTapes, different]

@[simp] theorem contextTapes_source (triples : List (Nat × Nat × Nat))
    (context : Context triples.length) (base : Tape → List Bool) :
    contextTapes triples context base (contextSource context) = base (contextSource context) :=
  contextTapes_other triples context base _ (contextSource_ne_reversed context)

@[simp] theorem contextTapes_scratch (triples : List (Nat × Nat × Nat))
    (context : Context triples.length) (base : Tape → List Bool) :
    contextTapes triples context base .scratch = base .scratch :=
  contextTapes_other triples context base _ (by decide)

/-- Setup discards arbitrary old control and register values before scanning. -/
theorem setupStep (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (context : Context triples.length) (base : Tape → List Bool)
    (state : State triples.length) :
    TM2.step (program triples nonempty) ⟨some (.setup context), state, base⟩ =
      some ⟨some (.scan context), (((), context), none), base⟩ := rfl

theorem contextTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (context : Context triples.length) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State triples.length) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[
        3 * (base (contextSource context)).length + 3]
      (some ⟨some (.setup context), state, base⟩) =
      some ⟨contextNext context, initialState _, contextTapes triples context base⟩ := by
  have copied := MachineTransducerCopy.transduceCopyTrace
    (contextSource context) Tape.scratch Tape.reversed
    (contextSource_ne_scratch context) (contextSource_ne_reversed context) (by decide)
    (defaultControl triples.length) (fun control _ => control) (emission triples)
    (.scan context) (.restore context) (fun control symbol => .emit context control symbol)
    (contextNext context) (program triples nonempty)
    rfl (by intros; rfl) rfl base scratchEmpty () context none
  rw [show 3 * (base (contextSource context)).length + 3 =
      (3 * (base (contextSource context)).length + 2) + 1 by omega,
    Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step (program triples nonempty)))^[
    3 * (base (contextSource context)).length + 2]
    (TM2.step (program triples nonempty) ⟨some (.setup context), state, base⟩) = _
  rw [setupStep]
  exact copied

/-- The exact trace packaged for composition with neighboring cloning stages. -/
def contextInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (context : Context triples.length) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State triples.length) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some (.setup context), state, base⟩
      (some ⟨contextNext context, initialState _, contextTapes triples context base⟩)
      (3 * (base (contextSource context)).length + 3) where
  steps := 3 * (base (contextSource context)).length + 3
  evals_in_steps := contextTrace triples nonempty context base scratchEmpty state
  steps_le_m := Nat.le_refl _

@[simp] theorem contextInTime_steps (triples : List (Nat × Nat × Nat))
    (nonempty : triples ≠ []) (context : Context triples.length) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State triples.length) :
    (contextInTime triples nonempty context base scratchEmpty state).steps =
      3 * (base (contextSource context)).length + 3 := rfl

end UniqueGamesTheorem.Explicit.MachineClone100Context

end

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Finish

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineClone100Model

def finishTapes (base : Tape → List Bool) : Tape → List Bool :=
  MachineTransfer.tapesAt .reversed .output (Function.update base .counter []) []
    ((base .reversed).reverse ++ base .output)

@[simp] theorem finishTapes_counter (base : Tape → List Bool) :
    finishTapes base .counter = [] := by simp [finishTapes, MachineTransfer.tapesAt]

@[simp] theorem finishTapes_reversed (base : Tape → List Bool) :
    finishTapes base .reversed = [] := by simp [finishTapes, MachineTransfer.tapesAt]

@[simp] theorem finishTapes_output (base : Tape → List Bool) :
    finishTapes base .output = (base .reversed).reverse ++ base .output := by
  simp [finishTapes, MachineTransfer.tapesAt]

theorem finishTapes_other (base : Tape → List Bool) (tape : Tape)
    (hc : tape ≠ .counter) (hr : tape ≠ .reversed) (ho : tape ≠ .output) :
    finishTapes base tape = base tape := by
  simp [finishTapes, MachineTransfer.tapesAt, hc, hr, ho]

theorem counterStep (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (hcounter : base .counter = [false]) :
    TM2.step (program triples hne)
      ⟨some .finalCounter, initialState _, base⟩ =
        some ⟨some .finalReverse, initialState _, Function.update base .counter []⟩ := by
  simp [TM2.step, TM2.stepAux, program, initialState, hcounter]

theorem finishTrace (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (hcounter : base .counter = [false]) :
    (MachineComposition.advance (TM2.step (program triples hne)))^[(base .reversed).length + 2]
      (some ⟨some .finalCounter, initialState _, base⟩) =
        some ⟨none, initialState _, finishTapes base⟩ := by
  have first := counterStep triples hne base hcounter
  have rest := MachineTransfer.transferAt_fromTapes Tape.reversed Tape.output
    (by decide) id false (Label.finalReverse : Label triples.length) none
    (program triples hne) rfl (Function.update base Tape.counter [])
    ((), defaultControl triples.length) none
  change (MachineComposition.advance (TM2.step (program triples hne)))^[
      ((Function.update base Tape.counter []) Tape.reversed).length + 1]
    (some ⟨some .finalReverse, initialState _, Function.update base .counter []⟩) = _ at rest
  have rest' :
      (MachineComposition.advance (TM2.step (program triples hne)))^[(base .reversed).length + 1]
        (some ⟨some .finalReverse, initialState _, Function.update base .counter []⟩) =
          some ⟨none, initialState _, finishTapes base⟩ := by
    simpa only [finishTapes, initialState,
      Function.update_of_ne (by decide : Tape.reversed ≠ Tape.counter),
      Function.update_of_ne (by decide : Tape.output ≠ Tape.counter), List.map_id] using rest
  rw [show (base .reversed).length + 2 = ((base .reversed).length + 1) + 1 by omega,
    Function.iterate_succ_apply, MachineComposition.advance_some, first]
  exact rest'

def finishInTime (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (hcounter : base .counter = [false]) :
    StateTransition.EvalsToInTime (TM2.step (program triples hne))
      ⟨some .finalCounter, initialState _, base⟩
      (some ⟨none, initialState _, finishTapes base⟩) ((base .reversed).length + 2) where
  steps := (base .reversed).length + 2
  evals_in_steps := finishTrace triples hne base hcounter
  steps_le_m := Nat.le_refl _

theorem finish_eq_haltList (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool)
    (emptyOther : ∀ tape, tape ≠ .counter → tape ≠ .reversed → base tape = []) :
    (⟨none, initialState _, finishTapes base⟩ : (machine triples hne).Cfg) =
      haltList (machine triples hne) ((base .reversed).reverse) := by
  have hout := emptyOther .output (by decide) (by decide)
  have ht : finishTapes base =
      (haltList (machine triples hne) ((base .reversed).reverse)).stk := by
    funext tape
    cases tape <;> simp [finishTapes, MachineTransfer.tapesAt, haltList, machine, hout,
      emptyOther]
    rfl
  exact congrArg
    (fun tapes => (⟨none, initialState triples.length, tapes⟩ : (machine triples hne).Cfg)) ht

end UniqueGamesTheorem.Explicit.MachineClone100Finish

end

end OAI
