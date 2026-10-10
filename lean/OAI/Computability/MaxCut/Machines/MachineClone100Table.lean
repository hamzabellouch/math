import Mathlib
import OAI.Computability.MaxCut.Machines.MachineSequential
import OAI.Computability.MaxCut.Encoding.ThreeBitTest
import OAI.Computability.MaxCut.PCP.Folding

namespace OAI

/-!
The literal four-word row used by the hundred-clone finite machine. The
natural-number triple is a fixed program parameter; its bounds and distinctness
are needed only when identifying the output with the typed parity instance.
-/

namespace MaxCutGames.Explicit.MachineClone100Table

open MaxCutGames.Reduction

def cloneEquationWords {n : Nat} (e : CloneGap.Equation (Fin n))
    (t : Nat × Nat × Nat) : List Nat :=
  [t.1 + 100 * e.first.val, t.2.1 + 100 * e.second.val,
    t.2.2 + 100 * e.third.val, if e.rhs then 1 else 0]

end MaxCutGames.Explicit.MachineClone100Table

namespace MaxCutGames.Explicit.MachineClone100Model

open MaxCutGames.Reduction

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad

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

end MaxCutGames.Explicit.MachineClone100Model

namespace MaxCutGames.Explicit.MachineClone100Context

open MaxCutGames.Reduction

open Turing
open MaxCutGames.Foundations.Complexity
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

end MaxCutGames.Explicit.MachineClone100Context

namespace MaxCutGames.Explicit.MachineClone100Affine

open MaxCutGames.Reduction

open MaxCutGames.Foundations.Complexity
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

end MaxCutGames.Explicit.MachineClone100Affine

namespace MaxCutGames.Explicit.MachineClone100Cleanup

open MaxCutGames.Reduction

open Turing
open MaxCutGames.Foundations.Complexity
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

end MaxCutGames.Explicit.MachineClone100Cleanup

namespace MaxCutGames.Explicit.MachineClone100Headers

open MaxCutGames.Reduction

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MachineClone100Model

def parsedTapes (base : Tape → List Bool) (n m : Nat) (suffix : List Bool) :
    Tape → List Bool
  | .input => suffix
  | .header => encodeWord n
  | .counter => encodeWord m
  | tape => base tape

/-- Exact header-stage endpoint. The occurrence counter is retained for the
body loop; generated output is accumulated in reverse. -/
def resultTapes (triples : List (Nat × Nat × Nat)) (base : Tape → List Bool)
    (n m : Nat) (suffix : List Bool) : Tape → List Bool
  | .input => suffix
  | .header => []
  | .counter => encodeWord m
  | .reversed => (encodeWords [100 * n, triples.length * m]).reverse
  | tape => base tape

@[simp] theorem resultTapes_input (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .input = suffix := rfl
@[simp] theorem resultTapes_header (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .header = [] := rfl
@[simp] theorem resultTapes_counter (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .counter = encodeWord m := rfl
@[simp] theorem resultTapes_reversed (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .reversed =
      (encodeWords [100 * n, triples.length * m]).reverse := rfl
@[simp] theorem resultTapes_scratch (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .scratch = base .scratch := rfl
@[simp] theorem resultTapes_field (triples) (base) (n m) (suffix) (j : Fin 4) :
    resultTapes triples base n m suffix (.field j) = base (.field j) := rfl
@[simp] theorem resultTapes_output (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .output = base .output := rfl

private theorem twoFieldsTapes_inline_MachineClone100Headers (base : Tape → List Bool) (n m : Nat) (suffix : List Bool)
    (hheader : base .header = []) (hcounter : base .counter = []) :
    SourceMachine.afterField .input .counter
      (SourceMachine.afterField .input .header base n (encodeWord m ++ suffix)) m suffix =
      parsedTapes base n m suffix := by
  funext tape
  cases tape <;>
    simp [SourceMachine.afterField, SourceMachine.fieldTapes, parsedTapes, hheader, hcounter]

private theorem firstContextTapes_inline_MachineClone100Headers (triples : List (Nat × Nat × Nat))
    (base : Tape → List Bool) (n m : Nat) (suffix : List Bool)
    (hreversed : base .reversed = []) :
    MachineClone100Context.contextTapes triples (.inl 0) (parsedTapes base n m suffix) =
      Function.update (parsedTapes base n m suffix) .reversed (encodeWord (100 * n)).reverse := by
  simp [MachineClone100Context.contextTapes, contextSource, headerTape, parsedTapes,
    MachineClone100Affine.output_word, contextOffset, contextScale, hreversed]

private theorem secondContextTapes_inline_MachineClone100Headers (triples : List (Nat × Nat × Nat))
    (base : Tape → List Bool) (n m : Nat) (suffix : List Bool) :
    MachineClone100Context.contextTapes triples (.inl 1)
      (Function.update (parsedTapes base n m suffix) .reversed (encodeWord (100 * n)).reverse) =
      Function.update (parsedTapes base n m suffix) .reversed
        (encodeWords [100 * n, triples.length * m]).reverse := by
  simp [MachineClone100Context.contextTapes, contextSource, headerTape, parsedTapes,
    MachineClone100Affine.output_word, contextOffset, contextScale,
    encodeWords, List.reverse_append]

private theorem clearHeaderTapes_inline_MachineClone100Headers (triples : List (Nat × Nat × Nat))
    (base : Tape → List Bool) (n m : Nat) (suffix : List Bool) :
    Function.update
      (Function.update (parsedTapes base n m suffix) .reversed
        (encodeWords [100 * n, triples.length * m]).reverse) .header [] =
      resultTapes triples base n m suffix := by
  funext tape
  cases tape <;> simp [parsedTapes, resultTapes]

theorem headersTrace (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (n m : Nat) (suffix : List Bool)
    (hinput : base .input = encodeWords [n, m] ++ suffix)
    (hheader : base .header = []) (hcounter : base .counter = [])
    (hscratch : base .scratch = []) (hreversed : base .reversed = []) :
    (MachineComposition.advance (TM2.step (program triples hne)))^[5 * n + 4 * m + 18]
      (some ⟨some (.headerStart 0), initialState triples.length, base⟩) =
      some ⟨some .guard, initialState triples.length,
        resultTapes triples base n m suffix⟩ := by
  let t₀ := SourceMachine.afterField .input .header base n (encodeWord m ++ suffix)
  let t₁ := parsedTapes base n m suffix
  let t₂ := Function.update t₁ .reversed (encodeWord (100 * n)).reverse
  let t₃ := Function.update t₁ .reversed (encodeWords [100 * n, triples.length * m]).reverse
  have h₀ : base .input = encodeWord n ++ (encodeWord m ++ suffix) := by
    simpa only [encodeWords, List.append_nil, List.append_assoc] using hinput
  have p₀ := (SourceMachine.fieldInTime .input .header (by decide)
    (.headerStart 0) (.headerLoop 0) (some (.headerStart 1))
    (program triples hne) rfl rfl base n (encodeWord m ++ suffix) h₀
    ((), defaultControl triples.length) none).evals_in_steps
  change (MachineComposition.advance (TM2.step (program triples hne)))^[n + 2]
    (some ⟨some (.headerStart 0), initialState triples.length, base⟩) =
    some ⟨some (.headerStart 1), initialState triples.length, t₀⟩ at p₀
  have h₁ : t₀ .input = encodeWord m ++ suffix := by
    simp [t₀, SourceMachine.afterField]
  have p₁ := (SourceMachine.fieldInTime .input .counter (by decide)
    (.headerStart 1) (.headerLoop 1) (some (.setup (.inl 0)))
    (program triples hne) rfl rfl t₀ m suffix h₁
    ((), defaultControl triples.length) none).evals_in_steps
  change (MachineComposition.advance (TM2.step (program triples hne)))^[m + 2]
    (some ⟨some (.headerStart 1), initialState triples.length, t₀⟩) =
    some ⟨some (.setup (.inl 0)), initialState triples.length,
      SourceMachine.afterField .input .counter t₀ m suffix⟩ at p₁
  have ht₁ : SourceMachine.afterField .input .counter t₀ m suffix = t₁ :=
    twoFieldsTapes_inline_MachineClone100Headers base n m suffix hheader hcounter
  rw [ht₁] at p₁
  have hs₁ : t₁ .scratch = [] := by simpa [t₁, parsedTapes] using hscratch
  have p₂ := MachineClone100Context.contextTrace triples hne (.inl 0) t₁ hs₁
    (initialState triples.length)
  have ht₂ : MachineClone100Context.contextTapes triples (.inl 0) t₁ = t₂ :=
    firstContextTapes_inline_MachineClone100Headers triples base n m suffix hreversed
  rw [ht₂] at p₂
  have hlen₂ : (t₁ (contextSource (.inl 0 : Context triples.length))).length = n + 1 := by
    simp [contextSource, headerTape, t₁, parsedTapes]
  rw [hlen₂] at p₂
  change (MachineComposition.advance (TM2.step (program triples hne)))^[3 * (n + 1) + 3]
    (some ⟨some (.setup (.inl 0)), initialState triples.length, t₁⟩) =
    some ⟨some (.setup (.inl 1)), initialState triples.length, t₂⟩ at p₂
  have hs₂ : t₂ .scratch = [] := by simp [t₂, t₁, parsedTapes, hscratch]
  have p₃ := MachineClone100Context.contextTrace triples hne (.inl 1) t₂ hs₂
    (initialState triples.length)
  have ht₃ : MachineClone100Context.contextTapes triples (.inl 1) t₂ = t₃ :=
    secondContextTapes_inline_MachineClone100Headers triples base n m suffix
  rw [ht₃] at p₃
  have hlen₃ : (t₂ (contextSource (.inl 1 : Context triples.length))).length = m + 1 := by
    simp [contextSource, headerTape, t₂, t₁, parsedTapes]
  rw [hlen₃] at p₃
  change (MachineComposition.advance (TM2.step (program triples hne)))^[3 * (m + 1) + 3]
    (some ⟨some (.setup (.inl 1)), initialState triples.length, t₂⟩) =
    some ⟨some .clearHeader, initialState triples.length, t₃⟩ at p₃
  have p₄ := MachineClone100Cleanup.clearHeaderTrace triples hne t₃
    ((), defaultControl triples.length) none
  have ht₄ : Function.update t₃ .header [] = resultTapes triples base n m suffix :=
    clearHeaderTapes_inline_MachineClone100Headers triples base n m suffix
  rw [ht₄] at p₄
  have hh₃ : t₃ .header = encodeWord n := by simp [t₃, t₁, parsedTapes]
  rw [hh₃, encodeWord_length] at p₄
  change (MachineComposition.advance (TM2.step (program triples hne)))^[(n + 1) + 1]
    (some ⟨some .clearHeader, initialState triples.length, t₃⟩) =
    some ⟨some .guard, initialState triples.length, resultTapes triples base n m suffix⟩ at p₄
  rw [show 5 * n + 4 * m + 18 =
      (n + 2) + (3 * (m + 1) + 3) + (3 * (n + 1) + 3) + (m + 2) + (n + 2) by omega,
    Function.iterate_add_apply, p₀, Function.iterate_add_apply, p₁,
    Function.iterate_add_apply, p₂, Function.iterate_add_apply, p₃]
  exact p₄

/-- The exact header trace packaged in the machine execution-time interface. -/
def headersInTime (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (n m : Nat) (suffix : List Bool)
    (hinput : base .input = encodeWords [n, m] ++ suffix)
    (hheader : base .header = []) (hcounter : base .counter = [])
    (hscratch : base .scratch = []) (hreversed : base .reversed = []) :
    StateTransition.EvalsToInTime (TM2.step (program triples hne))
      ⟨some (.headerStart 0), initialState triples.length, base⟩
      (some ⟨some .guard, initialState triples.length,
        resultTapes triples base n m suffix⟩) (5 * n + 4 * m + 18) where
  steps := 5 * n + 4 * m + 18
  evals_in_steps := headersTrace triples hne base n m suffix hinput hheader hcounter hscratch hreversed
  steps_le_m := Nat.le_refl _

theorem headersTime_linear (n m : Nat) : 5 * n + 4 * m + 18 ≤ 5 * (n + m) + 18 := by omega

end MaxCutGames.Explicit.MachineClone100Headers

end OAI
