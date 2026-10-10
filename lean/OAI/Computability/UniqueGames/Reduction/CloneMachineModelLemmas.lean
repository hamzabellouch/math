import Mathlib.Tactic.DeriveFintype
import OAI.Computability.UniqueGames.Machines.MachineLemmas
import OAI.Computability.UniqueGames.Machines.MachineTransducerCopy
import OAI.Computability.UniqueGames.PCP.SourceMachine
import OAI.Computability.UniqueGames.Reduction.CloneTable
import OAI.Computability.UniqueGames.Reduction.MachineTransducer

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.CloneMachineModel

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
  | .inl j => if j.val = 0 then 48 else D
  | .inr p => if p.2.val < 3 then 48 else 1

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

end UniqueGamesTheorem.Reduction.CloneMachineModel

end

section

/-!
# Affine word emission in the actual clone-table machine

The shared machine keeps its context fixed while copying one saved word. Its
finite transducer therefore acts by a fixed symbol substitution. The lemmas
below identify that substitution with the established unary encoding of
`offset + scale * value`, including all header and equation-field contexts.
Scale, offset, and the triple-table length remain symbolic.
-/

namespace UniqueGamesTheorem.Reduction.CloneMachineAffine

open UniqueGamesTheorem.Foundations.Complexity
open CloneMachineModel

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
      encodeWord (48 * v) := by
  simpa [contextOffset, contextScale] using output_word triples (.inl 0) v

/-- The equation-count multiplier remains the arbitrary symbolic table length. -/
theorem output_header_count (triples : List (Nat × Nat × Nat)) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inl 1) (encodeWord v) =
      encodeWord (triples.length * v) := by
  simpa [contextOffset, contextScale] using output_word triples (.inl 1) v

theorem output_field (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (j : Fin 4) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inr (i, j)) (encodeWord v) =
      encodeWord (tripleField (triples.get i) j + (if j.val < 3 then 48 else 1) * v) := by
  exact output_word triples (.inr (i, j)) v

theorem output_first_field (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inr (i, 0)) (encodeWord v) =
      encodeWord ((triples.get i).1 + 48 * v) := by
  simpa [tripleField] using output_field triples i 0 v

theorem output_second_field (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inr (i, 1)) (encodeWord v) =
      encodeWord ((triples.get i).2.1 + 48 * v) := by
  simpa [tripleField] using output_field triples i 1 v

theorem output_third_field (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inr (i, 2)) (encodeWord v) =
      encodeWord ((triples.get i).2.2 + 48 * v) := by
  simpa [tripleField] using output_field triples i 2 v

/-- RHS words are copied exactly, including both legal Boolean values. -/
theorem output_rhs_field (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inr (i, 3)) (encodeWord v) =
      encodeWord v := by
  simpa [tripleField] using output_field triples i 3 v

end UniqueGamesTheorem.Reduction.CloneMachineAffine

end

end OAI
