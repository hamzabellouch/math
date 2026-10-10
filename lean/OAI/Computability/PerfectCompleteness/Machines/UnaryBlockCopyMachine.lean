import Mathlib.Data.List.OfFn
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.Reduction.MachineTransfer

namespace OAI


namespace PerfectCompleteness.UnaryBlockCopyMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool

def blockWords (values : Fin 6 → Nat) : List Nat :=
  [values 0, values 1, values 2, values 3, values 4, values 5]

def listValues (words : List Nat) (length_eq : words.length = 6) : Fin 6 → Nat :=
  fun i => words.get (Fin.cast length_eq.symm i)

theorem blockWords_listValues (words : List Nat) (length_eq : words.length = 6) :
    blockWords (listValues words length_eq) = words := by
  have h := (List.ofFn_congr length_eq words.get).symm
  rw [List.ofFn_get] at h
  change List.ofFn (listValues words length_eq) = words at h
  simp only [List.ofFn_succ, List.ofFn_zero] at h
  change blockWords (listValues words length_eq) = words at h
  exact h

section Placement

variable {K Λ A : Type} [DecidableEq K]

def nextField (labels : Fin 6 → Λ) (exit : Option Λ) (slot : Fin 6) : Option Λ :=
  if h : slot.val + 1 < 6 then some (labels ⟨slot.val + 1, h⟩) else exit

@[simp] theorem nextField_zero (labels : Fin 6 → Λ) (exit : Option Λ) :
    nextField labels exit 0 = some (labels 1) := rfl
@[simp] theorem nextField_one (labels : Fin 6 → Λ) (exit : Option Λ) :
    nextField labels exit 1 = some (labels 2) := rfl
@[simp] theorem nextField_two (labels : Fin 6 → Λ) (exit : Option Λ) :
    nextField labels exit 2 = some (labels 3) := rfl
@[simp] theorem nextField_three (labels : Fin 6 → Λ) (exit : Option Λ) :
    nextField labels exit 3 = some (labels 4) := rfl
@[simp] theorem nextField_four (labels : Fin 6 → Λ) (exit : Option Λ) :
    nextField labels exit 4 = some (labels 5) := rfl
@[simp] theorem nextField_five (labels : Fin 6 → Λ) (exit : Option Λ) :
    nextField labels exit 5 = exit := rfl

def finish (destination : K) (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => (state.1, none)) (exitAt destination exit)

def instruction (source destination : K) (again : Λ) (next rejected : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push destination (fun state => state.2.getD false)
        (.branch (fun state => state.2.getD false)
          (finish destination (some again)) (finish destination next)))
      (finish destination rejected))

private theorem update_source (source destination : K) (distinct : source ≠ destination)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) source replacement =
      tapesAt source destination base replacement output := by
  funext k
  by_cases hs : k = source
  · subst k
    simp [tapesAt, distinct]
  · by_cases hd : k = destination
    · subst k
      simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hd]

private theorem update_destination (source destination : K)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) destination replacement =
      tapesAt source destination base input replacement := by
  simp [tapesAt]

variable (source destination : K) (distinct : source ≠ destination)
variable (labels : Fin 6 → Λ) (exit rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ slot, program (labels slot) =
  instruction source destination (labels slot) (nextField labels exit slot) rejected)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem step_true (slot : Fin 6) (input output : List Bool) (register : Option Bool) :
    TM2.step program
      ⟨some (labels slot), (ambient, register),
        tapesAt source destination base (true :: input) output⟩ =
      some ⟨some (labels slot), (ambient, none),
        tapesAt source destination base input (true :: output)⟩ := by
  change some (TM2.stepAux (program (labels slot)) _ _) = _
  rw [atLabels slot]
  simp [instruction, finish, exitAt, TM2.stepAux, distinct,
    update_source, update_destination]

theorem step_false (slot : Fin 6) (input output : List Bool) (register : Option Bool) :
    TM2.step program
      ⟨some (labels slot), (ambient, register),
        tapesAt source destination base (false :: input) output⟩ =
      some ⟨nextField labels exit slot, (ambient, none),
        tapesAt source destination base input (false :: output)⟩ := by
  change some (TM2.stepAux (program (labels slot)) _ _) = _
  rw [atLabels slot]
  cases h : nextField labels exit slot <;>
    simp [instruction, finish, exitAt, TM2.stepAux, distinct,
      update_source, update_destination]

theorem step_empty (slot : Fin 6) (output : List Bool) (register : Option Bool) :
    TM2.step program
      ⟨some (labels slot), (ambient, register), tapesAt source destination base [] output⟩ =
      some ⟨rejected, (ambient, none), tapesAt source destination base [] output⟩ := by
  change some (TM2.stepAux (program (labels slot)) _ _) = _
  rw [atLabels slot]
  cases rejected <;>
    simp [instruction, finish, exitAt, TM2.stepAux, distinct, update_source]

theorem fieldTrace (slot : Fin 6) (value : Nat) (suffix output : List Bool)
    (register : Option Bool) :
    (advance (TM2.step program))^[value + 1]
      (some ⟨some (labels slot), (ambient, register),
        tapesAt source destination base (encodeWord value ++ suffix) output⟩) =
      some ⟨nextField labels exit slot, (ambient, none),
        tapesAt source destination base suffix ((encodeWord value).reverse ++ output)⟩ := by
  induction value generalizing output register with
  | zero =>
      simpa only [Nat.zero_add, Function.iterate_one, advance_some, encodeWord,
        List.replicate_zero, List.nil_append, List.reverse_singleton, List.singleton_append] using
        step_false source destination distinct labels exit rejected program atLabels base ambient
          slot suffix output register
  | succ value ih =>
      rw [Function.iterate_succ_apply]
      simp only [encodeWord, List.replicate_succ, List.cons_append, advance_some]
      rw [step_true source destination distinct labels exit rejected program atLabels]
      change (advance (TM2.step program))^[value + 1]
        (some ⟨some (labels slot), (ambient, none),
          tapesAt source destination base (encodeWord value ++ suffix) (true :: output)⟩) = _
      rw [ih]
      simp only [encodeWord, List.reverse_cons, List.append_assoc, List.singleton_append]

omit [DecidableEq K] distinct atLabels in
private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem blockTrace (values : Fin 6 → Nat) (suffix output : List Bool)
    (register : Option Bool) :
    (advance (TM2.step program))^[(encodeWords (blockWords values)).length]
      (some ⟨some (labels 0), (ambient, register),
        tapesAt source destination base (encodeWords (blockWords values) ++ suffix) output⟩) =
      some ⟨exit, (ambient, none), tapesAt source destination base suffix
        ((encodeWords (blockWords values)).reverse ++ output)⟩ := by
  have first := fieldTrace source destination distinct labels exit rejected program atLabels base ambient
    0 (values 0) (encodeWords [values 1, values 2, values 3, values 4, values 5] ++ suffix)
    output register
  have second := fieldTrace source destination distinct labels exit rejected program atLabels base ambient
    1 (values 1) (encodeWords [values 2, values 3, values 4, values 5] ++ suffix)
    ((encodeWord (values 0)).reverse ++ output) none
  have third := fieldTrace source destination distinct labels exit rejected program atLabels base ambient
    2 (values 2) (encodeWords [values 3, values 4, values 5] ++ suffix)
    ((encodeWord (values 1)).reverse ++ ((encodeWord (values 0)).reverse ++ output)) none
  have fourth := fieldTrace source destination distinct labels exit rejected program atLabels base ambient
    3 (values 3) (encodeWords [values 4, values 5] ++ suffix)
    ((encodeWord (values 2)).reverse ++ ((encodeWord (values 1)).reverse ++
      ((encodeWord (values 0)).reverse ++ output))) none
  have fifth := fieldTrace source destination distinct labels exit rejected program atLabels base ambient
    4 (values 4) (encodeWords [values 5] ++ suffix)
    ((encodeWord (values 3)).reverse ++ ((encodeWord (values 2)).reverse ++
      ((encodeWord (values 1)).reverse ++ ((encodeWord (values 0)).reverse ++ output)))) none
  have sixth := fieldTrace source destination distinct labels exit rejected program atLabels base ambient
    5 (values 5) suffix
    ((encodeWord (values 4)).reverse ++ ((encodeWord (values 3)).reverse ++
      ((encodeWord (values 2)).reverse ++ ((encodeWord (values 1)).reverse ++
        ((encodeWord (values 0)).reverse ++ output))))) none
  simp only [nextField_zero, nextField_one, nextField_two, nextField_three,
    nextField_four, nextField_five, encodeWords, List.append_nil, List.append_assoc]
    at first second third fourth fifth sixth
  have full := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace first second) third) fourth) fifth) sixth
  have htime : ((((values 0 + 1 + (values 1 + 1)) + (values 2 + 1)) +
      (values 3 + 1)) + (values 4 + 1)) + (values 5 + 1) =
      (encodeWords (blockWords values)).length := by
    simp only [encodeWords_length, blockWords, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil]
    omega
  rw [htime] at full
  simpa only [blockWords, encodeWords, List.append_nil, List.reverse_append,
    List.reverse_nil, List.nil_append, List.append_assoc] using full

def blockInTime (values : Fin 6 → Nat) (suffix output : List Bool) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels 0), (ambient, register),
        tapesAt source destination base (encodeWords (blockWords values) ++ suffix) output⟩
      (some ⟨exit, (ambient, none), tapesAt source destination base suffix
        ((encodeWords (blockWords values)).reverse ++ output)⟩)
      (encodeWords (blockWords values)).length where
  steps := (encodeWords (blockWords values)).length
  evals_in_steps := blockTrace source destination distinct labels exit rejected program atLabels
    base ambient values suffix output register
  steps_le_m := Nat.le_refl _

theorem listTrace (words : List Nat) (length_eq : words.length = 6)
    (suffix output : List Bool) (register : Option Bool) :
    (advance (TM2.step program))^[(encodeWords words).length]
      (some ⟨some (labels 0), (ambient, register),
        tapesAt source destination base (encodeWords words ++ suffix) output⟩) =
      some ⟨exit, (ambient, none), tapesAt source destination base suffix
        ((encodeWords words).reverse ++ output)⟩ := by
  simpa only [blockWords_listValues] using
    blockTrace source destination distinct labels exit rejected program atLabels
      base ambient (listValues words length_eq) suffix output register

def listInTime (words : List Nat) (length_eq : words.length = 6)
    (suffix output : List Bool) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels 0), (ambient, register),
        tapesAt source destination base (encodeWords words ++ suffix) output⟩
      (some ⟨exit, (ambient, none), tapesAt source destination base suffix
        ((encodeWords words).reverse ++ output)⟩)
      (encodeWords words).length where
  steps := (encodeWords words).length
  evals_in_steps := listTrace source destination distinct labels exit rejected program atLabels
    base ambient words length_eq suffix output register
  steps_le_m := Nat.le_refl _

end Placement

abbrev ConcreteLabel := Fin 6 ⊕ Bool

def concreteProgram : ConcreteLabel → TM2.Stmt (Alphabet (K := Bool)) ConcreteLabel (State Unit)
  | .inl slot => instruction false true (.inl slot)
      (nextField Sum.inl (some (.inr true)) slot) (some (.inr false))
  | .inr _ => .halt

abbrev machine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := Alphabet
  Λ := ConcreteLabel
  main := .inl 0
  σ := State Unit
  initialState := ((), none)
  m := concreteProgram

def machineInTime (values : Fin 6 → Nat) (suffix output : List Bool) :
    StateTransition.EvalsToInTime machine.step
      ⟨some (.inl 0), ((), none), tapesAt false true (fun _ : Bool => [])
        (encodeWords (blockWords values) ++ suffix) output⟩
      (some ⟨some (.inr true), ((), none), tapesAt false true (fun _ : Bool => []) suffix
        ((encodeWords (blockWords values)).reverse ++ output)⟩)
      (encodeWords (blockWords values)).length :=
  blockInTime false true (by decide) Sum.inl (some (.inr true)) (some (.inr false))
    concreteProgram (fun _ => rfl) (fun _ => []) () values suffix output none

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end PerfectCompleteness.UnaryBlockCopyMachine

end OAI
