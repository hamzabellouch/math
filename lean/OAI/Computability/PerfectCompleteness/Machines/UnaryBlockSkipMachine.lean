import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.Reduction.MachineTransfer

namespace OAI


namespace PerfectCompleteness.UnaryBlockSkipMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool

section Placement

variable {K Λ A : Type} [DecidableEq K]

def nextField {count : Nat} (labels : Fin (count + 1) → Λ) (exit : Option Λ)
    (slot : Fin (count + 1)) : Option Λ :=
  if h : slot.val + 1 < count + 1 then some (labels ⟨slot.val + 1, h⟩) else exit

def finish (source : K) (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => (state.1, none)) (exitAt source exit)

def instruction (source : K) (again : Λ) (next rejected : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.branch (fun state => state.2.getD false)
        (finish source (some again)) (finish source next))
      (finish source rejected))

variable (source : K) {count : Nat} (labels : Fin (count + 1) → Λ)
variable (exit rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ slot, program (labels slot) =
  instruction source (labels slot) (nextField labels exit slot) rejected)
variable (base : K → List Bool) (ambient : A)

include atLabels

theorem step_true (slot : Fin (count + 1)) (input : List Bool) (register : Option Bool) :
    TM2.step program
      ⟨some (labels slot), (ambient, register), Function.update base source (true :: input)⟩ =
      some ⟨some (labels slot), (ambient, none), Function.update base source input⟩ := by
  change some (TM2.stepAux (program (labels slot)) _ _) = _
  rw [atLabels slot]
  simp [instruction, finish, exitAt, TM2.stepAux]

theorem step_false (slot : Fin (count + 1)) (input : List Bool) (register : Option Bool) :
    TM2.step program
      ⟨some (labels slot), (ambient, register), Function.update base source (false :: input)⟩ =
      some ⟨nextField labels exit slot, (ambient, none), Function.update base source input⟩ := by
  change some (TM2.stepAux (program (labels slot)) _ _) = _
  rw [atLabels slot]
  cases nextField labels exit slot <;>
    simp [instruction, finish, exitAt, TM2.stepAux]

theorem step_empty (slot : Fin (count + 1)) (register : Option Bool) :
    TM2.step program
      ⟨some (labels slot), (ambient, register), Function.update base source []⟩ =
      some ⟨rejected, (ambient, none), Function.update base source []⟩ := by
  change some (TM2.stepAux (program (labels slot)) _ _) = _
  rw [atLabels slot]
  cases rejected <;> simp [instruction, finish, exitAt, TM2.stepAux]

theorem fieldTrace (slot : Fin (count + 1)) (value : Nat) (suffix : List Bool)
    (register : Option Bool) :
    (advance (TM2.step program))^[value + 1]
      (some ⟨some (labels slot), (ambient, register),
        Function.update base source (encodeWord value ++ suffix)⟩) =
      some ⟨nextField labels exit slot, (ambient, none), Function.update base source suffix⟩ := by
  induction value generalizing register with
  | zero =>
      simpa only [Nat.zero_add, Function.iterate_one, advance_some, encodeWord,
        List.replicate_zero, List.nil_append, List.singleton_append] using
        step_false source labels exit rejected program atLabels base ambient slot suffix register
  | succ value ih =>
      rw [Function.iterate_succ_apply]
      simp only [encodeWord, List.replicate_succ, List.cons_append, advance_some]
      rw [step_true source labels exit rejected program atLabels]
      exact ih none

omit [DecidableEq K] atLabels in
private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

private theorem fromTrace (suffix : List Bool) (words : List Nat) :
    ∀ (slot : Fin (count + 1)), words ≠ [] → slot.val + words.length = count + 1 →
      ∀ register : Option Bool,
        (advance (TM2.step program))^[(encodeWords words).length]
          (some ⟨some (labels slot), (ambient, register),
            Function.update base source (encodeWords words ++ suffix)⟩) =
          some ⟨exit, (ambient, none), Function.update base source suffix⟩ := by
  induction words with
  | nil =>
      intro slot nonempty _ _
      exact (nonempty rfl).elim
  | cons value words ih =>
      intro slot _ remaining register
      cases words with
      | nil =>
          have last : ¬slot.val + 1 < count + 1 := by
            simp only [List.length_cons, List.length_nil, Nat.zero_add] at remaining
            omega
          have h := fieldTrace source labels exit rejected program atLabels base ambient
            slot value suffix register
          simpa only [nextField, dite_eq_right last, encodeWords, List.append_nil,
            encodeWord_length] using h
      | cons next words =>
          have more : slot.val + 1 < count + 1 := by
            simp only [List.length_cons] at remaining
            omega
          let following : Fin (count + 1) := ⟨slot.val + 1, more⟩
          have tailCount : following.val + (next :: words).length = count + 1 := by
            simp only [following, List.length_cons] at remaining ⊢
            omega
          have first := fieldTrace source labels exit rejected program atLabels base ambient
            slot value (encodeWords (next :: words) ++ suffix) register
          have second := ih following (by simp) tailCount none
          rw [nextField, dite_eq_left more] at first
          have full := joinTrace first second
          simpa only [encodeWords, List.length_append, encodeWord_length, List.append_assoc]
            using full

theorem listTrace (words : List Nat) (length_eq : words.length = count + 1)
    (suffix : List Bool) (register : Option Bool) :
    (advance (TM2.step program))^[(encodeWords words).length]
      (some ⟨some (labels 0), (ambient, register),
        Function.update base source (encodeWords words ++ suffix)⟩) =
      some ⟨exit, (ambient, none), Function.update base source suffix⟩ := by
  have nonempty : words ≠ [] := by
    intro h
    simp [h] at length_eq
  exact fromTrace source labels exit rejected program atLabels base ambient suffix words 0
    nonempty (by simpa only [Fin.val_zero, Nat.zero_add] using length_eq) register

def listInTime (words : List Nat) (length_eq : words.length = count + 1)
    (suffix : List Bool) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels 0), (ambient, register),
        Function.update base source (encodeWords words ++ suffix)⟩
      (some ⟨exit, (ambient, none), Function.update base source suffix⟩)
      (encodeWords words).length where
  steps := (encodeWords words).length
  evals_in_steps := listTrace source labels exit rejected program atLabels base ambient
    words length_eq suffix register
  steps_le_m := Nat.le_refl _

end Placement

abbrev ConcreteLabel (count : Nat) := Fin (count + 1) ⊕ Bool

def concreteProgram (count : Nat) :
    ConcreteLabel count → TM2.Stmt (Alphabet (K := Bool)) (ConcreteLabel count) (State Unit)
  | .inl slot => instruction false (.inl slot)
      (nextField Sum.inl (some (.inr true)) slot) (some (.inr false))
  | .inr _ => .halt

abbrev machine (count : Nat) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := Alphabet
  Λ := ConcreteLabel count
  main := .inl 0
  σ := State Unit
  initialState := ((), none)
  m := concreteProgram count

def machineInTime (count : Nat) (words : List Nat) (length_eq : words.length = count + 1)
    (suffix : List Bool) :
    StateTransition.EvalsToInTime (machine count).step
      ⟨some (.inl 0), ((), none),
        Function.update (fun _ : Bool => []) false (encodeWords words ++ suffix)⟩
      (some ⟨some (.inr true), ((), none), Function.update (fun _ : Bool => []) false suffix⟩)
      (encodeWords words).length :=
  listInTime false Sum.inl (some (.inr true)) (some (.inr false))
    (concreteProgram count) (fun _ => rfl) (fun _ => []) () words length_eq suffix none

theorem machine_finiteAlphabet (count : Nat) (k : (machine count).K) :
    Finite ((machine count).Γ k) := by
  change Finite Bool
  infer_instance

end PerfectCompleteness.UnaryBlockSkipMachine

end OAI
