import Mathlib.Data.List.FinRange
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.MachineRhsLoad

open Turing
open UniqueGamesTheorem.Foundations.Complexity

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

section Program

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

end Program

end UniqueGamesTheorem.Reduction.MachineRhsLoad

end

end OAI
