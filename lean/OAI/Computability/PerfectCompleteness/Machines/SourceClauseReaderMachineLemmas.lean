import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Linarith
import OAI.Computability.PerfectCompleteness.Foundations.CanonicalEdgesLemmas
import OAI.Computability.PerfectCompleteness.Machines.NormalizationReadMachine
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas

namespace OAI


namespace PerfectCompleteness.SourceClauseReaderMachine


open Turing
open UniqueGamesTheorem.Foundations
open Complexity Complexity.MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

abbrev Signs := NormalizationReadMachine.Signs
abbrev State (A : Type) := NormalizationReadMachine.State A
abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev clean {A : Type} (ambient : A) (signs : Signs) : State A :=
  NormalizationReadMachine.clean ambient signs

def shape (signs : Signs) : CanonicalKeyShape.Shape :=
  .clause (signs 0, signs 1, signs 2)

def clauseShape {n : Nat} (clause : Target.Clause n) : CanonicalKeyShape.Shape :=
  shape (NormalizationReadMachine.clauseSigns clause)

@[simp] theorem clauseShape_eq {n : Nat} (clause : Target.Clause n) :
    clauseShape clause = .clause (clause[0].positive, clause[1].positive, clause[2].positive) := rfl

def steps {n : Nat} (clause : Target.Clause n) : Nat :=
  clause[0].variableIndex.val + clause[1].variableIndex.val + clause[2].variableIndex.val + 7

inductive Label where
  | read (label : NormalizationReadMachine.Label)
  | publish
  deriving DecidableEq, Fintype

def main : Label := .read (.field 0)

section Placement

variable {K Λ A : Type} [DecidableEq K]

def instruction (tape : Fin 4 → K) (labels : Label → Λ) (done rejected : Option Λ)
    (save : A → CanonicalKeyShape.Shape → A) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .read label => NormalizationReadMachine.instruction tape
      (fun label => labels (.read label)) (some (labels .publish)) rejected label
  | .publish =>
      .load (fun state => clean (save state.1.1 (shape state.1.2)) state.1.2)
        (exitAt (tape 0) done)

variable (tape : Fin 4 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (done rejected : Option Λ)
variable (save : A → CanonicalKeyShape.Shape → A)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ label, program (labels label) = instruction tape labels done rejected save label)
variable (base : K → List Bool) (ambient : A)

include atLabels in
theorem publishStep (signs : Signs) (register : Option Bool) (tapeValues : K → List Bool) :
    TM2.step program ⟨some (labels .publish), ((ambient, signs), register), tapeValues⟩ =
      some ⟨done, clean (save ambient (shape signs)) signs, tapeValues⟩ := by
  change some (TM2.stepAux (program (labels .publish)) _ _) = _
  rw [atLabels .publish]
  cases done <;> rfl

include distinct atLabels

theorem readTrace {n : Nat} (clause : Target.Clause n) (suffix : List Bool)
    (signs : Signs) (register : Option Bool) :
    (advance (TM2.step program))^[steps clause]
      (some ⟨some (labels main), ((ambient, signs), register),
        NormalizationReadMachine.tapes tape base
          (encodeWords (clauseWords clause) ++ suffix) (fun _ => [])⟩) =
      some ⟨done, clean (save ambient (clauseShape clause))
        (NormalizationReadMachine.clauseSigns clause),
        NormalizationReadMachine.tapes tape base suffix
          (NormalizationReadMachine.clauseCounters clause)⟩ := by
  have first := NormalizationReadMachine.clauseTrace tape distinct
    (fun label => labels (.read label)) (some (labels .publish)) rejected program
    (fun label => atLabels (.read label)) base ambient clause suffix signs register
  have second := publishStep tape labels done rejected save program atLabels ambient
    (NormalizationReadMachine.clauseSigns clause) none
    (NormalizationReadMachine.tapes tape base suffix
      (NormalizationReadMachine.clauseCounters clause))
  rw [show steps clause =
      (clause[0].variableIndex.val + clause[1].variableIndex.val + clause[2].variableIndex.val + 6) + 1 by
        unfold steps
        omega,
    Function.iterate_succ_apply']
  change advance (TM2.step program)
    ((advance (TM2.step program))^[clause[0].variableIndex.val +
      clause[1].variableIndex.val + clause[2].variableIndex.val + 6]
      (some ⟨some (labels (.read (.field 0))), ((ambient, signs), register),
        NormalizationReadMachine.tapes tape base
          (encodeWords (clauseWords clause) ++ suffix) (fun _ => [])⟩)) = _
  rw [first, advance_some]
  exact second

def readInTime {n : Nat} (clause : Target.Clause n) (suffix : List Bool)
    (signs : Signs) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels main), ((ambient, signs), register),
        NormalizationReadMachine.tapes tape base
          (encodeWords (clauseWords clause) ++ suffix) (fun _ => [])⟩
      (some ⟨done, clean (save ambient (clauseShape clause))
        (NormalizationReadMachine.clauseSigns clause),
        NormalizationReadMachine.tapes tape base suffix
          (NormalizationReadMachine.clauseCounters clause)⟩)
      (steps clause) where
  steps := steps clause
  evals_in_steps := readTrace tape distinct labels done rejected save program atLabels
    base ambient clause suffix signs register
  steps_le_m := Nat.le_refl _

end Placement

theorem steps_le_encoded_length {n : Nat} (clause : Target.Clause n) :
    steps clause ≤ (encodeWords (clauseWords clause)).length + 1 := by
  have bound := NormalizationReadMachine.steps_le_encoded_length clause
  unfold steps
  omega

theorem finiteState {A : Type} [Finite A] : Finite (State A) := inferInstance

theorem finiteAlphabet {K : Type} (k : K) : Finite (Alphabet k) := by
  change Finite Bool
  infer_instance

end PerfectCompleteness.SourceClauseReaderMachine


namespace PerfectCompleteness.SourceOccurrenceEncoding

open UniqueGamesTheorem.Foundations Complexity Target

def recordWords {n : Nat} (index : Nat) (clause : Clause n) : List Nat :=
  index :: clauseWords clause

def records {n : Nat} (first : Nat) : List (Clause n) → List Nat
  | [] => []
  | clause :: clauses => recordWords first clause ++ records (first + 1) clauses

def recordBits {n : Nat} (index : Nat) (clause : Clause n) : List Bool :=
  encodeWords (recordWords index clause)

def body {n : Nat} (first : Nat) (clauses : List (Clause n)) : List Bool :=
  encodeWords (records first clauses)

def words (formula : Formula) : List Nat :=
  [formula.variables, formula.clauses.length] ++ records 0 formula.clauses

def bits (formula : Formula) : List Bool := encodeWords (words formula)

@[simp] theorem recordWords_length {n : Nat} (index : Nat) (clause : Clause n) :
    (recordWords index clause).length = 7 := by simp [recordWords]

@[simp] theorem records_length {n : Nat} (first : Nat) (clauses : List (Clause n)) :
    (records first clauses).length = 7 * clauses.length := by
  induction clauses generalizing first with
  | nil => rfl
  | cons clause clauses ih => simp [records, ih, Nat.mul_add]; omega

@[simp] theorem words_length (formula : Formula) :
    (words formula).length = 2 + 7 * formula.clauses.length := by simp [words]; omega

theorem records_eq_finRange {n : Nat} (clauses : List (Clause n)) (first : Nat) :
    records first clauses = (List.finRange clauses.length).flatMap (fun i =>
      recordWords (first + i.val) clauses[i.val]) := by
  induction clauses generalizing first with
  | nil => simp [records]
  | cons clause clauses ih =>
      simp only [records, List.length_cons, List.finRange_succ, List.flatMap_cons,
        List.flatMap_map, List.getElem_cons_zero, Fin.val_zero, Nat.add_zero]
      apply congrArg (fun rest => recordWords first clause ++ rest)
      rw [ih]
      apply List.flatMap_congr
      intro i _
      simp only [Fin.val_succ, List.getElem_cons_succ]
      congr 1
      omega

@[simp] theorem body_nil {n : Nat} (first : Nat) : body first ([] : List (Clause n)) = [] := rfl

theorem body_cons {n : Nat} (first : Nat) (clause : Clause n) (clauses : List (Clause n)) :
    body first (clause :: clauses) = recordBits first clause ++ body (first + 1) clauses := by
  exact encodeWords_append _ _

theorem recordBits_eq {n : Nat} (index : Nat) (clause : Clause n) :
    recordBits index clause = encodeWord index ++ encodeWords (clauseWords clause) := rfl

theorem bits_eq (formula : Formula) :
    bits formula = encodeWord formula.variables ++ encodeWord formula.clauses.length ++
      body 0 formula.clauses := by
  simp only [bits, words, encodeWords_append, encodeWords, List.append_nil,
    body, List.append_assoc]

def parseRecords (variableCount : Nat) : Nat → Nat → List Nat →
    Option (List (Clause variableCount) × List Nat)
  | _, 0, remaining => some ([], remaining)
  | first, count + 1, index :: remaining => do
      if index = first then
        let (clause, remaining) ← parseClause variableCount remaining
        let (clauses, remaining) ← parseRecords variableCount (first + 1) count remaining
        return (clause :: clauses, remaining)
      else none
  | _, _ + 1, [] => none

@[simp] theorem parseRecords_encoded {n : Nat} (clauses : List (Clause n))
    (first : Nat) (suffix : List Nat) :
    parseRecords n first clauses.length (records first clauses ++ suffix) =
      some (clauses, suffix) := by
  induction clauses generalizing first with
  | nil => rfl
  | cons clause clauses ih =>
      simp [records, recordWords, List.append_assoc, parseRecords, parseClause_encoded, ih]

def decodeWords : List Nat → Option Formula
  | variableCount :: count :: remaining => do
      let (clauses, remaining) ← parseRecords variableCount 0 count remaining
      if remaining = [] then some ⟨variableCount, clauses⟩ else none
  | _ => none

def decode (input : List Bool) : Option Formula :=
  Complexity.decodeWords input >>= decodeWords

@[simp] theorem decodeWords_words (formula : Formula) :
    decodeWords (words formula) = some formula := by
  cases formula with
  | mk variableCount clauses =>
      have parsed := parseRecords_encoded clauses 0 []
      simp only [List.append_nil] at parsed
      simp [words, decodeWords, parsed]

@[simp] theorem decode_bits (formula : Formula) : decode (bits formula) = some formula := by
  simp [decode, bits]

theorem bits_injective : Function.Injective bits := by
  intro first second same
  have parsed := congrArg decode same
  simpa only [decode_bits, Option.some.injEq] using parsed

theorem body_length_le {n : Nat} (clauses : List (Clause n)) (first maximum : Nat)
    (indices : first + clauses.length ≤ maximum) :
    (body first clauses).length ≤ clauses.length * (maximum + 1 + 3 * (n + 2)) := by
  induction clauses generalizing first with
  | nil => simp
  | cons clause clauses ih =>
      have tail := ih (first + 1) (by simp only [List.length_cons] at indices; omega)
      have head := clauseBits_length_le clause
      rw [body_cons, recordBits_eq]
      simp only [List.length_append, encodeWord_length, List.length_cons]
      nlinarith

end PerfectCompleteness.SourceOccurrenceEncoding

end OAI
