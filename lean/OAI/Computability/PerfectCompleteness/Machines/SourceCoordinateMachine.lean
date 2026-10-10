import OAI.Computability.PerfectCompleteness.Machines.SourceClauseLookupMachine
import OAI.Computability.PerfectCompleteness.Machines.SourceClauseReaderMachineLemmas

namespace OAI


namespace PerfectCompleteness.SourceCoordinateMachine


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition UniqueGamesTheorem.Reduction.MachineTransfer

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := SourceClauseReaderMachine.State A
abbrev Signs := NormalizationReadMachine.Signs

def lookupMap (i : Fin 6) : Fin 10 := ⟨i.val, lt_trans i.isLt (by decide)⟩
def readerMap (i : Fin 4) : Fin 10 := ⟨i.val + 6, by have := i.isLt; omega⟩

def lookupTapes (tape : Fin 10 → K) : Fin 6 → K := fun i => tape (lookupMap i)
def readerTapes (tape : Fin 10 → K) : Fin 4 → K := fun i => tape (readerMap i)

omit [DecidableEq K] in
theorem lookupTapes_injective (tape : Fin 10 → K) (distinct : Function.Injective tape) :
    Function.Injective (lookupTapes tape) := by
  intro i j h
  have hv := congrArg (fun x : Fin 10 => x.val) (distinct h)
  exact Fin.ext hv

omit [DecidableEq K] in
theorem readerTapes_injective (tape : Fin 10 → K) (distinct : Function.Injective tape) :
    Function.Injective (readerTapes tape) := by
  intro i j h
  have hv := congrArg (fun x : Fin 10 => x.val) (distinct h)
  apply Fin.ext
  dsimp [readerMap] at hv
  omega

inductive Label
  | lookup (label : SourceClauseLookupMachine.Label)
  | restore
  | read (label : SourceClauseReaderMachine.Label)
  deriving DecidableEq, Fintype

def main : Label := .lookup SourceClauseLookupMachine.main

def instruction (tape : Fin 10 → K) (labels : Label → Λ) (done rejected : Option Λ)
    (save : A → CanonicalKeyShape.Shape → A) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .lookup l => SourceClauseLookupMachine.instruction (lookupTapes tape)
      (fun l => labels (.lookup l)) (some (labels .restore)) rejected l
  | .restore => loopAt (tape 5) (tape 6) id false (labels .restore)
      (some (labels (.read SourceClauseReaderMachine.main)))
  | .read l => SourceClauseReaderMachine.instruction (readerTapes tape)
      (fun l => labels (.read l)) done rejected save l

def resultTapes {n : Nat} (tape : Fin 10 → K) (base : K → List Bool)
    (clause : Clause n) : K → List Bool :=
  NormalizationReadMachine.tapes (readerTapes tape) base []
    (NormalizationReadMachine.clauseCounters clause)

theorem result_variable {n : Nat} (tape : Fin 10 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (clause : Clause n) (slot : Fin 3) :
    resultTapes tape base clause (readerTapes tape slot.succ) =
      List.replicate clause[slot].variableIndex.val true :=
  NormalizationReadMachine.tapes_counter (readerTapes tape)
    (readerTapes_injective tape distinct) base [] _ slot

theorem result_original {n : Nat} (tape : Fin 10 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (clause : Clause n) (i : Fin 10) (original : i.val < 6) :
    resultTapes tape base clause (tape i) = base (tape i) := by
  apply NormalizationReadMachine.tapes_other
  intro j same
  have hv := congrArg (fun x : Fin 10 => x.val) (distinct same)
  dsimp [readerTapes, readerMap] at hv
  omega

def steps (formula : Formula) (index : Fin formula.clauses.length) : Nat :=
  SourceClauseLookupMachine.steps formula index.val +
    ((encodeWords (clauseWords formula.clauses[index.val])).length + 1) +
    SourceClauseReaderMachine.steps formula.clauses[index.val]

theorem steps_le (formula : Formula) (index : Fin formula.clauses.length) :
    steps formula index ≤
      30 * ((SourceOccurrenceEncoding.bits formula).length + index.val + 1) := by
  have lookupBound := SourceClauseLookupMachine.steps_le formula index.val index.isLt
  have readerBound := SourceClauseReaderMachine.steps_le_encoded_length formula.clauses[index.val]
  have clauseBound := clauseBits_length_le formula.clauses[index.val]
  have variableBound : formula.variables ≤ (SourceOccurrenceEncoding.bits formula).length := by
    rw [SourceOccurrenceEncoding.bits_eq]
    simp only [List.length_append, encodeWord_length]
    omega
  unfold steps
  omega

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

variable (tape : Fin 10 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (done rejected : Option Λ)
variable (save : A → CanonicalKeyShape.Shape → A)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) = instruction tape labels done rejected save l)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem coordinateTrace (formula : Formula) (index : Fin formula.clauses.length)
    (signs : Signs)
    (tableWord : base (tape 0) = SourceOccurrenceEncoding.bits formula)
    (indexWord : base (tape 1) = List.replicate index.val true)
    (empty : ∀ i : Fin 10, 2 ≤ i.val → base (tape i) = []) :
    (advance (TM2.step program))^[steps formula index]
      (some ⟨some (labels main), SourceClauseReaderMachine.clean ambient signs, base⟩) =
      some ⟨done,
        SourceClauseReaderMachine.clean
          (save ambient (SourceClauseReaderMachine.clauseShape formula.clauses[index.val]))
          (NormalizationReadMachine.clauseSigns formula.clauses[index.val]),
        resultTapes tape base formula.clauses[index.val]⟩ := by
  have hd (i j : Fin 10) (different : i ≠ j) : tape i ≠ tape j :=
    fun same => different (distinct same)
  let clause := formula.clauses[index.val]
  let word := encodeWords (clauseWords clause)
  let reversed := Function.update base (tape 5) word.reverse
  let forward := Function.update base (tape 6) word
  have looked := SourceClauseLookupMachine.lookupTrace (lookupTapes tape)
    (lookupTapes_injective tape distinct) (fun l => labels (.lookup l))
    (some (labels .restore)) rejected program (fun l => atLabels (.lookup l))
    base (ambient, signs) formula index.val index.isLt tableWord indexWord
    (empty 2 (by decide)) (empty 3 (by decide)) (empty 4 (by decide))
  change (advance (TM2.step program))^[SourceClauseLookupMachine.steps formula index.val]
    (some ⟨some (labels main), SourceClauseReaderMachine.clean ambient signs, base⟩) =
    some ⟨some (labels .restore), SourceClauseReaderMachine.clean ambient signs,
      Function.update base (tape 5) (word.reverse ++ base (tape 5))⟩ at looked
  rw [empty 5 (by decide), List.append_nil] at looked
  have restored : (advance (TM2.step program))^[word.length + 1]
      (some ⟨some (labels .restore), SourceClauseReaderMachine.clean ambient signs, reversed⟩) =
      some ⟨some (labels (.read SourceClauseReaderMachine.main)),
        SourceClauseReaderMachine.clean ambient signs, forward⟩ := by
    change (nextAt (tape 6) program)^[word.length + 1]
      (some ⟨some (labels .restore), ((ambient, signs), none), reversed⟩) =
      some ⟨some (labels (.read SourceClauseReaderMachine.main)),
        ((ambient, signs), none), forward⟩
    have source : reversed (tape 5) = word.reverse := by simp [reversed]
    have dest : reversed (tape 6) = [] := by simp [reversed, hd, empty 6 (by decide)]
    have updated : tapesAt (tape 5) (tape 6) reversed [] word = forward := by
      funext k
      by_cases h5 : k = tape 5
      · subst k; simp [tapesAt, reversed, forward, hd, empty 5 (by decide)]
      · by_cases h6 : k = tape 6
        · subst k; simp [tapesAt, reversed, forward]
        · simp [tapesAt, reversed, forward, h5, h6]
    have native := transferAt_fromTapes (Γ := Alphabet (K := K)) (tape 5) (tape 6)
      (hd 5 6 (by decide)) id false (labels .restore)
      (some (labels (.read SourceClauseReaderMachine.main))) program (atLabels .restore)
      reversed (ambient, signs) none
    rw [source, dest, List.length_reverse, List.reverse_reverse, List.map_id_fun,
      List.append_nil, id_eq, updated] at native
    exact native
  have initialReader : NormalizationReadMachine.tapes (readerTapes tape) base word
      (fun _ => []) = forward := by
    funext k
    by_cases h7 : k = tape 7
    · subst k; simp [NormalizationReadMachine.tapes, readerTapes, readerMap, forward, hd,
        empty 7 (by decide)]
    · by_cases h8 : k = tape 8
      · subst k; simp [NormalizationReadMachine.tapes, readerTapes, readerMap, forward, hd,
          empty 8 (by decide)]
      · by_cases h9 : k = tape 9
        · subst k; simp [NormalizationReadMachine.tapes, readerTapes, readerMap, forward, hd,
            empty 9 (by decide)]
        · simp [NormalizationReadMachine.tapes, readerTapes, readerMap, forward,
            Function.update_apply, h7, h8, h9]
  have read := SourceClauseReaderMachine.readTrace (readerTapes tape)
    (readerTapes_injective tape distinct) (fun l => labels (.read l)) done rejected save
    program (fun l => atLabels (.read l)) base ambient clause [] signs none
  simp only [List.append_nil] at read
  change (advance (TM2.step program))^[SourceClauseReaderMachine.steps clause]
    (some ⟨some (labels (.read SourceClauseReaderMachine.main)),
      SourceClauseReaderMachine.clean ambient signs,
      NormalizationReadMachine.tapes (readerTapes tape) base word (fun _ => [])⟩) =
    some ⟨done,
      SourceClauseReaderMachine.clean (save ambient (SourceClauseReaderMachine.clauseShape clause))
        (NormalizationReadMachine.clauseSigns clause),
      resultTapes tape base clause⟩ at read
  rw [initialReader] at read
  exact joinTrace (joinTrace looked restored) read

def coordinateInTime (formula : Formula) (index : Fin formula.clauses.length)
    (signs : Signs)
    (tableWord : base (tape 0) = SourceOccurrenceEncoding.bits formula)
    (indexWord : base (tape 1) = List.replicate index.val true)
    (empty : ∀ i : Fin 10, 2 ≤ i.val → base (tape i) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels main), SourceClauseReaderMachine.clean ambient signs, base⟩
      (some ⟨done,
        SourceClauseReaderMachine.clean
          (save ambient (SourceClauseReaderMachine.clauseShape formula.clauses[index.val]))
          (NormalizationReadMachine.clauseSigns formula.clauses[index.val]),
        resultTapes tape base formula.clauses[index.val]⟩)
      (30 * ((SourceOccurrenceEncoding.bits formula).length + index.val + 1)) where
  steps := steps formula index
  evals_in_steps := coordinateTrace tape distinct labels done rejected save program atLabels
    base ambient formula index signs tableWord indexWord empty
  steps_le_m := steps_le formula index

end PerfectCompleteness.SourceCoordinateMachine

end OAI
