import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import OAI.Computability.PerfectCompleteness.Foundations.SourceClause
import OAI.Computability.PerfectCompleteness.Reduction.OccurrenceGame

namespace OAI

section

namespace PerfectCompleteness.SourceGame

open SourceClause UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

def decodeLabel (signs : Triple) (label : Fin 7) : Triple :=
  (satisfyingTriples signs)[label.val]'(by
    rw [satisfyingTriples_length]
    exact label.isLt)

theorem decodeLabel_mem (signs : Triple) (label : Fin 7) :
    decodeLabel signs label ∈ satisfyingTriples signs := by
  exact List.getElem_mem _

theorem decodeLabel_legal (signs : Triple) (label : Fin 7) :
    localEval signs (decodeLabel signs label) = true :=
  (mem_satisfyingTriples signs _).mp (decodeLabel_mem signs label)

theorem decodeLabel_injective (signs : Triple) : Function.Injective (decodeLabel signs) := by
  intro a b same
  apply Fin.ext
  exact (List.Nodup.getElem_inj (satisfyingTriples_nodup signs)).mp same

def encodeLabel (signs label : Triple) (legal : localEval signs label = true) : Fin 7 :=
  ⟨(satisfyingTriples signs).idxOf label, by
    have h := List.idxOf_lt_length_of_mem ((mem_satisfyingTriples signs label).mpr legal)
    simpa using h⟩

@[simp] theorem decodeLabel_encodeLabel (signs label : Triple)
    (legal : localEval signs label = true) :
    decodeLabel signs (encodeLabel signs label legal) = label := by
  exact List.getElem_idxOf _

def projection {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (e : Occurrence m) (answer : Fin 7) : Bool :=
  (decodeLabel (clauses e.1).signs answer).at e.2

theorem projection_surjective {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (e : Occurrence m) (answer : Bool) :
    ∃ label : Fin 7, projection clauses e label = answer := by
  obtain ⟨t, legal, ht⟩ := coordinate_surjective (clauses e.1).signs e.2 answer
  refine ⟨encodeLabel (clauses e.1).signs t
    ((mem_satisfyingTriples _ _).mp legal), ?_⟩
  simpa [projection] using ht

theorem projection_pair_surjective {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (c : Fin m) (i j : Fin 3) (different : i ≠ j) (first second : Bool) :
    ∃ label : Fin 7,
      projection clauses (c, i) label = first ∧ projection clauses (c, j) label = second := by
  obtain ⟨t, legal, ht⟩ := pair_surjective (clauses c).signs i j different first second
  refine ⟨encodeLabel (clauses c).signs t ((mem_satisfyingTriples _ _).mp legal), ?_⟩
  simpa [projection] using ht

theorem leftAlphabet_card : Fintype.card (Fin 7) = 7 := by simp
theorem rightAlphabet_card : Fintype.card Bool = 2 := by decide

noncomputable section

def game {n m : Nat} [NeZero m] (clauses : Fin m → NormalizedClause n) :
    OccurrenceGame (Occurrence m) (Fin m) (Fin n) (Fin 7) Bool :=
  OccurrenceGame.ofProjection (FiniteDistribution.uniform (Occurrence m))
    Prod.fst (occurrenceVariable clauses) (projection clauses)

theorem endpointDetermined {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n) : (game clauses).EndpointDetermined := by
  intro e e' sameClause sameVariable a b
  have same := occurrence_determined_by_endpoints clauses e e' sameClause sameVariable
  subst e'
  rfl

def endpointPredicate {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (c : Fin m) (v : Fin n) (a : Fin 7) (b : Bool) : Bool :=
  decide (∃ i : Fin 3, (clauses c).variable i = v ∧
    (decodeLabel (clauses c).signs a).at i = b)

theorem endpointPredicate_eq_true {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (c : Fin m) (v : Fin n) (a : Fin 7) (b : Bool) :
    endpointPredicate clauses c v a b = true ↔
      ∃ i : Fin 3, (clauses c).variable i = v ∧
        (decodeLabel (clauses c).signs a).at i = b := by
  exact decide_eq_true_iff

def presentation {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n) : (game clauses).EndpointPresentation where
  predicate := endpointPredicate clauses
  agrees e a b := by
    apply Bool.eq_iff_iff.mpr
    rw [endpointPredicate_eq_true]
    simp only [game, OccurrenceGame.ofProjection, occurrenceVariable, decide_eq_true_eq]
    constructor
    · intro h
      exact ⟨e.2, rfl, h⟩
    · rintro ⟨i, sameVariable, h⟩
      have samePosition : i = e.2 := (clauses e.1).distinct i e.2 sameVariable
      simpa [projection, samePosition] using h

def questionGame {n m : Nat} [NeZero m] (clauses : Fin m → NormalizedClause n) :
    Game (Fin m) (Fin n) (Fin 7) Bool :=
  (game clauses).toGame (presentation clauses)

@[simp] theorem questionGame_success {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n) (strategy : Strategy (Fin m) (Fin n) (Fin 7) Bool) :
    (questionGame clauses).success strategy = (game clauses).success strategy :=
  (game clauses).toGame_success (presentation clauses) strategy

theorem restrict_at {n : Nat} (c : NormalizedClause n)
    (assignment : Fin n → Bool) (i : Fin 3) :
    (c.restrict assignment).at i = assignment (c.variable i) := by
  have cases_three : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases cases_three i with rfl | rfl | rfl <;> rfl

def completenessStrategy {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (assignment : Fin n → Bool) (satisfying : ∀ c, (clauses c).clause.eval assignment = true) :
    Strategy (Fin m) (Fin n) (Fin 7) Bool :=
  (fun c => encodeLabel (clauses c).signs ((clauses c).restrict assignment)
    (by simpa using satisfying c), assignment)

theorem completeness_wins {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n) (assignment : Fin n → Bool)
    (satisfying : ∀ c, (clauses c).clause.eval assignment = true) (e : Occurrence m) :
    (game clauses).wins (completenessStrategy clauses assignment satisfying) e = true := by
  simp only [game, OccurrenceGame.ofProjection, OccurrenceGame.wins, completenessStrategy,
    projection, decodeLabel_encodeLabel, decide_eq_true_eq]
  exact restrict_at (clauses e.1) assignment e.2

theorem completeness_success {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n) (assignment : Fin n → Bool)
    (satisfying : ∀ c, (clauses c).clause.eval assignment = true) :
    (game clauses).success (completenessStrategy clauses assignment satisfying) = 1 := by
  have h : (game clauses).wins (completenessStrategy clauses assignment satisfying) =
      fun _ => true := funext (completeness_wins clauses assignment satisfying)
  unfold OccurrenceGame.success
  rw [h, FiniteDistribution.probability_true]

theorem completeness_value {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n) (assignment : Fin n → Bool)
    (satisfying : ∀ c, (clauses c).clause.eval assignment = true) :
    (game clauses).value = 1 := by
  apply le_antisymm (game clauses).value_le_one
  rw [← completeness_success clauses assignment satisfying]
  exact (game clauses).success_le_value _

def winCount {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (strategy : Strategy (Fin m) (Fin n) (Fin 7) Bool) : Nat :=
  ∑ c, agreementCount (clauses c) (decodeLabel (clauses c).signs (strategy.1 c)) strategy.2

def violatedCount {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (assignment : Fin n → Bool) : Nat :=
  ∑ c, if (clauses c).clause.eval assignment then 0 else 1

theorem winCount_add_violated_le {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (strategy : Strategy (Fin m) (Fin n) (Fin 7) Bool) :
    winCount clauses strategy + violatedCount clauses strategy.2 ≤ 3 * m := by
  unfold winCount violatedCount
  rw [← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _c : Fin m, 3 := by
      apply Finset.sum_le_sum
      intro c _
      have h := agreementCount_le_two_add_satisfied (clauses c)
        (decodeLabel (clauses c).signs (strategy.1 c)) strategy.2
        (decodeLabel_legal _ _)
      cases heval : (clauses c).clause.eval strategy.2 <;>
        simp [heval] at h ⊢ <;> omega
    _ = 3 * m := by simp [Nat.mul_comm]

private theorem probability_uniform {E : Type*} [Fintype E] [Nonempty E]
    (event : E → Bool) :
    (FiniteDistribution.uniform E).probability event =
      (∑ e, if event e then (1 : ℝ) else 0) / (Fintype.card E : ℝ) := by
  unfold FiniteDistribution.probability FiniteDistribution.uniform
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  cases event e <;> simp

theorem success_eq_winCount_div {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n)
    (strategy : Strategy (Fin m) (Fin n) (Fin 7) Bool) :
    (game clauses).success strategy = (winCount clauses strategy : ℝ) / (3 * (m : ℝ)) := by
  have hsum :
      (∑ e : Occurrence m, if (game clauses).wins strategy e then (1 : ℝ) else 0) =
        (winCount clauses strategy : ℝ) := by
    rw [Fintype.sum_prod_type]
    simp only [winCount, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Fin.sum_univ_three]
    simp [game, OccurrenceGame.ofProjection, OccurrenceGame.wins, projection,
      occurrenceVariable, agreementCount, Triple.at, Nat.cast_add, Nat.cast_ite]
  change (FiniteDistribution.uniform (Occurrence m)).probability
    ((game clauses).wins strategy) = _
  rw [probability_uniform, hsum]
  congr 1
  simp [Occurrence, mul_comm]

theorem success_le_one_sub_third_violations {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n)
    (strategy : Strategy (Fin m) (Fin n) (Fin 7) Bool) :
    (game clauses).success strategy ≤
      1 - ((violatedCount clauses strategy.2 : ℝ) / (m : ℝ)) / 3 := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_neZero m
  have hden : (0 : ℝ) < 3 * (m : ℝ) := mul_pos (by norm_num) hm
  have hcount : (winCount clauses strategy : ℝ) +
      (violatedCount clauses strategy.2 : ℝ) ≤ 3 * (m : ℝ) := by
    exact_mod_cast winCount_add_violated_le clauses strategy
  rw [success_eq_winCount_div]
  apply (div_le_iff₀ hden).mpr
  have hidentity :
      (1 - ((violatedCount clauses strategy.2 : ℝ) / (m : ℝ)) / 3) * (3 * (m : ℝ)) =
        3 * (m : ℝ) - (violatedCount clauses strategy.2 : ℝ) := by
    field_simp [ne_of_gt hm]
  rw [hidentity]
  linarith

end
end PerfectCompleteness.SourceGame

end

end OAI
