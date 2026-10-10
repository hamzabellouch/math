import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionOrderLemmas
import OAI.Computability.PerfectCompleteness.Sampling.CompletedSignedLaw

namespace OAI

section

namespace PerfectCompleteness.CompletedOccurrenceOrder

open MetadataFreeSampler
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v) (rows repeats : Nat → Nat)
  [NeZero m] (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

local notation "locationCount" => TreeCanonical.locationCount branch n t
local notation "hq" => CanonicalLocalCompletion.alphabet_positive locationCount δ
local notation "large" => CanonicalLocalCompletion.partitionWidth_le_alphabet locationCount δ
local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows
  (FinitePreliminaryCompletion.alphabet branch n t δ)
local notation "F" => FinitePreliminaryCompletion.blockFamily clauses branch n t rows repeats

local instance leftVertex_fintype : Fintype (CanonicalGame.LeftVertex F) := Fintype.ofFinite _
local instance rightVertex_fintype : Fintype (CanonicalGame.RightVertex F) := Fintype.ofFinite _
local instance leftLabel_fintype (x : CanonicalGame.LeftVertex F) :
    Fintype (CanonicalGame.LeftLabel F x) := Fintype.ofFinite _
local instance rightLabel_fintype (y : CanonicalGame.RightVertex F) :
    Fintype (CanonicalGame.RightLabel F y) := Fintype.ofFinite _

local notation "C" =>
  FinitePreliminaryCompletion.actualFamily (t := t) clauses rows repeats hn hbranch hrows δ
local notation "Completed" => CompletedSignedLaw.Completed (t := t) clauses rows repeats hn hbranch hrows δ
local notation "transport" =>
  Equiv.symm (CompletedSignedLaw.completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ)

def localOrder (source : PreliminarySampler.Questions branch n t m) : List Completed :=
  (SignedCompletionSchedule.schedule (branch := branch) (n := n) (t := t)
      (rows := rows) (repeats := repeats) hq large hn hbranch hrows
    (sourceSigns clauses source)).map (fun outcome => transport ⟨source, outcome⟩)

def completedOrder : List Completed :=
  (SourceQuestionOrder.sourceOrder branch n t m).flatMap
    (localOrder (t := t) clauses rows repeats hn hbranch hrows δ)

theorem localOrder_length (source : PreliminarySampler.Questions branch n t m) :
    (localOrder (t := t) clauses rows repeats hn hbranch hrows δ source).length = D := by
  rw [localOrder, List.length_map, SignedCompletionSchedule.schedule_length]

theorem completedOrder_length :
    (completedOrder (t := t) clauses rows repeats hn hbranch hrows δ).length =
      D * m ^ locationCount := by
  change (ExactConditionalOutput.output
    (SignedCompletionSchedule.count (branch := branch) (n := n) (t := t)
      (rows := rows) (repeats := repeats) hq large hn hbranch hrows) (sourceSigns clauses)
    (fun source outcome => transport ⟨source, outcome⟩)
    (SourceQuestionOrder.sourceOrder branch n t m)).length = _
  rw [ExactConditionalOutput.output_length _ _ _ D
    (SignedCompletionSchedule.count_total (branch := branch) (n := n) (t := t)
      (rows := rows) (repeats := repeats) hq large hn hbranch hrows),
    SourceQuestionOrder.sourceOrder_length]

theorem completedOrder_nonempty :
    completedOrder (t := t) clauses rows repeats hn hbranch hrows δ ≠ [] := by
  intro hempty
  have h := completedOrder_length (t := t) clauses rows repeats hn hbranch hrows δ
  rw [hempty, List.length_nil] at h
  exact (Nat.ne_of_gt (Nat.mul_pos
    (SignedMultiplicity.denominator_positive branch n t rows repeats hn hbranch hrows _)
    (Nat.pow_pos (NeZero.pos m)))) h.symm

private theorem mem_copies {S : Type*} {E : S → Type*}
    [Fintype S] [∀ s, Fintype (E s)] (count : ∀ s, E s → Nat)
    (s : S) (e : E s) (positive : 0 < count s e) :
    e ∈ ExactConditionalOutput.copies count s := by
  unfold ExactConditionalOutput.copies
  refine List.mem_flatten.mpr ⟨List.replicate (count s e) e, ?_, ?_⟩
  · refine List.mem_ofFn.mpr ⟨ExactConditionalOutput.enumeration s e, ?_⟩
    simp only [Equiv.symm_apply_apply]
  · exact List.mem_replicate.mpr ⟨Nat.ne_of_gt positive, rfl⟩

theorem mem_completedOrder (e : Completed) :
    e ∈ completedOrder (t := t) clauses rows repeats hn hbranch hrows δ := by
  let descriptor := CompletedSignedLaw.completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ e
  apply List.mem_flatMap.mpr
  refine ⟨descriptor.1, SourceQuestionOrder.mem_sourceOrder descriptor.1, ?_⟩
  apply List.mem_map.mpr
  refine ⟨descriptor.2, ?_, ?_⟩
  · exact mem_copies (SignedCompletionSchedule.count (branch := branch) (n := n) (t := t)
      (rows := rows) (repeats := repeats) hq large hn hbranch hrows)
      (sourceSigns clauses descriptor.1) descriptor.2
      (SignedCompletionSchedule.count_positive (branch := branch) (n := n) (t := t)
        (rows := rows) (repeats := repeats) hq large hn hbranch hrows _ _)
  · exact (CompletedSignedLaw.completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ).symm_apply_apply e

def rawOrder : List (PreliminarySampler.Raw clauses branch n t rows repeats) :=
  (completedOrder (t := t) clauses rows repeats hn hbranch hrows δ).map Sigma.fst

theorem mem_rawOrder (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    e ∈ rawOrder (t := t) clauses rows repeats hn hbranch hrows δ := by
  apply List.mem_map.mpr
  refine ⟨⟨e, ⟨0, (C).positive e⟩⟩,
    mem_completedOrder (t := t) clauses rows repeats hn hbranch hrows δ _, rfl⟩

theorem rawOrder_length :
    (rawOrder (t := t) clauses rows repeats hn hbranch hrows δ).length = D * m ^ locationCount := by
  rw [rawOrder, List.length_map,
    completedOrder_length (t := t) clauses rows repeats hn hbranch hrows δ]

theorem completedOrder_filter_length (event : Completed → Bool) :
    ((completedOrder (t := t) clauses rows repeats hn hbranch hrows δ).filter event).length =
      ∑ source : PreliminarySampler.Questions branch n t m,
        ((SignedCompletionSchedule.schedule (branch := branch) (n := n) (t := t)
          (rows := rows) (repeats := repeats) hq large hn hbranch hrows
          (sourceSigns clauses source)).filter
            (fun outcome => event (transport ⟨source, outcome⟩))).length := by
  rw [completedOrder, List.filter_flatMap, List.length_flatMap]
  simp only [localOrder, List.filter_map, List.length_map, Function.comp_def]
  exact SourceQuestionOrder.sum_map_sourceOrder _

theorem completedOrder_probability (event : Completed → Bool) :
    (((completedOrder (t := t) clauses rows repeats hn hbranch hrows δ).filter event).length : ℝ) /
        (completedOrder (t := t) clauses rows repeats hn hbranch hrows δ).length =
      (C).game.occurrences.probability event := by
  have hcard : Fintype.card (PreliminarySampler.Questions branch n t m) =
      m ^ locationCount := by
    rw [Fintype.card_congr (SourceQuestionOrder.questionTupleEquiv branch n t m)]
    simp only [Fintype.card_fun, Fintype.card_fin]
  rw [completedOrder_filter_length (t := t) clauses rows repeats hn hbranch hrows δ event,
    Nat.cast_sum, completedOrder_length (t := t) clauses rows repeats hn hbranch hrows δ,
    Nat.cast_mul,
    CompletedSignedLaw.probability_schedule (t := t) clauses rows repeats hn hbranch hrows δ event]
  simp only [FiniteDistribution.expectation, PreliminarySampler.questionsLaw,
    FiniteDistribution.uniform, SignedCompletionSchedule.schedule_length]
  rw [← Finset.mul_sum, ← Finset.sum_div, hcard]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end
end PerfectCompleteness.CompletedOccurrenceOrder

end

end OAI
