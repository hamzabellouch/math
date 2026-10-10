import OAI.Computability.PerfectCompleteness.Foundations.RecursiveSpaces
import OAI.Computability.PerfectCompleteness.Repetition.CleanCountingLemmas
import OAI.Computability.PerfectCompleteness.Repetition.RepetitionRateLemmas

namespace OAI


namespace PerfectCompleteness.DesignatedLeaves

open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {height : Nat}
  (designated : Fin (branch height) → Slots branch height)
  (clean : Fin (branch height) → Prop)

def selected (leaf : Slots branch (height + 1)) : Prop :=
  clean leaf.1 ∧ leaf.2 = designated leaf.1

abbrev Children := {i : Fin (branch height) // clean i}
abbrev Leaves := {leaf : Slots branch (height + 1) // selected designated clean leaf}

def equiv : Children clean ≃ Leaves designated clean where
  toFun i := ⟨(i.val, designated i.val), i.property, rfl⟩
  invFun leaf := ⟨leaf.val.1, leaf.property.1⟩
  left_inv i := rfl
  right_inv leaf := by
    apply Subtype.ext
    exact Prod.ext rfl leaf.property.2.symm

@[simp] theorem equiv_apply (i : Children clean) :
    (equiv designated clean i).val = (i.val, designated i.val) := rfl

@[simp] theorem equiv_symm_apply (leaf : Leaves designated clean) :
    (equiv designated clean).symm leaf = ⟨leaf.val.1, leaf.property.1⟩ := rfl

theorem card_leaves : Fintype.card (Leaves designated clean) = Fintype.card (Children clean) :=
  (Fintype.card_congr (equiv designated clean)).symm


variable {E Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype E] [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
  (strategy : Strategy (Leaves designated clean → Q₁) (Leaves designated clean → Q₂)
    (Leaves designated clean → A₁) (Leaves designated clean → A₂))

def childStrategy :
    Strategy (Children clean → Q₁) (Children clean → Q₂)
      (Children clean → A₁) (Children clean → A₂) :=
  IndexedRepetition.reindexStrategy (equiv designated clean) strategy

theorem wins_eq (occurrences : Children clean → E) :
    (IndexedRepetition.game G (Children clean)).wins
      (childStrategy designated clean strategy) occurrences =
    (IndexedRepetition.game G (Leaves designated clean)).wins strategy
      (occurrences ∘ (equiv designated clean).symm) := by
  apply Bool.eq_iff_iff.mpr
  change (decide (∀ i : Children clean,
      G.accepts (occurrences i)
        (strategy.1 ((fun i => G.left (occurrences i)) ∘ (equiv designated clean).symm)
          (equiv designated clean i))
        (strategy.2 ((fun i => G.right (occurrences i)) ∘ (equiv designated clean).symm)
          (equiv designated clean i)) = true) = true) ↔
    (decide (∀ leaf : Leaves designated clean,
      G.accepts (occurrences ((equiv designated clean).symm leaf))
        (strategy.1 (fun leaf => G.left (occurrences ((equiv designated clean).symm leaf))) leaf)
        (strategy.2 (fun leaf => G.right (occurrences ((equiv designated clean).symm leaf))) leaf)
        = true) = true)
  simp only [decide_eq_true_eq, Function.comp_def]
  constructor
  · intro h leaf
    simpa only [Equiv.apply_symm_apply] using h ((equiv designated clean).symm leaf)
  · intro h i
    simpa only [Equiv.symm_apply_apply] using h (equiv designated clean i)

theorem occurrence_law :
    (IndexedRepetition.game G (Leaves designated clean)).occurrences.pushforward
        (fun x => x ∘ equiv designated clean) =
      (IndexedRepetition.game G (Children clean)).occurrences :=
  IndexedRepetition.reindex_law G.occurrences (equiv designated clean)

theorem success_eq :
    (IndexedRepetition.game G (Children clean)).success (childStrategy designated clean strategy) =
      (IndexedRepetition.game G (Leaves designated clean)).success strategy :=
  IndexedRepetition.reindex_success G (equiv designated clean) strategy


end
end PerfectCompleteness.DesignatedLeaves



namespace PerfectCompleteness.FiniteConditioningBounds

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct

noncomputable section

variable {Ω : Type*} [Fintype Ω]

theorem condition_probability_mono_on (P : FiniteDistribution Ω)
    (given event target : Ω → Bool) (positive : 0 < P.probability given)
    (inclusion : ∀ x, given x = true → event x = true → target x = true) :
    (P.condition given positive).probability event ≤
      (P.condition given positive).probability target := by
  rw [FiniteDistribution.probability_condition, FiniteDistribution.probability_condition]
  apply div_le_div_of_nonneg_right _ positive.le
  apply P.probability_mono
  intro x hx
  have hx' : given x = true ∧ event x = true := by simpa using hx
  simpa using And.intro hx'.1 (inclusion x hx'.1 hx'.2)

theorem sum_record_inter {R : Type*} [Fintype R] [DecidableEq R]
    (P : FiniteDistribution Ω) (record : Ω → R) (event : Ω → Bool) :
    (∑ r : R, P.probability (fun x => decide (record x = r) && event x)) =
      P.probability event := by
  unfold FiniteDistribution.probability
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  cases he : event x <;> simp [he]

theorem sum_record_weight {R : Type*} [Fintype R] [DecidableEq R]
    (P : FiniteDistribution Ω) (record : Ω → R) (bound : R → ℝ) :
    (∑ r : R, P.probability (fun x => decide (record x = r)) * bound r) =
      P.expectation (fun x => bound (record x)) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

theorem probability_le_record_bound {R : Type*} [Fintype R] [DecidableEq R]
    (P : FiniteDistribution Ω) (record : Ω → R) (event : Ω → Bool)
    (bound : R → ℝ)
    (conditional : ∀ r (positive : 0 < P.probability (fun x => decide (record x = r))),
      (P.condition (fun x => decide (record x = r)) positive).probability event ≤ bound r) :
    P.probability event ≤ P.expectation (fun x => bound (record x)) := by
  rw [← sum_record_inter P record event, ← sum_record_weight P record bound]
  apply Finset.sum_le_sum
  intro r _
  by_cases positive : 0 < P.probability (fun x => decide (record x = r))
  · rw [P.probability_inter_eq_mul_conditional _ _ positive]
    exact mul_le_mul_of_nonneg_left (conditional r positive) (P.probability_nonnegative _)
  · have zero : P.probability (fun x => decide (record x = r)) = 0 :=
      le_antisymm (le_of_not_gt positive) (P.probability_nonnegative _)
    rw [P.probability_and_eq_zero_of_probability_eq_zero _ _ zero, zero, zero_mul]

section Game

variable {E Q₁ Q₂ A₁ A₂ I : Type*}
  [Fintype E] [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype I] [DecidableEq I] [Nonempty A₁] [Nonempty A₂]

theorem conditioned_source_success (P : FiniteDistribution Ω)
    (given event : Ω → Bool) (positive : 0 < P.probability given)
    (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) (source : Ω → I → E)
    (source_law : (P.condition given positive).pushforward source =
      law (fun _ : I => G.occurrences))
    (strategy : Strategy (I → Q₁) (I → Q₂) (I → A₁) (I → A₂))
    (inclusion : ∀ x, given x = true → event x = true →
      (IndexedRepetition.game G I).wins strategy (source x) = true) :
    (P.condition given positive).probability event ≤
      (G.repetition (Fintype.card I)).value := by
  have hsource := congrArg
    (fun D : FiniteDistribution (I → E) =>
      D.probability ((IndexedRepetition.game G I).wins strategy)) source_law
  rw [FiniteDistribution.probability_pushforward] at hsource
  calc
    _ ≤ (P.condition given positive).probability
        (fun x => (IndexedRepetition.game G I).wins strategy (source x)) :=
      condition_probability_mono_on P given event _ positive inclusion
    _ = (IndexedRepetition.game G I).success strategy := hsource
    _ ≤ _ := IndexedRepetition.success_le_repetition_value G strategy

end Game

theorem independent_clean_bound {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, Fintype (A i)]
    {R : Type*} [Fintype R] [DecidableEq R]
    (P : (i : I) → FiniteDistribution (A i))
    (clean : (i : I) → A i → Bool) (record : ((i : I) → A i) → R)
    (count : R → Nat)
    (count_eq : ∀ x, count (record x) = CleanCounting.cleanCount clean x)
    (event : ((i : I) → A i) → Bool) (a : ℝ)
    (conditional : ∀ r (positive : 0 <
      (law P).probability (fun x => decide (record x = r))),
      ((law P).condition (fun x => decide (record x = r)) positive).probability event ≤
        a ^ count r) :
    (law P).probability event ≤
      ∏ i : I, (1 - (1 - a) * (P i).probability (clean i)) := by
  calc
    _ ≤ (law P).expectation (fun x => a ^ count (record x)) :=
      probability_le_record_bound (law P) record event (fun r => a ^ count r) conditional
    _ = (law P).expectation (fun x => a ^ CleanCounting.cleanCount clean x) := by
      apply FiniteDistribution.expectation_congr
      intro x
      rw [count_eq]
    _ = _ := CleanCounting.cleanCount_moment P clean a

end
end PerfectCompleteness.FiniteConditioningBounds

end OAI
