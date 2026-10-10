import OAI.Computability.PerfectCompleteness.Foundations.OddLists
import OAI.Computability.PerfectCompleteness.Foundations.RecursiveSpaceEquivLemmas
import OAI.Computability.PerfectCompleteness.Repetition.RepetitionRateLemmas
import OAI.Computability.PerfectCompleteness.Sampling.FiniteListSampling

namespace OAI

section

namespace PerfectCompleteness.OddListGame

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open OddLists FiniteListSampling

noncomputable section

variable {E Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype E] [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] [DecidableEq A₁] [DecidableEq A₂]

def base (μ : FiniteDistribution E) (left : E → Q₁) (right : E → Q₂)
    (projection : E → A₁ → A₂) : OccurrenceGame E Q₁ Q₂ A₁ A₂ :=
  OccurrenceGame.ofProjection μ left right projection

def game (s : Nat) (μ : FiniteDistribution E) (left : E → Q₁) (right : E → Q₂)
    (projection : E → A₁ → A₂) :
    OccurrenceGame E Q₁ Q₂ (OddList s A₁) (OddList s A₂) :=
  OccurrenceGame.ofProjection μ left right (fun e => OddList.map (projection e))

def responses {Q A : Type*} [Fintype A] [DecidableEq A] {s : Nat}
    (lists : Q → OddList s A) (q : Q) : FiniteDistribution A :=
  uniformList (lists q).val (lists q).nonempty

omit [DecidableEq Q₁] [DecidableEq Q₂] [DecidableEq A₁] in
theorem accepted_pair {s : Nat} (μ : FiniteDistribution E)
    (left : E → Q₁) (right : E → Q₂) (projection : E → A₁ → A₂)
    (strategy : Strategy Q₁ Q₂ (OddList s A₁) (OddList s A₂)) (e : E)
    (accepted : (game s μ left right projection).wins strategy e = true) :
    ∃ a ∈ (strategy.1 (left e)).val, ∃ b ∈ (strategy.2 (right e)).val,
      (base μ left right projection).accepts e a b = true := by
  have hmap : OddList.map (projection e) (strategy.1 (left e)) = strategy.2 (right e) := by
    simpa only [game, OccurrenceGame.wins, OccurrenceGame.ofProjection, decide_eq_true_eq]
      using accepted
  obtain ⟨a, ha, b, hb, hab⟩ := OddList.exists_accepting_pair_of_eq
    (projection e) (strategy.1 (left e)) (strategy.2 (right e)) hmap
  exact ⟨a, ha, b, hb, by simpa [base, OccurrenceGame.ofProjection] using hab⟩

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem success_le_randomized {s : Nat} [NeZero s] (μ : FiniteDistribution E)
    (left : E → Q₁) (right : E → Q₂) (projection : E → A₁ → A₂)
    (strategy : Strategy Q₁ Q₂ (OddList s A₁) (OddList s A₂)) :
    (game s μ left right projection).success strategy ≤
      (s : ℝ) ^ 2 * (base μ left right projection).stochasticSuccess
        (responses strategy.1) (responses strategy.2) := by
  let G := base μ left right projection
  let pair := fun e => pairAcceptance (responses strategy.1 (left e))
    (responses strategy.2 (right e)) (G.accepts e)
  have hs : 0 < (s : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr (Nat.pos_of_neZero s)) 2
  have hpoint (e : E) :
      (if (game s μ left right projection).wins strategy e then (1 : ℝ) else 0) ≤
        (s : ℝ) ^ 2 * pair e := by
    by_cases hwin : (game s μ left right projection).wins strategy e = true
    · simp only [hwin, ite_true]
      have h := bounded_uniform_pair_lower
        (strategy.1 (left e)).val (strategy.2 (right e)).val
        (strategy.1 (left e)).nonempty (strategy.2 (right e)).nonempty s
        (strategy.1 (left e)).card_le (strategy.2 (right e)).card_le (G.accepts e)
        (accepted_pair μ left right projection strategy e hwin)
      have hscaled := (div_le_iff₀ hs).mp h
      change 1 ≤ (s : ℝ) ^ 2 *
        pairAcceptance (uniformList (strategy.1 (left e)).val (strategy.1 (left e)).nonempty)
          (uniformList (strategy.2 (right e)).val (strategy.2 (right e)).nonempty) (G.accepts e)
      exact hscaled.trans_eq (mul_comm _ _)
    · simp only [hwin]
      exact mul_nonneg (sq_nonneg _) (pairAcceptance_nonnegative _ _ _)
  have hpair : μ.expectation pair = G.stochasticSuccess
      (responses strategy.1) (responses strategy.2) := by
    unfold OccurrenceGame.stochasticSuccess
    apply FiniteDistribution.expectation_congr
    intro e
    exact pairAcceptance_eq_expectation _ _ _
  calc
    _ = μ.expectation
        (fun e => if (game s μ left right projection).wins strategy e then 1 else 0) :=
      (game s μ left right projection).success_eq_occurrence_expectation strategy
    _ ≤ μ.expectation (fun e => (s : ℝ) ^ 2 * pair e) :=
      SmallBias.expectation_mono μ hpoint
    _ = (s : ℝ) ^ 2 * μ.expectation pair := by
      simp only [FiniteDistribution.expectation, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = _ := by rw [hpair]

theorem value_le {s : Nat} [NeZero s] [Nonempty A₁] [Nonempty A₂]
    (μ : FiniteDistribution E) (left : E → Q₁) (right : E → Q₂)
    (projection : E → A₁ → A₂) :
    (game s μ left right projection).value ≤
      (s : ℝ) ^ 2 * (base μ left right projection).value := by
  apply ((game s μ left right projection).value_le_iff _).mpr
  intro strategy
  exact (success_le_randomized μ left right projection strategy).trans
    (mul_le_mul_of_nonneg_left
      ((base μ left right projection).stochasticSuccess_le_value
        (responses strategy.1) (responses strategy.2)) (sq_nonneg _))

omit [DecidableEq Q₁] [DecidableEq Q₂] [DecidableEq A₁] in
theorem endpointDetermined {s : Nat} (μ : FiniteDistribution E)
    (left : E → Q₁) (right : E → Q₂) (projection : E → A₁ → A₂)
    (determined : (base μ left right projection).EndpointDetermined) :
    (game s μ left right projection).EndpointDetermined := by
  intro e e' hl hr L R
  have hprojection : projection e = projection e' := by
    funext a
    have h := determined e e' hl hr a (projection e a)
    have htrue : (base μ left right projection).accepts e' a (projection e a) = true := by
      rw [← h]
      simp [base, OccurrenceGame.ofProjection]
    have heq : projection e' a = projection e a := by
      simpa only [base, OccurrenceGame.ofProjection, decide_eq_true_eq] using htrue
    exact heq.symm
  simp only [game, OccurrenceGame.ofProjection, hprojection]
  by_cases h : OddList.map (projection e') L = R <;> simp only [h, decide_true, decide_false]

theorem repetition_halfRate {s L : Nat} [NeZero s] [Nonempty A₁] [Nonempty A₂]
    (μ : FiniteDistribution E) (left : E → Q₁) (right : E → Q₂)
    (projection : E → A₁ → A₂)
    (determined : (base μ left right projection).EndpointDetermined)
    (gap : (s : ℝ) ^ 2 * (base μ left right projection).value ≤ 1 / 2)
    (hL : 0 < L)
    (alphabet : UniqueGamesTheorem.Foundations.Repetition.logTwo
      ((Fintype.card (OddList s A₁) : ℝ) * (Fintype.card (OddList s A₂) : ℝ)) ≤ L)
    (n : Nat) :
    ((game s μ left right projection).repetition n).value ≤
      (RepetitionRate.halfRate L : ℝ) ^ n := by
  exact RepetitionRate.occurrence_repetition_halfRate (game s μ left right projection)
    ((game s μ left right projection).presentationOfDetermined
      (endpointDetermined μ left right projection determined)) hL alphabet
    ((value_le μ left right projection).trans gap) n

end
end PerfectCompleteness.OddListGame

end

end OAI
