import OAI.Computability.PerfectCompleteness.Foundations.OriginalWholeCutComparison
import OAI.Computability.PerfectCompleteness.Foundations.StoppedSharedEvents
import OAI.Computability.PerfectCompleteness.Sampling.StoppedSharedLaw

namespace OAI

section

namespace PerfectCompleteness.StoppedSharedComparison

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open StoppedSharedSampler
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {v m n t cut : Nat} {branch rows repeats : Nat → Nat}

def error (branch rows repeats : Nat → Nat) (n cut t : Nat) : ℝ :=
  Real.sqrt ((ChildBlockCardinality.bound branch cut t
    (OriginalCutCalls.count rows repeats n (cut + 1)) rows : ℝ) ^ 2 / branch cut) / 2

theorem observed_totalVariation_le [NeZero m] {Γ : Type*} [Fintype Γ]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hcut : cut + 1 ≤ n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (observe : Record clauses branch n t cut rows → Γ) :
    ((originalLaw clauses rows repeats hcut hbranch hrows).pushforward observe).totalVariation
      ((stoppedLaw clauses rows repeats hcut hbranch hrows).pushforward observe) ≤
      error branch rows repeats n cut t := by
  rw [StoppedSharedLaw.originalLaw_eq_averagedLaw]
  exact OriginalWholeCutComparison.conditional_observed_totalVariation_le rows repeats
    (fun context : Context branch n t m cut rows =>
      GeometricCutSplit.prefixPath hcut context.2.1)
    (fun context => sourceSlots clauses (PreliminarySampler.endpoints context.1))
    (contextLaw hcut hbranch hrows)
    (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hcut)) observe

theorem totalVariation_le [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hcut : cut + 1 ≤ n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) :
    (originalLaw (t := t) clauses rows repeats hcut hbranch hrows).totalVariation
      (stoppedLaw (t := t) clauses rows repeats hcut hbranch hrows) ≤
      error branch rows repeats n cut t := by
  simpa only [FiniteDistribution.pushforward_id] using
    observed_totalVariation_le clauses rows repeats hcut hbranch hrows
      (id : Record clauses branch n t cut rows → Record clauses branch n t cut rows)

theorem pair_probability_transfer [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (strategy : PreliminaryStrategy.Strategy clauses branch n t rows repeats)
    (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) (i j : Fin n)
    (hi : cut + 1 ≤ i.val + 1) (hj : cut + 1 ≤ j.val + 1) :
    (CandidateCoupling.sharedLaw clauses rows repeats hbranch hrows).probability
        (fun sample => PreliminaryLevelPair.win clauses strategy i sample &&
          PreliminaryLevelPair.win clauses strategy j sample) ≤
      (stoppedLaw clauses rows repeats hcut hbranch hrows).probability
        (StoppedSharedEvents.pair clauses strategy hcut hbranch i j) +
          error branch rows repeats n cut t := by
  have h := FiniteDistribution.probability_le_add_totalVariation
    (originalLaw clauses rows repeats hcut hbranch hrows)
    (stoppedLaw clauses rows repeats hcut hbranch hrows)
    (StoppedSharedEvents.pair clauses strategy hcut hbranch i j)
  rw [StoppedSharedEvents.original_pair_probability clauses strategy hcut hbranch hrows i j hi hj] at h
  exact h.trans (add_le_add le_rfl
    (totalVariation_le (t := t) clauses rows repeats hcut hbranch hrows))

theorem pair_probability_lower [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (strategy : PreliminaryStrategy.Strategy clauses branch n t rows repeats)
    (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) (i j : Fin n)
    (hi : cut + 1 ≤ i.val + 1) (hj : cut + 1 ≤ j.val + 1)
    {mass : ℝ} (hmass : mass ≤
      (CandidateCoupling.sharedLaw clauses rows repeats hbranch hrows).probability
        (fun sample => PreliminaryLevelPair.win clauses strategy i sample &&
          PreliminaryLevelPair.win clauses strategy j sample)) :
    mass - error branch rows repeats n cut t ≤
      (stoppedLaw clauses rows repeats hcut hbranch hrows).probability
        (StoppedSharedEvents.pair clauses strategy hcut hbranch i j) := by
  have h := pair_probability_transfer clauses strategy hcut hbranch hrows i j hi hj
  linarith

end
end PerfectCompleteness.StoppedSharedComparison

end

end OAI
