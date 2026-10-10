import OAI.Computability.PerfectCompleteness.Foundations.DependentPredictionDifferenceLemmas
import OAI.Computability.PerfectCompleteness.Sampling.StoppedSharedSampler

namespace OAI

section

namespace PerfectCompleteness.StoppedSharedLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open PreliminarySampler StoppedSharedSampler
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

private theorem expectation_mixture {E X : Type*} [Fintype E] [Fintype X]
    (μ : FiniteDistribution E) (ν : E → FiniteDistribution X) (f : X → ℝ) :
    (μ.mixture ν).expectation f =
      μ.expectation (fun e => (ν e).expectation f) := by
  simp only [FiniteDistribution.expectation, FiniteDistribution.mixture,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

variable {v m n t cut : Nat} {branch : Nat → Nat}

private theorem conditional_expectation
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hcut : cut + 1 ≤ n)
    (hrows : ∀ k, 0 < rows (k + 1))
    (q : Questions branch n t m) (leaf : Slots branch n)
    (f : Record clauses branch n t cut rows → ℝ) :
    (CandidateCoupling.conditionalSharedLaw clauses rows repeats hrows (q, leaf)).expectation
        (fun sample => f (forgetSuffix clauses hcut ⟨(q, leaf), sample⟩)) =
      (CanonicalDirections.law rows n hrows).expectation (fun directions =>
        (WholeArraySampler.law rows repeats (GeometricPath.leafPath leaf)
          (sourceSlots clauses (endpoints q))).expectation (fun arrays =>
            f ⟨(q, ((GeometricCutSplit.splitEquiv hcut leaf).1, directions)), arrays⟩)) := by
  rw [CandidateCoupling.conditionalSharedLaw, FiniteDistribution.expectation_product]
  calc
    _ = (WholeArraySampler.law rows repeats (GeometricPath.leafPath leaf)
        (sourceSlots clauses (endpoints q))).expectation (fun arrays =>
          (CanonicalDirections.law rows n hrows).expectation (fun directions =>
            f ⟨(q, ((GeometricCutSplit.splitEquiv hcut leaf).1, directions)), arrays⟩)) := by
      apply FiniteDistribution.expectation_congr
      intro arrays
      change (CandidateCoupling.directionsLaw leaf hrows).expectation
          (fun directions => f ⟨(q, ((GeometricCutSplit.splitEquiv hcut leaf).1,
            (CanonicalDirections.tupleEquiv rows leaf).symm directions)), arrays⟩) = _
      rw [← FiniteDistribution.expectation_pushforward
        (CandidateCoupling.directionsLaw leaf hrows)
        (CanonicalDirections.tupleEquiv rows leaf).symm
        (fun directions =>
          f ⟨(q, ((GeometricCutSplit.splitEquiv hcut leaf).1, directions)), arrays⟩),
        CanonicalDirections.directionsLaw_toCanonical]
    _ = _ := FiniteDistribution.expectation_comm _ _ _

theorem originalLaw_expectation_eq_averagedLaw [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hcut : cut + 1 ≤ n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (f : Record clauses branch n t cut rows → ℝ) :
    (originalLaw clauses rows repeats hcut hbranch hrows).expectation f =
      (averagedLaw clauses rows repeats hcut hbranch hrows).expectation f := by
  rw [originalLaw, FiniteDistribution.expectation_pushforward,
    CandidateCoupling.sharedLaw, CandidateCoupling.expectation_sigmaLaw,
    averagedLaw, CandidateCoupling.expectation_sigmaLaw]
  simp only [baseLaw, contextLaw, FiniteDistribution.expectation_product,
    CutContinuationAveraging.originalArrayLaw, expectation_mixture]
  apply FiniteDistribution.expectation_congr
  intro q
  let value (pref : GeometricCutSplit.Prefix branch n (cut + 1))
      (suffix : Slots branch (cut + 1)) (directions : CanonicalDirections.Tuple rows n) : ℝ :=
    (WholeArraySampler.law rows repeats
      ((GeometricCutSplit.prefixPath hcut pref).append (GeometricPath.leafPath suffix))
      (sourceSlots clauses (endpoints q))).expectation (fun arrays =>
        f ⟨(q, (pref, directions)), arrays⟩)
  calc
    _ = (GeometricPath.law n hbranch).expectation (fun leaf =>
        (CanonicalDirections.law rows n hrows).expectation (fun directions =>
          value (GeometricCutSplit.splitEquiv hcut leaf).1
            (GeometricCutSplit.splitEquiv hcut leaf).2 directions)) := by
      apply FiniteDistribution.expectation_congr
      intro leaf
      rw [conditional_expectation clauses rows repeats hcut hrows q leaf f]
      apply FiniteDistribution.expectation_congr
      intro directions
      dsimp only [value]
      rw [GeometricCutSplit.leafPath_split]
    _ = (GeometricCutSplit.prefixLaw hcut hbranch).expectation (fun pref =>
        (GeometricPath.law (cut + 1)
          (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hcut))).expectation (fun suffix =>
            (CanonicalDirections.law rows n hrows).expectation (value pref suffix))) :=
      GeometricCutSplit.expectation_split hcut hbranch
        (fun pref suffix => (CanonicalDirections.law rows n hrows).expectation
          (value pref suffix))
    _ = _ := by
      apply FiniteDistribution.expectation_congr
      intro pref
      exact FiniteDistribution.expectation_comm _ _ (value pref)

theorem originalLaw_eq_averagedLaw [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hcut : cut + 1 ≤ n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) :
    originalLaw (t := t) clauses rows repeats hcut hbranch hrows =
      averagedLaw clauses rows repeats hcut hbranch hrows := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [CandidateCoupling.probability_eq_expectation,
    CandidateCoupling.probability_eq_expectation]
  exact originalLaw_expectation_eq_averagedLaw clauses rows repeats hcut hbranch hrows
    (fun record => if event record then 1 else 0)

end
end PerfectCompleteness.StoppedSharedLaw

end

end OAI
