import OAI.Computability.PerfectCompleteness.Sampling.StoppedSharedSampler

namespace OAI

section

namespace PerfectCompleteness.StoppedSharedEvents

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open StoppedSharedSampler
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {v m n t cut : Nat} {branch rows repeats : Nat → Nat}

def referenceSuffix (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k) :
    Slots branch (cut + 1) :=
  Classical.choice (GeometricPath.slots_nonempty (cut + 1)
    (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hcut)))

def representativeLeaf (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k)
    (context : Context branch n t m cut rows) : Slots branch n :=
  (GeometricCutSplit.prefixPath hcut context.2.1).slotEmbedding (referenceSuffix hcut hbranch)

def win (clauses : Fin m → SourceClause.NormalizedClause v)
    (strategy : PreliminaryStrategy.Strategy clauses branch n t rows repeats)
    (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k)
    (level : Fin n) (record : Record clauses branch n t cut rows) : Bool :=
  PreliminaryStrategy.observe clauses
    (PreliminaryStrategy.extend clauses branch n t rows repeats strategy)
    (record.1.1, representativeLeaf hcut hbranch record.1) record.2
    (PrefixTests.choiceAt rows (representativeLeaf hcut hbranch record.1) level
      (record.1.2.2 level))

theorem actual_win_eq (clauses : Fin m → SourceClause.NormalizedClause v)
    (strategy : PreliminaryStrategy.Strategy clauses branch n t rows repeats)
    (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k)
    (level : Fin n) (hlevel : cut + 1 ≤ level.val + 1)
    (sample : CandidateCoupling.Shared clauses branch n t rows) :
    PreliminaryLevelPair.win clauses strategy level sample =
      win clauses strategy hcut hbranch level (forgetSuffix clauses hcut sample) := by
  rw [CanonicalDirections.win_eq_observe]
  have h := PrefixTests.observe_above_cut_eq clauses
    (PreliminaryStrategy.extend clauses branch n t rows repeats strategy)
    sample.1.1 sample.2.1
    (GeometricCutSplit.prefixPath hcut (GeometricCutSplit.splitEquiv hcut sample.1.2).1)
    level hlevel (GeometricCutSplit.splitEquiv hcut sample.1.2).2
    (referenceSuffix hcut hbranch)
    ((CanonicalDirections.tupleEquiv rows sample.1.2).symm sample.2.2 level)
  rw [GeometricCutSplit.split_embedding_eq] at h
  exact h

def pair (clauses : Fin m → SourceClause.NormalizedClause v)
    (strategy : PreliminaryStrategy.Strategy clauses branch n t rows repeats)
    (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k) (i j : Fin n)
    (record : Record clauses branch n t cut rows) : Bool :=
  win clauses strategy hcut hbranch i record && win clauses strategy hcut hbranch j record

theorem original_pair_probability [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (strategy : PreliminaryStrategy.Strategy clauses branch n t rows repeats)
    (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) (i j : Fin n)
    (hi : cut + 1 ≤ i.val + 1) (hj : cut + 1 ≤ j.val + 1) :
    (originalLaw clauses rows repeats hcut hbranch hrows).probability
        (pair clauses strategy hcut hbranch i j) =
      (CandidateCoupling.sharedLaw clauses rows repeats hbranch hrows).probability
        (fun sample => PreliminaryLevelPair.win clauses strategy i sample &&
          PreliminaryLevelPair.win clauses strategy j sample) := by
  rw [originalLaw, FiniteDistribution.probability_pushforward]
  apply congrArg (CandidateCoupling.sharedLaw clauses rows repeats hbranch hrows).probability
  funext sample
  exact (congrArg₂ Bool.and
    (actual_win_eq clauses strategy hcut hbranch i hi sample)
    (actual_win_eq clauses strategy hcut hbranch j hj sample)).symm

end
end PerfectCompleteness.StoppedSharedEvents

end

end OAI
