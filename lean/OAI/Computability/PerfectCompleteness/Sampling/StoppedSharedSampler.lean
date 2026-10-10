import OAI.Computability.PerfectCompleteness.Foundations.CanonicalDirections
import OAI.Computability.PerfectCompleteness.Foundations.CutContinuationAveraging
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalFrozenTablesLemmas

namespace OAI

section

namespace PerfectCompleteness.StoppedSharedSampler

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open PreliminarySampler
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {v m n t cut : Nat} {branch rows repeats : Nat → Nat}

abbrev Context (branch : Nat → Nat) (n t m cut : Nat) (rows : Nat → Nat) :=
  Questions branch n t m ×
    (GeometricCutSplit.Prefix branch n (cut + 1) × CanonicalDirections.Tuple rows n)

abbrev Record (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t cut : Nat) (rows : Nat → Nat) :=
  (context : Context branch n t m cut rows) ×
    Arrays (sourceSlots clauses (endpoints context.1)) rows

def contextLaw [NeZero m] (hcut : cut + 1 ≤ n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) :
    FiniteDistribution (Context branch n t m cut rows) :=
  questionsLaw.product ((GeometricCutSplit.prefixLaw hcut hbranch).product
    (CanonicalDirections.law rows n hrows))

def forgetSuffix (clauses : Fin m → SourceClause.NormalizedClause v)
    (hcut : cut + 1 ≤ n)
    (sample : CandidateCoupling.Shared clauses branch n t rows) :
    Record clauses branch n t cut rows :=
  ⟨(sample.1.1, ((GeometricCutSplit.splitEquiv hcut sample.1.2).1,
    (CanonicalDirections.tupleEquiv rows sample.1.2).symm sample.2.2)), sample.2.1⟩

def originalLaw [NeZero m] (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hcut : cut + 1 ≤ n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) :
    FiniteDistribution (Record clauses branch n t cut rows) :=
  (CandidateCoupling.sharedLaw clauses rows repeats hbranch hrows).pushforward
    (forgetSuffix clauses hcut)

def stoppedLaw [NeZero m] (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hcut : cut + 1 ≤ n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) :
    FiniteDistribution (Record clauses branch n t cut rows) :=
  CompletionSoundness.sigmaLaw (contextLaw hcut hbranch hrows) (fun context =>
    WholeArraySampler.law rows repeats (GeometricCutSplit.prefixPath hcut context.2.1)
      (sourceSlots clauses (endpoints context.1)))

def averagedLaw [NeZero m] (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hcut : cut + 1 ≤ n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) :
    FiniteDistribution (Record clauses branch n t cut rows) :=
  CompletionSoundness.sigmaLaw (contextLaw hcut hbranch hrows) (fun context =>
    CutContinuationAveraging.originalArrayLaw rows repeats
      (GeometricCutSplit.prefixPath hcut context.2.1)
      (sourceSlots clauses (endpoints context.1))
      (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hcut)))

end
end PerfectCompleteness.StoppedSharedSampler

end

end OAI
