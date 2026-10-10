import OAI.Computability.PerfectCompleteness.Foundations.DualQuotientRowsLemmas
import OAI.Computability.PerfectCompleteness.Reduction.HierarchicalFixedAdviceFamilyLemmas

namespace OAI

section

namespace PerfectCompleteness.PreliminaryLevelPair

open PreliminarySampler PreliminaryStrategy CandidateCoupling
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

variable {v m n t : Nat} {branch rows repeats : Nat → Nat}

def win (clauses : Fin m → SourceClause.NormalizedClause v)
    (strategy : Strategy clauses branch n t rows repeats)
    (level : Fin n) (e : Shared clauses branch n t rows) : Bool :=
  observe clauses (extend clauses branch n t rows repeats strategy)
    e.1 e.2.1 ⟨level, e.2.2 level⟩

theorem success_eq_mean [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1))
    (strategy : Strategy clauses branch n t rows repeats) :
    (game clauses branch n t rows repeats hn hbranch hrows).success strategy =
      𝔼 level : Fin n,
        (sharedLaw clauses rows repeats hbranch hrows).probability
          (win clauses strategy level) := by
  rw [success_eq_shared_candidate_mean clauses branch n t rows repeats
    hn hbranch hrows strategy]
  simp only [candidateFraction, expectation_div, SmallBias.expectation_sum,
    Fintype.expect_eq_sum_div_card, Fintype.card_fin]
  congr 1
  apply Finset.sum_congr rfl
  intro level _
  exact (probability_eq_expectation _ (win clauses strategy level)).symm

theorem exists_pair [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1))
    (strategy : Strategy clauses branch n t rows repeats)
    {ε : ℝ} (hε : 0 < ε) (hsize : 4 ≤ (n : ℝ) * ε)
    (hsuccess : ε ≤
      (game clauses branch n t rows repeats hn hbranch hrows).success strategy) :
    ∃ i j : Fin n, i < j ∧ ε ^ 2 / 2 ≤
      (sharedLaw clauses rows repeats hbranch hrows).probability
        (fun e => win clauses strategy i e && win clauses strategy j e) := by
  apply LevelPairCounting.exists_level_pair
    (sharedLaw clauses rows repeats hbranch hrows) (win clauses strategy) ε hε
  · rwa [success_eq_mean clauses hn hbranch hrows strategy] at hsuccess
  · exact hsize

end
end PerfectCompleteness.PreliminaryLevelPair

end

end OAI
