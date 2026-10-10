import OAI.Computability.PerfectCompleteness.Foundations.StoppedProjectedPhysicalAdvice

namespace OAI

section

namespace PerfectCompleteness.StoppedPhysicalPrefixSwap

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
attribute [local instance] linearMapFintype
attribute [local instance] StoppedProjectedPhysicalAdvice.adviceFintype
  StoppedProjectedPhysicalAdvice.physicalAdviceFintype

variable {branch : Nat → Nat} {n i j t v m : Nat} [NeZero m]
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)
  (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)

omit [NeZero m] in
theorem fiber_expectation
    (o : StoppedProjectedPhysicalAdvice.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m)) (r : Nat)
    (F : StoppedProjectedPhysicalAdvice.Sample
      clauses rows repeats hupper hij designated r → ℝ) :
    (StoppedProjectedExperiment.physicalLaw clauses rows repeats hupper hij designated
      (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag o).expectation
        (fun sample => (FiniteDistribution.uniform
          (StoppedProjectedPhysicalAdvice.Advice rows hupper o r)).expectation
            (fun A => F ⟨o, (sample, A)⟩)) =
      (GeometricCutSplit.prefixLaw (Nat.succ_le_succ hij.le)
        (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper))).expectation
          (fun lower => (FiniteDistribution.uniform
            (StoppedProjectedPhysicalAdvice.Advice rows hupper o r)).expectation
              (fun A => (CanonicalDirections.law rows n hrows).expectation
                (fun directions => (SourceProjectedTag.positionLaw
                  (branch := branch) (n := i) (t := t)).expectation
                    (fun positions => (StoppedProjectedExperiment.physicalFiberLaw
                      clauses rows repeats hupper hij designated flag o
                        (lower, (positions, directions))).expectation
                          (fun raw => F ⟨o, (⟨(lower, (positions, directions)), raw⟩, A)⟩))))) := by
  rw [FiniteDistribution.expectation_comm]
  simp only [StoppedProjectedExperiment.physicalLaw, CandidateCoupling.expectation_sigmaLaw,
    StoppedProjectedExperiment.physicalBaseLaw, FiniteDistribution.expectation_product]
  rw [FiniteDistribution.expectation_comm]
  apply FiniteDistribution.expectation_congr
  intro lower
  apply FiniteDistribution.expectation_congr
  intro A
  exact FiniteDistribution.expectation_comm _ _ _

theorem expectation_prefixes (r : Nat)
    (F : StoppedProjectedPhysicalAdvice.Sample
      clauses rows repeats hupper hij designated r → ℝ) :
    (StoppedProjectedPhysicalAdvice.law clauses rows repeats hupper hij designated
      hbranch hrows flag r).expectation F =
      ((GeometricCutSplit.prefixLaw hupper hbranch).product
        (GeometricCutSplit.prefixLaw (Nat.succ_le_succ hij.le)
          (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)))).expectation
            (fun prefixes => (PreliminarySampler.questionsLaw
              (branch := branch) (n := n) (t := t) (m := m)).expectation
                (fun Q => (FiniteDistribution.uniform
                  (StoppedProjectedPhysicalAdvice.Advice rows hupper (Q, prefixes.1) r)).expectation
                    (fun A => (CanonicalDirections.law rows n hrows).expectation
                      (fun directions => (SourceProjectedTag.positionLaw
                        (branch := branch) (n := i) (t := t)).expectation
                          (fun positions => (StoppedProjectedExperiment.physicalFiberLaw
                            clauses rows repeats hupper hij designated flag (Q, prefixes.1)
                              (prefixes.2, (positions, directions))).expectation
                                (fun raw => F ⟨(Q, prefixes.1),
                                  (⟨(prefixes.2, (positions, directions)), raw⟩, A)⟩)))))) := by
  rw [StoppedProjectedPhysicalAdvice.law, CandidateCoupling.expectation_sigmaLaw]
  simp only [StoppedProjectedExperiment.outerLaw, FiniteDistribution.expectation_product]
  simp_rw [fiber_expectation clauses rows repeats hupper hij designated hbranch hrows flag]
  rw [FiniteDistribution.expectation_comm]
  apply FiniteDistribution.expectation_congr
  intro upper
  exact FiniteDistribution.expectation_comm _ _ _

end
end PerfectCompleteness.StoppedPhysicalPrefixSwap

end

end OAI
