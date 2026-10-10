import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalAdviceExperimentLemmas
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalPairCoarse
import OAI.Computability.PerfectCompleteness.Sampling.CandidateCoupling

namespace OAI

section

namespace PerfectCompleteness.HeterogeneousPairAdvice

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

private theorem append_totalVariation {X : Type*} [Fintype X]
    {Y : X → Type*} [∀ x, Fintype (Y x)]
    (P Q : FiniteDistribution X) (kernel : (x : X) → FiniteDistribution (Y x)) :
    (CompletionSoundness.sigmaLaw P kernel).totalVariation
      (CompletionSoundness.sigmaLaw Q kernel) = P.totalVariation Q := by
  change (∑ z : Σ x, Y x,
    |P.weight z.1 * (kernel z.1).weight z.2 -
      Q.weight z.1 * (kernel z.1).weight z.2|) / 2 =
    (∑ x, |P.weight x - Q.weight x|) / 2
  congr 1
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro x _
  simp only [← sub_mul, abs_mul, abs_of_nonneg ((kernel x).nonnegative _),
    ← Finset.mul_sum, (kernel x).normalized, mul_one]

variable {branch rows : Nat → Nat} {n t : Nat} {O : Type*} [Fintype O]
  {Ω : O → Type*} [∀ o, Fintype (Ω o)]
  (S : (o : O) → HierarchicalAdviceExperiment.Experiment branch rows n t (Ω o))

local instance backgroundFintype (o : O) :
    Fintype (HierarchicalAdviceExperiment.Background (S o)) :=
  HierarchicalAdviceExperiment.backgroundFintype (S o)

local instance rowSpaceFintype (o : O) :
    Fintype (NodeEmbedding.RowSpace (S o).slots (S o).upper) :=
  HierarchicalPairCoarse.rowSpaceFintype (S o)

local instance coarseFintype (o : O) :
    Fintype (HierarchicalAdviceExperiment.Coarse (S o)) :=
  HierarchicalAdviceFamily.coarseFintype S o

local instance inputFintype (o : O)
    (background : HierarchicalAdviceExperiment.Background (S o)) :
    Fintype (HierarchicalAdviceExperiment.Input (S o) background) :=
  HierarchicalAdviceExperiment.inputFintype (S o) background

local instance inputFiniteDimensional (o : O)
    (background : HierarchicalAdviceExperiment.Background (S o)) :
    FiniteDimensional F2 (HierarchicalAdviceExperiment.Input (S o) background) :=
  HierarchicalAdviceExperiment.inputFiniteDimensional (S o) background

abbrev PairSample := Σ o : O, HierarchicalPairCoarse.PairRecord (S o)

abbrev AdviceSample (r : Nat) :=
  Σ z : PairSample S, HierarchicalAdviceExperiment.Advice (S z.1) r

def appendLaw (P : FiniteDistribution (PairSample S)) (r : Nat) :
    FiniteDistribution (AdviceSample S r) :=
  CompletionSoundness.sigmaLaw P
    (fun z => HierarchicalAdviceExperiment.adviceLaw (S z.1) r)

def observe (r : Nat) (z : AdviceSample S r) : HierarchicalAdviceFamily.Observation S r :=
  ⟨z.1.1, HierarchicalPairCoarse.observe (S z.1.1) r (z.2, z.1.2)⟩

def observedLaw (P : FiniteDistribution (PairSample S)) (r : Nat) :
    FiniteDistribution (HierarchicalAdviceFamily.Observation S r) :=
  (appendLaw S P r).pushforward (observe S r)

def referencePairLaw (outer : FiniteDistribution O)
    (backgrounds : (o : O) →
      FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (hrows : ∀ o, 0 < rows (Nodes.height (S o).upper)) :
    FiniteDistribution (PairSample S) :=
  CompletionSoundness.sigmaLaw outer (fun o =>
    HierarchicalAgreementMean.referenceLaw (S o).slots (S o).upper (backgrounds o) (hrows o))

theorem observed_sigmaLaw (outer : FiniteDistribution O)
    (P : (o : O) → FiniteDistribution (HierarchicalPairCoarse.PairRecord (S o)))
    (r : Nat) :
    observedLaw S (CompletionSoundness.sigmaLaw outer P) r =
      CompletionSoundness.sigmaLaw outer (fun o =>
        ((HierarchicalAdviceExperiment.adviceLaw (S o) r).product (P o)).pushforward
          (HierarchicalPairCoarse.observe (S o) r)) := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [observedLaw, FiniteDistribution.probability_pushforward, appendLaw,
    CompletionSoundness.sigmaLaw_probability, CandidateCoupling.expectation_sigmaLaw,
    CompletionSoundness.sigmaLaw_probability]
  apply FiniteDistribution.expectation_congr
  intro o
  rw [FiniteDistribution.probability_pushforward, UsefulAdvice.product_probability_advice_first]
  rfl

theorem reference_observe_sigmaLaw (outer : FiniteDistribution O)
    (backgrounds : (o : O) →
      FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (r : Nat) :
    (HierarchicalAdviceFamily.referenceLaw S outer backgrounds r).pushforward
        (HierarchicalAdviceFamily.referenceObserve S r) =
      CompletionSoundness.sigmaLaw outer (fun o =>
        (HierarchicalAdviceExperiment.referenceLaw (S o) (backgrounds o) r).pushforward
          (HierarchicalAdviceExperiment.referenceObserve (S o) r)) := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward,
    HierarchicalAdviceFamily.referenceLaw, HeterogeneousAdviceFamily.law,
    CompletionSoundness.sigmaLaw_probability, HierarchicalAdviceFamily.backgroundLaw,
    CandidateCoupling.expectation_sigmaLaw, CompletionSoundness.sigmaLaw_probability]
  apply FiniteDistribution.expectation_congr
  intro o
  rw [FiniteDistribution.probability_pushforward, HierarchicalAdviceExperiment.referenceLaw,
    GoodAdviceFamily.law, CompletionSoundness.sigmaLaw_probability]
  rfl

theorem reference_observe_law (outer : FiniteDistribution O)
    (backgrounds : (o : O) →
      FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (hrows : ∀ o, 0 < rows (Nodes.height (S o).upper)) (r : Nat) :
    observedLaw S (referencePairLaw S outer backgrounds hrows) r =
      (HierarchicalAdviceFamily.referenceLaw S outer backgrounds r).pushforward
        (HierarchicalAdviceFamily.referenceObserve S r) := by
  rw [referencePairLaw, observed_sigmaLaw]
  simpa only [HierarchicalPairCoarse.reference_observe_law] using
    (reference_observe_sigmaLaw S outer backgrounds r).symm

theorem appendLaw_totalVariation (P Q : FiniteDistribution (PairSample S)) (r : Nat) :
    (appendLaw S P r).totalVariation (appendLaw S Q r) = P.totalVariation Q :=
  append_totalVariation P Q (fun z => HierarchicalAdviceExperiment.adviceLaw (S z.1) r)

theorem observed_totalVariation_le (P : FiniteDistribution (PairSample S))
    (outer : FiniteDistribution O)
    (backgrounds : (o : O) →
      FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (hrows : ∀ o, 0 < rows (Nodes.height (S o).upper)) (r : Nat) :
    (observedLaw S P r).totalVariation
      ((HierarchicalAdviceFamily.referenceLaw S outer backgrounds r).pushforward
        (HierarchicalAdviceFamily.referenceObserve S r)) ≤
      P.totalVariation (referencePairLaw S outer backgrounds hrows) := by
  rw [← reference_observe_law S outer backgrounds hrows r]
  exact (DensityVariation.variation_pushforward_le (appendLaw S P r)
    (appendLaw S (referencePairLaw S outer backgrounds hrows) r) (observe S r)).trans_eq
      (appendLaw_totalVariation S P (referencePairLaw S outer backgrounds hrows) r)

theorem observed_totalVariation_le_of_bound (P : FiniteDistribution (PairSample S))
    (outer : FiniteDistribution O)
    (backgrounds : (o : O) →
      FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (hrows : ∀ o, 0 < rows (Nodes.height (S o).upper)) (r : Nat)
    {error : ℝ} (herror : P.totalVariation (referencePairLaw S outer backgrounds hrows) ≤ error) :
    (observedLaw S P r).totalVariation
      ((HierarchicalAdviceFamily.referenceLaw S outer backgrounds r).pushforward
        (HierarchicalAdviceFamily.referenceObserve S r)) ≤ error :=
  (observed_totalVariation_le S P outer backgrounds hrows r).trans herror

theorem original_totalVariation_le_of_observed
    (P : FiniteDistribution (PairSample S)) (outer : FiniteDistribution O)
    (backgrounds : (o : O) →
      FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (hrows : ∀ o, 0 < rows (Nodes.height (S o).upper)) (r : Nat)
    (hactual : observedLaw S P r =
      (HierarchicalAdviceFamily.originalLaw S outer r).pushforward
        (HierarchicalAdviceFamily.observe S r)) :
    ((HierarchicalAdviceFamily.originalLaw S outer r).pushforward
        (HierarchicalAdviceFamily.observe S r)).totalVariation
      ((HierarchicalAdviceFamily.referenceLaw S outer backgrounds r).pushforward
        (HierarchicalAdviceFamily.referenceObserve S r)) ≤
      P.totalVariation (referencePairLaw S outer backgrounds hrows) := by
  rw [← hactual]
  exact observed_totalVariation_le S P outer backgrounds hrows r

end
end PerfectCompleteness.HeterogeneousPairAdvice

end

end OAI
