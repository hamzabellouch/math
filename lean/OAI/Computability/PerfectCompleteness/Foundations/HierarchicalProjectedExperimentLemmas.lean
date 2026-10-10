import OAI.Computability.PerfectCompleteness.Decoding.ChildBlockProjection
import OAI.Computability.PerfectCompleteness.Foundations.DependentPredictionDifferenceLemmas
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalAdviceExperimentLemmas
import OAI.Computability.PerfectCompleteness.Machines.WholeArrayInteriorOwnInputLaw
import OAI.Computability.PerfectCompleteness.Sampling.CandidateCoupling

namespace OAI


namespace PerfectCompleteness.HierarchicalProjectedExperiment

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch rows repeats : Nat → Nat} {n t : Nat} {K : Type*} [Fintype K]
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projected : K → RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ k s j, MixedSupport.Projection (slots s j) (projected k s j))
  (upper : Nodes branch n) (lowerLevel : Nat)
  (lower : K → Nodes branch n)
  (cut : ∀ k, OwnInputReference.Cut upper (lower k))
  (direction : ∀ k, Block rows (lower k))

abbrev Sample := (k : K) × WholeArraySampler.Tape rows repeats
  (WholeArrayInteriorOwnInputLaw.fullPath upper (lower k) (cut k)) (projected k)

def originalLaw (outer : FiniteDistribution K) :
    FiniteDistribution (Sample (rows := rows) (repeats := repeats) projected upper lower cut) :=
  CompletionSoundness.sigmaLaw outer (fun k => WholeArraySampler.tapeLaw rows repeats
    (WholeArrayInteriorOwnInputLaw.fullPath upper (lower k) (cut k)) (projected k))

def arrays (x : Sample (rows := rows) (repeats := repeats) projected upper lower cut) :
    Arrays slots rows :=
  ChildBlockProjection.arraysPullback rows (projection x.1)
    (WholeArraySampler.evaluate rows repeats
      (WholeArrayInteriorOwnInputLaw.fullPath upper (lower x.1) (cut x.1)) (projected x.1) x.2)

def experiment (outer : FiniteDistribution K)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t)) :
    HierarchicalAdviceExperiment.Experiment branch rows n t
      (Sample (rows := rows) (repeats := repeats) projected upper lower cut) where
  slots := slots
  upper := upper
  lowerLevel := lowerLevel
  arrays := arrays slots projected projection upper lower cut
  lowerNode x := lower x.1
  separate x := (cut x.1).upper_ne_lower
  direction x := direction x.1
  original := originalLaw projected upper lower cut outer
  strategy := σ

abbrev Advice (r : Nat) := ManyGoodRows.RowMap (Block rows upper) r

abbrev RawSample (r : Nat) :=
  (A : Advice (rows := rows) upper r) × (k : K) ×
    OwnInputReference.RawSample (projected k) rows upper (lower k) (LinearMap.ker A) repeats (cut k)

def rawLaw (outer : FiniteDistribution K) (r : Nat) :
    FiniteDistribution (RawSample (rows := rows) (repeats := repeats) projected upper lower cut r) :=
  CompletionSoundness.sigmaLaw (FiniteDistribution.uniform (Advice (rows := rows) upper r))
    (fun A => CompletionSoundness.sigmaLaw outer (fun k =>
      OwnInputReference.rawLaw (projected k) rows upper (lower k) (LinearMap.ker A) repeats (cut k)
        (WholeArrayInteriorOwnInputLaw.exteriorLaw rows repeats (projected k) upper (lower k) (cut k))))

def rawRead (r : Nat)
    (x : Sample (rows := rows) (repeats := repeats) projected upper lower cut ×
      Advice (rows := rows) upper r) :
    RawSample (rows := rows) (repeats := repeats) projected upper lower cut r :=
  ⟨x.2, x.1.1, WholeArrayInteriorOwnInputLaw.exposedRead rows repeats (projected x.1.1) upper
    (lower x.1.1) (cut x.1.1) (LinearMap.ker x.2) x.1.2⟩

theorem rawRead_expectation (outer : FiniteDistribution K) (r : Nat)
    (f : RawSample (rows := rows) (repeats := repeats) projected upper lower cut r → ℝ) :
    ((originalLaw projected upper lower cut outer).product
      (FiniteDistribution.uniform (Advice (rows := rows) upper r))).expectation
        (fun x => f (rawRead projected upper lower cut r x)) =
      (rawLaw projected upper lower cut outer r).expectation f := by
  rw [FiniteDistribution.expectation_product]
  rw [FiniteDistribution.expectation_comm]
  unfold rawLaw
  rw [CandidateCoupling.expectation_sigmaLaw]
  apply FiniteDistribution.expectation_congr
  intro A
  unfold originalLaw
  rw [CandidateCoupling.expectation_sigmaLaw, CandidateCoupling.expectation_sigmaLaw]
  apply FiniteDistribution.expectation_congr
  intro k
  have h := WholeArrayInteriorOwnInputLaw.exposedRead_law rows repeats (projected k) upper
    (lower k) (cut k) (LinearMap.ker A)
  rw [← h, FiniteDistribution.expectation_pushforward]
  rfl

theorem rawRead_law (outer : FiniteDistribution K) (r : Nat) :
    ((originalLaw (rows := rows) (repeats := repeats) projected upper lower cut outer).product
      (FiniteDistribution.uniform (Advice (rows := rows) upper r))).pushforward
        (rawRead projected upper lower cut r) =
      rawLaw projected upper lower cut outer r := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward,
    CandidateCoupling.probability_eq_expectation,
    CandidateCoupling.probability_eq_expectation]
  exact rawRead_expectation projected upper lower cut outer r
    (fun x => if event x then 1 else 0)

theorem experiment_rawRead_law (outer : FiniteDistribution K)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t)) (r : Nat) :
    (HierarchicalAdviceExperiment.originalLaw
      (experiment (repeats := repeats) slots projected projection upper lowerLevel lower cut
        direction outer σ) r).pushforward (rawRead projected upper lower cut r) =
      rawLaw projected upper lower cut outer r :=
  rawRead_law projected upper lower cut outer r

end
end PerfectCompleteness.HierarchicalProjectedExperiment


namespace PerfectCompleteness.HierarchicalWholeExperiment

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch rows repeats : Nat → Nat} {n t : Nat} {K : Type*} [Fintype K]
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)
  (lower : K → Nodes branch n)
  (cut : ∀ k, OwnInputReference.Cut upper (lower k))
  (direction : ∀ k, Block rows (lower k))

abbrev Sample := (k : K) × WholeArraySampler.Tape rows repeats
  (WholeArrayInteriorOwnInputLaw.fullPath upper (lower k) (cut k)) slots

def originalLaw (outer : FiniteDistribution K) :
    FiniteDistribution (Sample (rows := rows) (repeats := repeats) slots upper lower cut) :=
  CompletionSoundness.sigmaLaw outer (fun k => WholeArraySampler.tapeLaw rows repeats
    (WholeArrayInteriorOwnInputLaw.fullPath upper (lower k) (cut k)) slots)

def arrays (x : Sample (rows := rows) (repeats := repeats) slots upper lower cut) :
    Arrays slots rows :=
  WholeArraySampler.evaluate rows repeats
    (WholeArrayInteriorOwnInputLaw.fullPath upper (lower x.1) (cut x.1)) slots x.2

def experiment (outer : FiniteDistribution K)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t)) :
    HierarchicalAdviceExperiment.Experiment branch rows n t
      (Sample (rows := rows) (repeats := repeats) slots upper lower cut) where
  slots := slots
  upper := upper
  lowerLevel := lowerLevel
  arrays := arrays slots upper lower cut
  lowerNode x := lower x.1
  separate x := (cut x.1).upper_ne_lower
  direction x := direction x.1
  original := originalLaw slots upper lower cut outer
  strategy := σ

abbrev Advice (r : Nat) := ManyGoodRows.RowMap (Block rows upper) r

abbrev RawSample (r : Nat) :=
  (A : Advice (rows := rows) upper r) × (k : K) ×
    OwnInputReference.RawSample slots rows upper (lower k) (LinearMap.ker A) repeats (cut k)

def rawLaw (outer : FiniteDistribution K) (r : Nat) :
    FiniteDistribution (RawSample (rows := rows) (repeats := repeats) slots upper lower cut r) :=
  CompletionSoundness.sigmaLaw (FiniteDistribution.uniform (Advice (rows := rows) upper r))
    (fun A => CompletionSoundness.sigmaLaw outer (fun k =>
      OwnInputReference.rawLaw slots rows upper (lower k) (LinearMap.ker A) repeats (cut k)
        (WholeArrayInteriorOwnInputLaw.exteriorLaw rows repeats slots upper (lower k) (cut k))))

def rawRead (r : Nat)
    (x : Sample (rows := rows) (repeats := repeats) slots upper lower cut ×
      Advice (rows := rows) upper r) :
    RawSample (rows := rows) (repeats := repeats) slots upper lower cut r :=
  ⟨x.2, x.1.1, WholeArrayInteriorOwnInputLaw.exposedRead rows repeats slots upper
    (lower x.1.1) (cut x.1.1) (LinearMap.ker x.2) x.1.2⟩

theorem rawRead_expectation (outer : FiniteDistribution K) (r : Nat)
    (f : RawSample (rows := rows) (repeats := repeats) slots upper lower cut r → ℝ) :
    ((originalLaw slots upper lower cut outer).product
      (FiniteDistribution.uniform (Advice (rows := rows) upper r))).expectation
        (fun x => f (rawRead slots upper lower cut r x)) =
      (rawLaw slots upper lower cut outer r).expectation f := by
  rw [FiniteDistribution.expectation_product]
  rw [FiniteDistribution.expectation_comm]
  unfold rawLaw
  rw [CandidateCoupling.expectation_sigmaLaw]
  apply FiniteDistribution.expectation_congr
  intro A
  unfold originalLaw
  rw [CandidateCoupling.expectation_sigmaLaw, CandidateCoupling.expectation_sigmaLaw]
  apply FiniteDistribution.expectation_congr
  intro k
  have h := WholeArrayInteriorOwnInputLaw.exposedRead_law rows repeats slots upper
    (lower k) (cut k) (LinearMap.ker A)
  rw [← h, FiniteDistribution.expectation_pushforward]
  rfl

theorem rawRead_law (outer : FiniteDistribution K) (r : Nat) :
    ((originalLaw (rows := rows) (repeats := repeats) slots upper lower cut outer).product
      (FiniteDistribution.uniform (Advice (rows := rows) upper r))).pushforward
        (rawRead slots upper lower cut r) =
      rawLaw slots upper lower cut outer r := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward,
    CandidateCoupling.probability_eq_expectation,
    CandidateCoupling.probability_eq_expectation]
  exact rawRead_expectation slots upper lower cut outer r
    (fun x => if event x then 1 else 0)

theorem experiment_rawRead_law (outer : FiniteDistribution K)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t)) (r : Nat) :
    (HierarchicalAdviceExperiment.originalLaw
      (experiment (repeats := repeats) slots upper lowerLevel lower cut direction outer σ) r).pushforward
        (rawRead slots upper lower cut r) =
      rawLaw slots upper lower cut outer r :=
  rawRead_law slots upper lower cut outer r

end
end PerfectCompleteness.HierarchicalWholeExperiment

end OAI
