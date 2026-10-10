import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalAdviceExperimentLemmas
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalProjectedExperimentLemmas
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalProjectedRawAverage
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalProjectedSliceLemmas
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalRawAverage
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalRawPredictionLemmas
import OAI.Computability.PerfectCompleteness.Foundations.WholeArrayRawAssembly
import OAI.Computability.PerfectCompleteness.Reduction.FixedComparisonErrorsLemmas

namespace OAI


namespace PerfectCompleteness.HierarchicalProjectedPrediction

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
  (outer : FiniteDistribution K)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (κ : ℝ) (r : Nat) (ρ : ℝ)

local notation "S" => HierarchicalProjectedExperiment.experiment (rows := rows) (repeats := repeats)
  slots projected projection upper lowerLevel lower cut direction outer σ

def rawJ (sample : HierarchicalProjectedExperiment.RawSample (rows := rows) (repeats := repeats)
    projected upper lower cut r) : Bool :=
  HierarchicalProjectedRawPrediction.rawJ slots (projected sample.2.1) (projection sample.2.1)
    rows upper (lower sample.2.1) lowerLevel (S).original (S).arrays
    (HierarchicalAdviceExperiment.lowerEvent S) κ σ ρ sample.1
    repeats (cut sample.2.1) sample.2.2

def rawPrediction
    (sample : HierarchicalProjectedExperiment.RawSample (rows := rows) (repeats := repeats)
      projected upper lower cut r) : Bool :=
  HierarchicalProjectedRawPrediction.rawPrediction slots (projected sample.2.1) (projection sample.2.1)
    rows upper (lower sample.2.1) lowerLevel (S).original (S).arrays
    (HierarchicalAdviceExperiment.lowerEvent S) κ σ ρ sample.1
    repeats (cut sample.2.1) (direction sample.2.1) sample.2.2


theorem J_rawRead
    (x : HierarchicalProjectedExperiment.Sample (rows := rows) (repeats := repeats)
      projected upper lower cut × HierarchicalProjectedExperiment.Advice (rows := rows) upper r) :
    HierarchicalAdviceExperiment.J S κ r ρ (HierarchicalAdviceExperiment.observe S r x) =
      rawJ (repeats := repeats) slots projected projection upper lowerLevel lower cut direction outer σ κ r ρ
        (HierarchicalProjectedExperiment.rawRead (rows := rows) (repeats := repeats)
          projected upper lower cut r x) := by
  rcases x with ⟨⟨k, ω⟩, A⟩
  exact (congrArg
    (fun X : Arrays slots rows =>
      GoodAdviceEvents.J
        (HierarchicalUsefulness.table slots upper lowerLevel (S).original (S).arrays
          (HierarchicalAdviceExperiment.lowerEvent S) κ σ
          (HierarchicalMatrixTable.backgroundOf slots upper X)) r ρ
        (A, HierarchicalPrediction.quotientMatrix slots upper lowerLevel
          (HierarchicalMatrixTable.backgroundOf slots upper X) (NodeEmbedding.matrix X upper)))
    (congrArg (ChildBlockProjection.arraysPullback rows (projection k))
      (WholeArrayRawAssembly.arrays_exposedRead rows repeats (projected k) upper (lower k) (cut k)
        (LinearMap.ker A) ω))).symm


theorem prediction_rawRead
    (x : HierarchicalProjectedExperiment.Sample (rows := rows) (repeats := repeats)
      projected upper lower cut × HierarchicalProjectedExperiment.Advice (rows := rows) upper r) :
    HierarchicalAdviceExperiment.prediction S κ r ρ x =
      rawPrediction (repeats := repeats)
        slots projected projection upper lowerLevel lower cut direction outer σ κ r ρ
        (HierarchicalProjectedExperiment.rawRead (rows := rows) (repeats := repeats)
          projected upper lower cut r x) := by
  rcases x with ⟨⟨k, ω⟩, A⟩
  exact (congrArg
    (fun X : Arrays slots rows =>
      HierarchicalPrediction.prediction slots upper lowerLevel
        (HierarchicalMatrixTable.backgroundOf slots upper X) σ (lower k)
        (cut k).upper_ne_lower (direction k) (S).original (S).arrays
        (HierarchicalAdviceExperiment.lowerEvent S) κ r ρ A (NodeEmbedding.matrix X upper))
    (congrArg (ChildBlockProjection.arraysPullback rows (projection k))
      (WholeArrayRawAssembly.arrays_exposedRead rows repeats (projected k) upper (lower k) (cut k)
        (LinearMap.ker A) ω))).symm

theorem J_probability :
    (HierarchicalAdviceExperiment.originalLaw S r).probability
        (fun x => HierarchicalAdviceExperiment.J S κ r ρ (HierarchicalAdviceExperiment.observe S r x)) =
      (HierarchicalProjectedExperiment.rawLaw (rows := rows) (repeats := repeats)
        projected upper lower cut outer r).probability
        (rawJ (repeats := repeats)
          slots projected projection upper lowerLevel lower cut direction outer σ κ r ρ) := by
  have h := congrArg
    (fun μ : FiniteDistribution
        (HierarchicalProjectedExperiment.RawSample (rows := rows) (repeats := repeats)
          projected upper lower cut r) =>
      μ.probability (rawJ (repeats := repeats)
        slots projected projection upper lowerLevel lower cut direction outer σ κ r ρ))
    (HierarchicalProjectedExperiment.experiment_rawRead_law (rows := rows) (repeats := repeats)
      slots projected projection upper lowerLevel lower cut direction outer σ r)
  have hp := FiniteDistribution.probability_pushforward
    (Ω := HierarchicalProjectedExperiment.Sample (rows := rows) (repeats := repeats)
      projected upper lower cut × HierarchicalProjectedExperiment.Advice (rows := rows) upper r)
    (Γ := HierarchicalProjectedExperiment.RawSample (rows := rows) (repeats := repeats)
      projected upper lower cut r)
    (HierarchicalAdviceExperiment.originalLaw S r)
    (HierarchicalProjectedExperiment.rawRead (rows := rows) (repeats := repeats)
      projected upper lower cut r)
    (rawJ (repeats := repeats)
      slots projected projection upper lowerLevel lower cut direction outer σ κ r ρ)
  have hp' := hp.symm.trans h
  have hevent : (fun x => rawJ (repeats := repeats)
      slots projected projection upper lowerLevel lower cut direction outer σ κ r ρ
      (HierarchicalProjectedExperiment.rawRead (rows := rows) (repeats := repeats)
        projected upper lower cut r x)) =
      (fun x => HierarchicalAdviceExperiment.J S κ r ρ (HierarchicalAdviceExperiment.observe S r x)) :=
    funext (fun x =>
      (J_rawRead (repeats := repeats)
        slots projected projection upper lowerLevel lower cut direction outer σ κ r ρ x).symm)
  exact (congrArg (fun event =>
    (HierarchicalAdviceExperiment.originalLaw S r).probability event) hevent).symm.trans hp'

theorem prediction_probability :
    (HierarchicalAdviceExperiment.originalLaw S r).probability
        (HierarchicalAdviceExperiment.prediction S κ r ρ) =
      (HierarchicalProjectedExperiment.rawLaw (rows := rows) (repeats := repeats)
        projected upper lower cut outer r).probability
        (rawPrediction (repeats := repeats)
          slots projected projection upper lowerLevel lower cut direction outer σ κ r ρ) := by
  have h := congrArg
    (fun μ : FiniteDistribution
        (HierarchicalProjectedExperiment.RawSample (rows := rows) (repeats := repeats)
          projected upper lower cut r) =>
      μ.probability (rawPrediction (repeats := repeats)
        slots projected projection upper lowerLevel lower cut direction outer σ κ r ρ))
    (HierarchicalProjectedExperiment.experiment_rawRead_law (rows := rows) (repeats := repeats)
      slots projected projection upper lowerLevel lower cut direction outer σ r)
  have hp := FiniteDistribution.probability_pushforward
    (Ω := HierarchicalProjectedExperiment.Sample (rows := rows) (repeats := repeats)
      projected upper lower cut × HierarchicalProjectedExperiment.Advice (rows := rows) upper r)
    (Γ := HierarchicalProjectedExperiment.RawSample (rows := rows) (repeats := repeats)
      projected upper lower cut r)
    (HierarchicalAdviceExperiment.originalLaw S r)
    (HierarchicalProjectedExperiment.rawRead (rows := rows) (repeats := repeats)
      projected upper lower cut r)
    (rawPrediction (repeats := repeats)
      slots projected projection upper lowerLevel lower cut direction outer σ κ r ρ)
  have hp' := hp.symm.trans h
  have hevent : (fun x => rawPrediction (repeats := repeats)
      slots projected projection upper lowerLevel lower cut direction outer σ κ r ρ
      (HierarchicalProjectedExperiment.rawRead (rows := rows) (repeats := repeats)
        projected upper lower cut r x)) =
      HierarchicalAdviceExperiment.prediction S κ r ρ :=
    funext (fun x =>
      (prediction_rawRead (repeats := repeats)
        slots projected projection upper lowerLevel lower cut direction outer σ κ r ρ x).symm)
  exact (congrArg (fun event =>
    (HierarchicalAdviceExperiment.originalLaw S r).probability event) hevent).symm.trans hp'

end
end PerfectCompleteness.HierarchicalProjectedPrediction



namespace PerfectCompleteness.HierarchicalProjectedAverage

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays InitialParameters UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

section Projected

variable {δ : ℚ} (plan : FixedRows.Plan δ) {branch : Nat → Nat} {t : Nat}
  {K : Type*} [Fintype K]
  (slots : RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projected : K → RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projection : ∀ k s j, MixedSupport.Projection (slots s j) (projected k s j))
  (upper : Nodes branch plan.depth) (lowerLevel : Nat)
  (lower : K → Nodes branch plan.depth)
  (cut : ∀ k, OwnInputReference.Cut upper (lower k))
  (direction : ∀ k, Block (FixedRows.rows plan) (lower k))
  (outer : FiniteDistribution K)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))

local notation "S" => HierarchicalProjectedExperiment.experiment
  (rows := FixedRows.rows plan) (repeats := FixedRows.repeats plan)
  slots projected projection upper lowerLevel lower cut direction outer σ

abbrev RawSample := HierarchicalProjectedExperiment.RawSample
  (rows := FixedRows.rows plan) (repeats := FixedRows.repeats plan)
  projected upper lower cut plan.order

def meetingProbability (sample : RawSample plan projected upper lower cut) : ℝ :=
  HierarchicalProjectedRawMeeting.meetingProbability plan slots (projected sample.2.1)
    (projection sample.2.1) upper (lower sample.2.1) lowerLevel
    (S).original (S).arrays (HierarchicalAdviceExperiment.lowerEvent S) σ sample.1
    (direction sample.2.1) (cut sample.2.1) sample.2.2.2

def expectedMeeting : ℝ :=
  (HierarchicalProjectedExperiment.rawLaw (rows := FixedRows.rows plan)
    (repeats := FixedRows.repeats plan) projected upper lower cut outer plan.order).expectation
      (meetingProbability plan slots projected projection upper lowerLevel lower cut direction outer σ)

def predictionDifference : ℝ :=
  (HierarchicalAdviceExperiment.originalLaw S plan.order).probability
      (HierarchicalAdviceExperiment.prediction S (useful δ) plan.order plan.density) -
    rhoPred (useful δ) plan.density *
      (HierarchicalAdviceExperiment.originalLaw S plan.order).probability
        (fun x => HierarchicalAdviceExperiment.J S (useful δ) plan.order plan.density
          (HierarchicalAdviceExperiment.observe S plan.order x))

theorem expectedMeeting_eq_fibers :
    expectedMeeting plan slots projected projection upper lowerLevel lower cut direction outer σ =
      (FiniteDistribution.uniform
        (HierarchicalProjectedExperiment.Advice (rows := FixedRows.rows plan) upper plan.order)).expectation
        (fun A => outer.expectation (fun k =>
          HierarchicalProjectedRawAverage.expectedMeeting plan slots (projected k) (projection k) upper (lower k) lowerLevel
            (S).original (S).arrays (HierarchicalAdviceExperiment.lowerEvent S) σ A (direction k) (cut k)
            (WholeArrayInteriorOwnInputLaw.exteriorLaw (FixedRows.rows plan) (FixedRows.repeats plan)
              (projected k) upper (lower k) (cut k)))) := by
  simp only [expectedMeeting, HierarchicalProjectedExperiment.rawLaw,
    CandidateCoupling.expectation_sigmaLaw]
  rfl

theorem predictionDifference_eq_fibers :
    predictionDifference plan slots projected projection upper lowerLevel lower cut direction outer σ =
      (FiniteDistribution.uniform
        (HierarchicalProjectedExperiment.Advice (rows := FixedRows.rows plan) upper plan.order)).expectation
        (fun A => outer.expectation (fun k =>
          (HierarchicalProjectedRawAverage.law plan (projected k) upper (lower k) A (cut k)
            (WholeArrayInteriorOwnInputLaw.exteriorLaw (FixedRows.rows plan) (FixedRows.repeats plan)
              (projected k) upper (lower k) (cut k))).probability
            (HierarchicalProjectedRawAverage.prediction plan slots (projected k) (projection k) upper (lower k) lowerLevel
              (S).original (S).arrays (HierarchicalAdviceExperiment.lowerEvent S) σ A (direction k) (cut k)) -
          rhoPred (useful δ) plan.density *
            (HierarchicalProjectedRawAverage.law plan (projected k) upper (lower k) A (cut k)
              (WholeArrayInteriorOwnInputLaw.exteriorLaw (FixedRows.rows plan) (FixedRows.repeats plan)
                (projected k) upper (lower k) (cut k))).probability
              (HierarchicalProjectedRawAverage.J plan slots (projected k) (projection k) upper (lower k) lowerLevel
                (S).original (S).arrays (HierarchicalAdviceExperiment.lowerEvent S) σ A (cut k)))) := by
  unfold predictionDifference
  rw [HierarchicalProjectedPrediction.prediction_probability slots projected projection upper lowerLevel lower cut direction outer σ
      (useful δ) plan.order plan.density,
    HierarchicalProjectedPrediction.J_probability slots projected projection upper lowerLevel lower cut direction outer σ
      (useful δ) plan.order plan.density]
  simp only [HierarchicalProjectedExperiment.rawLaw, CompletionSoundness.sigmaLaw_probability,
    DensityVariation.expectation_sub, SmallBiasSlice.expectation_const_mul]
  rfl

theorem expectedMeeting_ge_prediction_difference (hδ : 0 < δ) :
    HierarchicalProjectedRawAverage.factor plan upper *
      predictionDifference plan slots projected projection upper lowerLevel lower cut direction outer σ ≤
      expectedMeeting plan slots projected projection upper lowerLevel lower cut direction outer σ := by
  rw [predictionDifference_eq_fibers, expectedMeeting_eq_fibers,
    ← SmallBiasSlice.expectation_const_mul]
  apply SmallBias.expectation_mono
  intro A
  rw [← SmallBiasSlice.expectation_const_mul]
  apply SmallBias.expectation_mono
  intro k
  exact HierarchicalProjectedRawAverage.expectedMeeting_ge_prediction_difference plan slots (projected k)
    (projection k) upper (lower k) lowerLevel
    (S).original (S).arrays (HierarchicalAdviceExperiment.lowerEvent S) σ A (direction k) (cut k) hδ
    (WholeArrayInteriorOwnInputLaw.exteriorLaw (FixedRows.rows plan) (FixedRows.repeats plan)
      (projected k) upper (lower k) (cut k))

theorem factor_mul_b_eq_gamma :
    HierarchicalProjectedRawAverage.factor plan upper *
      b (useful δ) plan.density (inverse δ) plan.order (FixedRows.rows plan (Nodes.height upper)) =
      gamma (useful δ) plan.density (inverse δ) plan.order (FixedRows.rows plan (Nodes.height upper)) := by
  unfold HierarchicalProjectedRawAverage.factor UpperParameterScalars.gamma
  rw [pow_add]
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

end Projected


variable {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)
  {branch : Nat → Nat} {t : Nat} {K P : Type*} [Fintype K] [Fintype P]
  (slots : RecursiveSpaces.Slots branch p.plan.depth → Fin t → MixedSupport.Slot)
  (projected : K → RecursiveSpaces.Slots branch p.plan.depth → Fin t → MixedSupport.Slot)
  (projection : ∀ k s j, MixedSupport.Projection (slots s j) (projected k s j))
  (upper : Nodes branch p.plan.depth) (lowerLevel : Nat)
  (lower : K → Nodes branch p.plan.depth)
  (cut : ∀ k, OwnInputReference.Cut upper (lower k))
  (direction : ∀ k, Block (FixedRows.rows p.plan) (lower k))
  (outer : FiniteDistribution K)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch p.plan.depth t))

local notation "S" => HierarchicalProjectedExperiment.experiment
  (rows := FixedRows.rows p.plan) (repeats := FixedRows.repeats p.plan)
  slots projected projection upper lowerLevel lower cut direction outer σ

local instance backgroundFintype : Fintype (HierarchicalAdviceExperiment.Background S) :=
  Fintype.ofFinite _

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _

local instance inputFintype :
    (background : HierarchicalAdviceExperiment.Background S) →
      Fintype (HierarchicalAdviceExperiment.Input S background) :=
  HierarchicalAdviceExperiment.inputFintype S

local instance inputFiniteDimensional :
    (background : HierarchicalAdviceExperiment.Background S) →
      FiniteDimensional F2 (HierarchicalAdviceExperiment.Input S background) :=
  HierarchicalAdviceExperiment.inputFiniteDimensional S

theorem expectedMeeting_ge_gamma
    (externalLaw : FiniteDistribution P)
    (background : P → HierarchicalAdviceExperiment.Background S)
    (scalarLaw : P → FiniteDistribution (NodeEmbedding.RowSpace slots upper))
    (hmass : simultaneous δ / 2 ≤ HierarchicalAdviceFromBuckets.usefulProbability
      S (useful δ) externalLaw background scalarLaw (HierarchicalFixedAdvice.rows_positive p S))
    (hpaired : (HierarchicalAdviceFromBuckets.pairedLaw S externalLaw background
      scalarLaw (HierarchicalFixedAdvice.rows_positive p S)).totalVariation
        (HierarchicalAgreementMean.referenceLaw (S).slots (S).upper
          (HierarchicalAdviceFromBuckets.backgroundLaw S externalLaw background)
          (HierarchicalFixedAdvice.rows_positive p S)) ≤ 10 * p.accuracy)
    (hcoarse : ((HierarchicalAdviceExperiment.originalLaw S p.plan.order).pushforward
      (HierarchicalAdviceExperiment.observe S p.plan.order)).totalVariation
        ((HierarchicalAdviceExperiment.referenceLaw S
          (HierarchicalAdviceFromBuckets.backgroundLaw S externalLaw background) p.plan.order).pushforward
            (HierarchicalAdviceExperiment.referenceObserve S p.plan.order)) ≤ 10 * p.accuracy) :
    gamma (useful δ) p.plan.density (inverse δ) p.plan.order
        (FixedRows.rows p.plan (Nodes.height upper)) ≤
      expectedMeeting p.plan slots projected projection upper lowerLevel lower cut direction outer σ := by
  have hdifference := HierarchicalFixedAdvice.prediction_difference p S
    externalLaw background scalarLaw hmass hpaired hcoarse
  rw [← factor_mul_b_eq_gamma p.plan upper]
  exact (mul_le_mul_of_nonneg_left hdifference (HierarchicalProjectedRawAverage.factor_nonneg p.plan upper)).trans
    (expectedMeeting_ge_prediction_difference p.plan slots projected projection upper lowerLevel lower cut direction outer σ hδ)

end
end PerfectCompleteness.HierarchicalProjectedAverage



namespace PerfectCompleteness.HierarchicalProjectedOuterAverage

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays InitialParameters UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {δ : ℚ} (plan : FixedRows.Plan δ)

def factor (ℓ : Nat) : ℝ :=
  (1 / (2 : ℝ) ^ plan.order) *
    (tau (useful δ) plan.density plan.order ℓ ^ 2 / (2 * (2 : ℝ) ^ ℓ))

theorem factor_nonneg (ℓ : Nat) : 0 ≤ factor plan ℓ := by
  unfold factor
  positivity

theorem factor_mul_b_eq_gamma (ℓ : Nat) :
    factor plan ℓ * b (useful δ) plan.density (inverse δ) plan.order ℓ =
      gamma (useful δ) plan.density (inverse δ) plan.order ℓ := by
  unfold factor gamma
  rw [pow_add]
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

variable {branch : Nat → Nat} {t : Nat} {O : Type*} [Fintype O]
  {K : O → Type*} [∀ o, Fintype (K o)]
  (slots : O → RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projected : (o : O) → K o → RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projection : ∀ o k s j, MixedSupport.Projection (slots o s j) (projected o k s j))
  (upper : O → Nodes branch plan.depth) (lowerLevel : Nat)
  (lower : (o : O) → K o → Nodes branch plan.depth)
  (cut : ∀ o k, OwnInputReference.Cut (upper o) (lower o k))
  (direction : ∀ o k, Block (FixedRows.rows plan) (lower o k))
  (inner : (o : O) → FiniteDistribution (K o))
  (outer : FiniteDistribution O)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))

abbrev experiment (o : O) :=
  HierarchicalProjectedExperiment.experiment
    (rows := FixedRows.rows plan) (repeats := FixedRows.repeats plan)
    (slots o) (projected o) (projection o) (upper o) lowerLevel (lower o) (cut o)
    (direction o) (inner o) σ

local notation "S" => experiment plan slots projected projection upper lowerLevel lower cut direction inner σ

def expectedMeeting : ℝ :=
  outer.expectation (fun o => HierarchicalProjectedAverage.expectedMeeting plan
    (slots o) (projected o) (projection o) (upper o) lowerLevel (lower o) (cut o)
    (direction o) (inner o) σ)

def predictionDifference : ℝ :=
  (HierarchicalAdviceFamily.originalLaw S outer plan.order).probability
      (HierarchicalAdviceFamily.prediction S (useful δ) plan.order plan.density) -
    rhoPred (useful δ) plan.density *
      (HierarchicalAdviceFamily.originalLaw S outer plan.order).probability
        (fun x => HierarchicalAdviceFamily.J S (useful δ) plan.order plan.density
          (HierarchicalAdviceFamily.observe S plan.order x))

theorem predictionDifference_eq_mean :
    predictionDifference plan slots projected projection upper lowerLevel lower cut direction inner outer σ =
      outer.expectation (fun o => HierarchicalProjectedAverage.predictionDifference plan
        (slots o) (projected o) (projection o) (upper o) lowerLevel (lower o) (cut o)
        (direction o) (inner o) σ) := by
  simp only [predictionDifference, HierarchicalProjectedAverage.predictionDifference,
    HierarchicalAdviceFamily.originalLaw,
    HierarchicalAdviceFamily.prediction, HierarchicalAdviceFamily.J, HierarchicalAdviceFamily.observe,
    CompletionSoundness.sigmaLaw_probability, DensityVariation.expectation_sub,
    SmallBiasSlice.expectation_const_mul]
  rfl

theorem expectedMeeting_ge_prediction_difference (hδ : 0 < δ)
    (ℓ : Nat) (hrowdim : ∀ o, FixedRows.rows plan (Nodes.height (upper o)) = ℓ) :
    factor plan ℓ *
      predictionDifference plan slots projected projection upper lowerLevel lower cut direction inner outer σ ≤
      expectedMeeting plan slots projected projection upper lowerLevel lower cut direction inner outer σ := by
  unfold expectedMeeting
  rw [predictionDifference_eq_mean, ← SmallBiasSlice.expectation_const_mul]
  apply SmallBias.expectation_mono
  intro o
  have h := HierarchicalProjectedAverage.expectedMeeting_ge_prediction_difference plan
    (slots o) (projected o) (projection o) (upper o) lowerLevel (lower o) (cut o)
    (direction o) (inner o) σ hδ
  have hfactor : HierarchicalProjectedRawAverage.factor plan (upper o) = factor plan ℓ := by
    simp only [HierarchicalProjectedRawAverage.factor, factor, hrowdim o]
  rw [hfactor] at h
  exact h

local instance contextBackgroundFintype (o : O) :
    Fintype (HierarchicalAdviceExperiment.Background (S o)) :=
  HierarchicalAdviceExperiment.backgroundFintype (S o)

local instance familyInputFintype (b : HierarchicalAdviceFamily.Background S) :
    Fintype (HierarchicalAdviceFamily.Input S b) :=
  HierarchicalAdviceFamily.inputFintype S b

local instance familyInputFiniteDimensional (b : HierarchicalAdviceFamily.Background S) :
    FiniteDimensional F2 (HierarchicalAdviceFamily.Input S b) :=
  HierarchicalAdviceFamily.inputFiniteDimensional S b

local instance familyValueFintype (b : HierarchicalAdviceFamily.Background S) :
    Fintype (HierarchicalAdviceFamily.Value S b) :=
  HierarchicalAdviceFamily.valueFintype S b

theorem expectedMeeting_ge_gamma_of_mean (hδ : 0 < δ)
    (ℓ : Nat) (hrowdim : ∀ o, FixedRows.rows plan (Nodes.height (upper o)) = ℓ)
    (backgrounds : (o : O) → FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (v : ℝ) (hv : 0 ≤ v)
    (hsmall : v ≤ plan.density *
      ((inverse δ ^ 2 / 4) / ((2 : ℝ) ^ (plan.order * ℓ)) ^ 2) / 16)
    (hmean : 2 * inverse δ ≤
      (HierarchicalAdviceFamily.backgroundLaw S outer backgrounds).expectation
        (fun b => PartialTableInverse.nonzeroAgreement
          (HierarchicalAdviceFamily.table S (useful δ) b)))
    (hvariation :
      ((HierarchicalAdviceFamily.originalLaw S outer plan.order).pushforward
        (HierarchicalAdviceFamily.observe S plan.order)).totalVariation
        ((HierarchicalAdviceFamily.referenceLaw S outer backgrounds plan.order).pushforward
          (HierarchicalAdviceFamily.referenceObserve S plan.order)) ≤ v) :
    gamma (useful δ) plan.density (inverse δ) plan.order ℓ ≤
      expectedMeeting plan slots projected projection upper lowerLevel lower cut direction inner outer σ := by
  have hrows (o : O) : 0 < FixedRows.rows plan (Nodes.height (S o).upper) :=
    plan.rows_pos (plan.depth - Nodes.height (upper o))
  have hdim (o : O) : FixedRows.rows plan (Nodes.height (S o).upper) ≤ ℓ :=
    (hrowdim o).le
  have hbound := HierarchicalAdviceFamily.prediction_difference S (useful δ) (useful_pos hδ).le
    outer backgrounds hrows ℓ hdim plan.order plan.density (inverse δ) v
    (inverse_pos hδ) plan.density_pos plan.density_lt plan.spectral hmean hv hsmall hvariation
  have hb : useful δ * plan.density *
      ((inverse δ ^ 2 / 4) / ((2 : ℝ) ^ (plan.order * ℓ)) ^ 2) / 4 =
      b (useful δ) plan.density (inverse δ) plan.order ℓ := by
    unfold b rhoPred q g h
    simp only [div_eq_mul_inv, pow_two, mul_inv_rev]
    ring
  rw [hb] at hbound
  rw [← factor_mul_b_eq_gamma plan ℓ]
  exact (mul_le_mul_of_nonneg_left hbound (factor_nonneg plan ℓ)).trans
    (expectedMeeting_ge_prediction_difference plan slots projected projection upper lowerLevel lower cut
      direction inner outer σ hδ ℓ hrowdim)

end
end PerfectCompleteness.HierarchicalProjectedOuterAverage



namespace PerfectCompleteness.HierarchicalWholePrediction

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
  (outer : FiniteDistribution K)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (κ : ℝ) (r : Nat) (ρ : ℝ)

local notation "S" => HierarchicalWholeExperiment.experiment (rows := rows) (repeats := repeats)
  slots upper lowerLevel lower cut direction outer σ

def rawJ (sample : HierarchicalWholeExperiment.RawSample (rows := rows) (repeats := repeats)
    slots upper lower cut r) : Bool :=
  HierarchicalRawPrediction.rawJ slots rows upper (lower sample.2.1) lowerLevel
    (S).original (S).arrays (HierarchicalAdviceExperiment.lowerEvent S) κ σ ρ sample.1
    repeats (cut sample.2.1) sample.2.2

def rawPrediction (sample : HierarchicalWholeExperiment.RawSample (rows := rows) (repeats := repeats)
    slots upper lower cut r) : Bool :=
  HierarchicalRawPrediction.rawPrediction slots rows upper (lower sample.2.1) lowerLevel
    (S).original (S).arrays (HierarchicalAdviceExperiment.lowerEvent S) κ σ ρ sample.1
    repeats (cut sample.2.1) (direction sample.2.1) sample.2.2


theorem J_rawRead
    (x : HierarchicalWholeExperiment.Sample (rows := rows) (repeats := repeats)
      slots upper lower cut × HierarchicalWholeExperiment.Advice (rows := rows) upper r) :
    HierarchicalAdviceExperiment.J S κ r ρ (HierarchicalAdviceExperiment.observe S r x) =
      rawJ (repeats := repeats) slots upper lowerLevel lower cut direction outer σ κ r ρ
        (HierarchicalWholeExperiment.rawRead (rows := rows) (repeats := repeats)
          slots upper lower cut r x) := by
  rcases x with ⟨⟨k, ω⟩, A⟩
  exact (congrArg
    (fun X : Arrays slots rows =>
      GoodAdviceEvents.J
        (HierarchicalUsefulness.table slots upper lowerLevel (S).original (S).arrays
          (HierarchicalAdviceExperiment.lowerEvent S) κ σ
          (HierarchicalMatrixTable.backgroundOf slots upper X)) r ρ
        (A, HierarchicalPrediction.quotientMatrix slots upper lowerLevel
          (HierarchicalMatrixTable.backgroundOf slots upper X) (NodeEmbedding.matrix X upper)))
    (WholeArrayRawAssembly.arrays_exposedRead rows repeats slots upper (lower k) (cut k)
      (LinearMap.ker A) ω)).symm


theorem prediction_rawRead
    (x : HierarchicalWholeExperiment.Sample (rows := rows) (repeats := repeats)
      slots upper lower cut × HierarchicalWholeExperiment.Advice (rows := rows) upper r) :
    HierarchicalAdviceExperiment.prediction S κ r ρ x =
      rawPrediction (repeats := repeats) slots upper lowerLevel lower cut direction outer σ κ r ρ
        (HierarchicalWholeExperiment.rawRead (rows := rows) (repeats := repeats)
          slots upper lower cut r x) := by
  rcases x with ⟨⟨k, ω⟩, A⟩
  exact (congrArg
    (fun X : Arrays slots rows =>
      HierarchicalPrediction.prediction slots upper lowerLevel
        (HierarchicalMatrixTable.backgroundOf slots upper X) σ (lower k)
        (cut k).upper_ne_lower (direction k) (S).original (S).arrays
        (HierarchicalAdviceExperiment.lowerEvent S) κ r ρ A (NodeEmbedding.matrix X upper))
    (WholeArrayRawAssembly.arrays_exposedRead rows repeats slots upper (lower k) (cut k)
      (LinearMap.ker A) ω)).symm

theorem J_probability :
    (HierarchicalAdviceExperiment.originalLaw S r).probability
        (fun x => HierarchicalAdviceExperiment.J S κ r ρ (HierarchicalAdviceExperiment.observe S r x)) =
      (HierarchicalWholeExperiment.rawLaw (rows := rows) (repeats := repeats)
        slots upper lower cut outer r).probability
        (rawJ (repeats := repeats) slots upper lowerLevel lower cut direction outer σ κ r ρ) := by
  have h := congrArg
    (fun μ : FiniteDistribution
        (HierarchicalWholeExperiment.RawSample (rows := rows) (repeats := repeats)
          slots upper lower cut r) =>
      μ.probability
        (rawJ (repeats := repeats) slots upper lowerLevel lower cut direction outer σ κ r ρ))
    (HierarchicalWholeExperiment.experiment_rawRead_law (rows := rows) (repeats := repeats)
      slots upper lowerLevel lower cut direction outer σ r)
  have hp := FiniteDistribution.probability_pushforward
    (Ω := HierarchicalWholeExperiment.Sample (rows := rows) (repeats := repeats)
      slots upper lower cut × HierarchicalWholeExperiment.Advice (rows := rows) upper r)
    (Γ := HierarchicalWholeExperiment.RawSample (rows := rows) (repeats := repeats)
      slots upper lower cut r)
    (HierarchicalAdviceExperiment.originalLaw S r)
    (HierarchicalWholeExperiment.rawRead (rows := rows) (repeats := repeats)
      slots upper lower cut r)
    (rawJ (repeats := repeats) slots upper lowerLevel lower cut direction outer σ κ r ρ)
  have hprob := hp.symm.trans h
  have hevent : (fun x => rawJ (repeats := repeats)
      slots upper lowerLevel lower cut direction outer σ κ r ρ
      (HierarchicalWholeExperiment.rawRead (rows := rows) (repeats := repeats)
        slots upper lower cut r x)) =
      (fun x => HierarchicalAdviceExperiment.J S κ r ρ (HierarchicalAdviceExperiment.observe S r x)) :=
    funext (fun x => (J_rawRead (repeats := repeats)
      slots upper lowerLevel lower cut direction outer σ κ r ρ x).symm)
  exact (congrArg
    (fun event => (HierarchicalAdviceExperiment.originalLaw S r).probability event)
    hevent).symm.trans hprob

theorem prediction_probability :
    (HierarchicalAdviceExperiment.originalLaw S r).probability
        (HierarchicalAdviceExperiment.prediction S κ r ρ) =
      (HierarchicalWholeExperiment.rawLaw (rows := rows) (repeats := repeats)
        slots upper lower cut outer r).probability
        (rawPrediction (repeats := repeats)
          slots upper lowerLevel lower cut direction outer σ κ r ρ) := by
  have h := congrArg
    (fun μ : FiniteDistribution
        (HierarchicalWholeExperiment.RawSample (rows := rows) (repeats := repeats)
          slots upper lower cut r) =>
      μ.probability
        (rawPrediction (repeats := repeats) slots upper lowerLevel lower cut direction outer σ κ r ρ))
    (HierarchicalWholeExperiment.experiment_rawRead_law (rows := rows) (repeats := repeats)
      slots upper lowerLevel lower cut direction outer σ r)
  have hp := FiniteDistribution.probability_pushforward
    (Ω := HierarchicalWholeExperiment.Sample (rows := rows) (repeats := repeats)
      slots upper lower cut × HierarchicalWholeExperiment.Advice (rows := rows) upper r)
    (Γ := HierarchicalWholeExperiment.RawSample (rows := rows) (repeats := repeats)
      slots upper lower cut r)
    (HierarchicalAdviceExperiment.originalLaw S r)
    (HierarchicalWholeExperiment.rawRead (rows := rows) (repeats := repeats)
      slots upper lower cut r)
    (rawPrediction (repeats := repeats) slots upper lowerLevel lower cut direction outer σ κ r ρ)
  have hprob := hp.symm.trans h
  have hevent : (fun x => rawPrediction (repeats := repeats)
      slots upper lowerLevel lower cut direction outer σ κ r ρ
      (HierarchicalWholeExperiment.rawRead (rows := rows) (repeats := repeats)
        slots upper lower cut r x)) =
      HierarchicalAdviceExperiment.prediction S κ r ρ :=
    funext (fun x => (prediction_rawRead (repeats := repeats)
      slots upper lowerLevel lower cut direction outer σ κ r ρ x).symm)
  exact (congrArg
    (fun event => (HierarchicalAdviceExperiment.originalLaw S r).probability event)
    hevent).symm.trans hprob

end
end PerfectCompleteness.HierarchicalWholePrediction



namespace PerfectCompleteness.HierarchicalWholeAverage

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays InitialParameters UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

section Whole

variable {δ : ℚ} (plan : FixedRows.Plan δ) {branch : Nat → Nat} {t : Nat}
  {K : Type*} [Fintype K]
  (slots : RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (upper : Nodes branch plan.depth) (lowerLevel : Nat)
  (lower : K → Nodes branch plan.depth)
  (cut : ∀ k, OwnInputReference.Cut upper (lower k))
  (direction : ∀ k, Block (FixedRows.rows plan) (lower k))
  (outer : FiniteDistribution K)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))

local notation "S" => HierarchicalWholeExperiment.experiment
  (rows := FixedRows.rows plan) (repeats := FixedRows.repeats plan)
  slots upper lowerLevel lower cut direction outer σ

abbrev RawSample := HierarchicalWholeExperiment.RawSample
  (rows := FixedRows.rows plan) (repeats := FixedRows.repeats plan)
  slots upper lower cut plan.order

def meetingProbability (sample : RawSample plan slots upper lower cut) : ℝ :=
  HierarchicalRawMeeting.meetingProbability plan slots upper (lower sample.2.1) lowerLevel
    (S).original (S).arrays (HierarchicalAdviceExperiment.lowerEvent S) σ sample.1
    (direction sample.2.1) (cut sample.2.1) sample.2.2.2

def expectedMeeting : ℝ :=
  (HierarchicalWholeExperiment.rawLaw (rows := FixedRows.rows plan)
    (repeats := FixedRows.repeats plan) slots upper lower cut outer plan.order).expectation
      (meetingProbability plan slots upper lowerLevel lower cut direction outer σ)

def predictionDifference : ℝ :=
  (HierarchicalAdviceExperiment.originalLaw S plan.order).probability
      (HierarchicalAdviceExperiment.prediction S (useful δ) plan.order plan.density) -
    rhoPred (useful δ) plan.density *
      (HierarchicalAdviceExperiment.originalLaw S plan.order).probability
        (fun x => HierarchicalAdviceExperiment.J S (useful δ) plan.order plan.density
          (HierarchicalAdviceExperiment.observe S plan.order x))

theorem expectedMeeting_eq_fibers :
    expectedMeeting plan slots upper lowerLevel lower cut direction outer σ =
      (FiniteDistribution.uniform
        (HierarchicalWholeExperiment.Advice (rows := FixedRows.rows plan) upper plan.order)).expectation
        (fun A => outer.expectation (fun k =>
          HierarchicalRawAverage.expectedMeeting plan slots upper (lower k) lowerLevel
            (S).original (S).arrays (HierarchicalAdviceExperiment.lowerEvent S) σ A (direction k) (cut k)
            (WholeArrayInteriorOwnInputLaw.exteriorLaw (FixedRows.rows plan) (FixedRows.repeats plan)
              slots upper (lower k) (cut k)))) := by
  simp only [expectedMeeting, HierarchicalWholeExperiment.rawLaw,
    CandidateCoupling.expectation_sigmaLaw]
  rfl

theorem predictionDifference_eq_fibers :
    predictionDifference plan slots upper lowerLevel lower cut direction outer σ =
      (FiniteDistribution.uniform
        (HierarchicalWholeExperiment.Advice (rows := FixedRows.rows plan) upper plan.order)).expectation
        (fun A => outer.expectation (fun k =>
          (HierarchicalRawAverage.law plan slots upper (lower k) A (cut k)
            (WholeArrayInteriorOwnInputLaw.exteriorLaw (FixedRows.rows plan) (FixedRows.repeats plan)
              slots upper (lower k) (cut k))).probability
            (HierarchicalRawAverage.prediction plan slots upper (lower k) lowerLevel
              (S).original (S).arrays (HierarchicalAdviceExperiment.lowerEvent S) σ A (direction k) (cut k)) -
          rhoPred (useful δ) plan.density *
            (HierarchicalRawAverage.law plan slots upper (lower k) A (cut k)
              (WholeArrayInteriorOwnInputLaw.exteriorLaw (FixedRows.rows plan) (FixedRows.repeats plan)
                slots upper (lower k) (cut k))).probability
              (HierarchicalRawAverage.J plan slots upper (lower k) lowerLevel
                (S).original (S).arrays (HierarchicalAdviceExperiment.lowerEvent S) σ A (cut k)))) := by
  unfold predictionDifference
  rw [HierarchicalWholePrediction.prediction_probability slots upper lowerLevel lower cut direction outer σ
      (useful δ) plan.order plan.density,
    HierarchicalWholePrediction.J_probability slots upper lowerLevel lower cut direction outer σ
      (useful δ) plan.order plan.density]
  simp only [HierarchicalWholeExperiment.rawLaw, CompletionSoundness.sigmaLaw_probability,
    DensityVariation.expectation_sub, SmallBiasSlice.expectation_const_mul]
  rfl

theorem expectedMeeting_ge_prediction_difference (hδ : 0 < δ) :
    HierarchicalRawAverage.factor plan upper *
      predictionDifference plan slots upper lowerLevel lower cut direction outer σ ≤
      expectedMeeting plan slots upper lowerLevel lower cut direction outer σ := by
  rw [predictionDifference_eq_fibers, expectedMeeting_eq_fibers,
    ← SmallBiasSlice.expectation_const_mul]
  apply SmallBias.expectation_mono
  intro A
  rw [← SmallBiasSlice.expectation_const_mul]
  apply SmallBias.expectation_mono
  intro k
  exact HierarchicalRawAverage.expectedMeeting_ge_prediction_difference plan slots upper (lower k) lowerLevel
    (S).original (S).arrays (HierarchicalAdviceExperiment.lowerEvent S) σ A (direction k) (cut k) hδ
    (WholeArrayInteriorOwnInputLaw.exteriorLaw (FixedRows.rows plan) (FixedRows.repeats plan)
      slots upper (lower k) (cut k))

theorem factor_mul_b_eq_gamma :
    HierarchicalRawAverage.factor plan upper *
      b (useful δ) plan.density (inverse δ) plan.order (FixedRows.rows plan (Nodes.height upper)) =
      gamma (useful δ) plan.density (inverse δ) plan.order (FixedRows.rows plan (Nodes.height upper)) := by
  unfold HierarchicalRawAverage.factor UpperParameterScalars.gamma
  rw [pow_add]
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

end Whole


variable {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)
  {branch : Nat → Nat} {t : Nat} {K P : Type*} [Fintype K] [Fintype P]
  (slots : RecursiveSpaces.Slots branch p.plan.depth → Fin t → MixedSupport.Slot)
  (upper : Nodes branch p.plan.depth) (lowerLevel : Nat)
  (lower : K → Nodes branch p.plan.depth)
  (cut : ∀ k, OwnInputReference.Cut upper (lower k))
  (direction : ∀ k, Block (FixedRows.rows p.plan) (lower k))
  (outer : FiniteDistribution K)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch p.plan.depth t))

local notation "S" => HierarchicalWholeExperiment.experiment
  (rows := FixedRows.rows p.plan) (repeats := FixedRows.repeats p.plan)
  slots upper lowerLevel lower cut direction outer σ

local instance backgroundFintype : Fintype (HierarchicalAdviceExperiment.Background S) :=
  Fintype.ofFinite _

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _

local instance inputFintype :
    (background : HierarchicalAdviceExperiment.Background S) →
      Fintype (HierarchicalAdviceExperiment.Input S background) :=
  HierarchicalAdviceExperiment.inputFintype S

local instance inputFiniteDimensional :
    (background : HierarchicalAdviceExperiment.Background S) →
      FiniteDimensional F2 (HierarchicalAdviceExperiment.Input S background) :=
  HierarchicalAdviceExperiment.inputFiniteDimensional S

theorem expectedMeeting_ge_gamma
    (externalLaw : FiniteDistribution P)
    (background : P → HierarchicalAdviceExperiment.Background S)
    (scalarLaw : P → FiniteDistribution (NodeEmbedding.RowSpace slots upper))
    (hmass : simultaneous δ / 2 ≤ HierarchicalAdviceFromBuckets.usefulProbability
      S (useful δ) externalLaw background scalarLaw (HierarchicalFixedAdvice.rows_positive p S))
    (hpaired : (HierarchicalAdviceFromBuckets.pairedLaw S externalLaw background
      scalarLaw (HierarchicalFixedAdvice.rows_positive p S)).totalVariation
        (HierarchicalAgreementMean.referenceLaw (S).slots (S).upper
          (HierarchicalAdviceFromBuckets.backgroundLaw S externalLaw background)
          (HierarchicalFixedAdvice.rows_positive p S)) ≤ 10 * p.accuracy)
    (hcoarse : ((HierarchicalAdviceExperiment.originalLaw S p.plan.order).pushforward
      (HierarchicalAdviceExperiment.observe S p.plan.order)).totalVariation
        ((HierarchicalAdviceExperiment.referenceLaw S
          (HierarchicalAdviceFromBuckets.backgroundLaw S externalLaw background) p.plan.order).pushforward
            (HierarchicalAdviceExperiment.referenceObserve S p.plan.order)) ≤ 10 * p.accuracy) :
    gamma (useful δ) p.plan.density (inverse δ) p.plan.order
        (FixedRows.rows p.plan (Nodes.height upper)) ≤
      expectedMeeting p.plan slots upper lowerLevel lower cut direction outer σ := by
  have hdifference := HierarchicalFixedAdvice.prediction_difference p S
    externalLaw background scalarLaw hmass hpaired hcoarse
  rw [← factor_mul_b_eq_gamma p.plan upper]
  exact (mul_le_mul_of_nonneg_left hdifference (HierarchicalRawAverage.factor_nonneg p.plan upper)).trans
    (expectedMeeting_ge_prediction_difference p.plan slots upper lowerLevel lower cut direction outer σ hδ)

end
end PerfectCompleteness.HierarchicalWholeAverage

end OAI
