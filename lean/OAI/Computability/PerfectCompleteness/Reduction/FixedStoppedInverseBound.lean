import OAI.Computability.PerfectCompleteness.Construction.StoppedProjectedBuckets
import OAI.Computability.PerfectCompleteness.Decoding.FixedStoppedDecoderLaw
import OAI.Computability.PerfectCompleteness.Reduction.HierarchicalFixedAdviceFamilyLemmas
import OAI.Computability.PerfectCompleteness.Sampling.FixedStoppedPhysicalLawLemmas
import OAI.Computability.PerfectCompleteness.Sampling.StoppedProjectedMeetingLaw

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedInverseBound

noncomputable section

open scoped Classical
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

abbrev clauses := PCPSource.clauseFamily (BinaryLanguage.totalRename input)

abbrev Outer := StoppedProjectedExperiment.Outer
  (branch := FixedParameters.branch parameters) (n := parameters.plan.depth)
  (j := j.val) (t := FixedRows.sourceLength parameters.plan hδ)
  (m := (PCPSource.normalizedFormula (BinaryLanguage.totalRename input)).clauses.length)

abbrev designated := FixedStoppedPhysicalLaw.designated parameters i

abbrev experiment (strategy : FixedPreliminaryGame.Strategy parameters input)
    (o : Outer parameters j input) :=
  StoppedProjectedExperiment.experiment (clauses input)
    (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
    (fun k _ => FixedParameters.branch_pos parameters k)
    (StoppedProjectedMeetingLaw.rows_positive parameters.plan)
    (FixedStoppedDecoderLaw.flag parameters i)
    (FixedStoppedDecoderLaw.labeling parameters input strategy) o

abbrev outerLaw : FiniteDistribution (Outer parameters j input) :=
  StoppedProjectedExperiment.outerLaw (Nat.succ_le_of_lt j.isLt)
    (fun k _ => FixedParameters.branch_pos parameters k)

abbrev externalLaw (o : Outer parameters j input) :=
  StoppedProjectedBuckets.externalLaw (clauses input)
    (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
    (StoppedProjectedMeetingLaw.rows_positive parameters.plan) o
    (fun k _ => FixedParameters.branch_pos parameters k)
    (FixedStoppedDecoderLaw.flag parameters i)

abbrev background (o : Outer parameters j input) :=
  StoppedProjectedBuckets.background (clauses input)
    (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
    (StoppedProjectedMeetingLaw.rows_positive parameters.plan) o

abbrev scalarLaw (o : Outer parameters j input) :=
  StoppedProjectedBuckets.scalarLaw (clauses input)
    (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
    (StoppedProjectedMeetingLaw.rows_positive parameters.plan) o

variable (strategy : FixedPreliminaryGame.Strategy parameters input)

local notation "S" => experiment parameters i j hij input strategy

local instance nativeBackgroundFintype (o : Outer parameters j input) :
    Fintype (HierarchicalMatrixTable.Background (rows := FixedRows.rows parameters.plan)
      (StoppedProjectedExperiment.nativeSlots (clauses input) o)
      (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o)) :=
  HierarchicalUsefulCollision.backgroundFintype (rows := FixedRows.rows parameters.plan)
    (StoppedProjectedExperiment.nativeSlots (clauses input) o)
    (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o)

local instance nativeRowSpaceFintype (o : Outer parameters j input) :
    Fintype (NodeEmbedding.RowSpace
      (StoppedProjectedExperiment.nativeSlots (clauses input) o)
      (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o)) :=
  HierarchicalUsefulCollision.rowSpaceFintype
    (StoppedProjectedExperiment.nativeSlots (clauses input) o)
    (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o)

abbrev PairFiber (o : Outer parameters j input) :=
  HierarchicalAgreementMean.PairRecord (rows := FixedRows.rows parameters.plan)
    (StoppedProjectedExperiment.nativeSlots (clauses input) o)
    (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o)

abbrev PairSample := (o : Outer parameters j input) × PairFiber parameters j input o

local instance pairFiberFintype (o : Outer parameters j input) :
    Fintype (PairFiber parameters j input o) := by
  unfold PairFiber HierarchicalAgreementMean.PairRecord
  infer_instance

local instance pairSampleFintype : Fintype (PairSample parameters j input) :=
  Sigma.instFintype

local instance backgroundFintype (o : Outer parameters j input) :
    Fintype (HierarchicalAdviceExperiment.Background (S o)) :=
  HierarchicalAdviceExperiment.backgroundFintype (S o)

local instance coarseFintype (o : Outer parameters j input) :
    Fintype (HierarchicalAdviceExperiment.Coarse (S o)) :=
  HierarchicalAdviceFamily.coarseFintype S o

local instance inputFintype (o : Outer parameters j input)
    (bg : HierarchicalAdviceExperiment.Background (S o)) :
    Fintype (HierarchicalAdviceExperiment.Input (S o) bg) :=
  HierarchicalAdviceExperiment.inputFintype (S o) bg

local instance inputFiniteDimensional (o : Outer parameters j input)
    (bg : HierarchicalAdviceExperiment.Background (S o)) :
    FiniteDimensional F2 (HierarchicalAdviceExperiment.Input (S o) bg) :=
  HierarchicalAdviceExperiment.inputFiniteDimensional (S o) bg

local instance projectedSampleFintype (o : Outer parameters j input) :
    Fintype (HierarchicalProjectedExperiment.Sample
      (rows := FixedRows.rows parameters.plan) (repeats := FixedRows.repeats parameters.plan)
      (StoppedProjectedExperiment.projectedSlots (clauses input) (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij (designated parameters i) o)
      (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o)
      (StoppedProjectedExperiment.lower (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij o)
      (StoppedProjectedExperiment.cut (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij o)) := by
  letI : (k : StoppedProjectedExperiment.Inner
      (branch := FixedParameters.branch parameters) (n := parameters.plan.depth)
      (i := i.val) (j := j.val) (t := FixedRows.sourceLength parameters.plan hδ)
      (FixedRows.rows parameters.plan)) →
      Fintype (WholeArraySampler.Tape (FixedRows.rows parameters.plan)
        (FixedRows.repeats parameters.plan)
        (WholeArrayInteriorOwnInputLaw.fullPath
          (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o)
          (StoppedProjectedExperiment.lower (FixedRows.rows parameters.plan)
            (Nat.succ_le_of_lt j.isLt) hij o k)
          (StoppedProjectedExperiment.cut (FixedRows.rows parameters.plan)
            (Nat.succ_le_of_lt j.isLt) hij o k))
        (StoppedProjectedExperiment.projectedSlots (clauses input) (FixedRows.rows parameters.plan)
          (Nat.succ_le_of_lt j.isLt) hij (designated parameters i) o k)) :=
    fun k => WholeArraySampler.tapeFintype _ _ _ _
  exact Sigma.instFintype

local instance adviceFintype (o : Outer parameters j input) (r : Nat) :
    Fintype (HierarchicalAdviceExperiment.Advice (S o) r) := linearMapFintype

local instance originalFiberFintype (o : Outer parameters j input) (r : Nat) :
    Fintype (HierarchicalProjectedExperiment.Sample
      (rows := FixedRows.rows parameters.plan) (repeats := FixedRows.repeats parameters.plan)
      (StoppedProjectedExperiment.projectedSlots (clauses input) (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij (designated parameters i) o)
      (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o)
      (StoppedProjectedExperiment.lower (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij o)
      (StoppedProjectedExperiment.cut (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij o) ×
      HierarchicalAdviceExperiment.Advice (S o) r) := by
  infer_instance

abbrev backgrounds :=
  HierarchicalBucketFamily.actualBackgrounds (experiment parameters i j hij input strategy)
    (externalLaw parameters i j hij input) (background parameters i j hij input)

abbrev usefulMass : ℝ :=
  HierarchicalBucketFamily.usefulMass (experiment parameters i j hij input strategy)
    (InitialParameters.useful δ) (outerLaw parameters j input)
    (externalLaw parameters i j hij input) (background parameters i j hij input)
    (scalarLaw parameters i j hij input)
    (HierarchicalFixedAdviceFamily.rows_positive parameters
      (experiment parameters i j hij input strategy))

abbrev actualPairs : FiniteDistribution (PairSample parameters j input) :=
  HierarchicalBucketFamily.actualPairLaw (experiment parameters i j hij input strategy)
    (outerLaw parameters j input) (externalLaw parameters i j hij input)
    (background parameters i j hij input) (scalarLaw parameters i j hij input)
    (HierarchicalFixedAdviceFamily.rows_positive parameters
      (experiment parameters i j hij input strategy))

abbrev referencePairs : FiniteDistribution (PairSample parameters j input) :=
  HierarchicalBucketFamily.referencePairLaw (experiment parameters i j hij input strategy)
    (outerLaw parameters j input) (backgrounds parameters i j hij input strategy)
    (HierarchicalFixedAdviceFamily.rows_positive parameters
      (experiment parameters i j hij input strategy))

abbrev pairedVariation : ℝ :=
  (actualPairs parameters i j hij input strategy).totalVariation
    (referencePairs parameters i j hij input strategy)

abbrev coarseVariation : ℝ :=
  ((HierarchicalAdviceFamily.originalLaw (experiment parameters i j hij input strategy)
    (outerLaw parameters j input) parameters.plan.order).pushforward
      (HierarchicalAdviceFamily.observe (experiment parameters i j hij input strategy)
        parameters.plan.order)).totalVariation
    ((HierarchicalAdviceFamily.referenceLaw (experiment parameters i j hij input strategy)
      (outerLaw parameters j input) (backgrounds parameters i j hij input strategy)
      parameters.plan.order).pushforward
        (HierarchicalAdviceFamily.referenceObserve
          (experiment parameters i j hij input strategy) parameters.plan.order))

abbrev expectedMeeting : ℝ :=
  StoppedProjectedMeetingLaw.expectedMeeting parameters.plan (clauses input)
    (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
    (fun k _ => FixedParameters.branch_pos parameters k)
    (FixedStoppedDecoderLaw.flag parameters i)
    (FixedStoppedDecoderLaw.labeling parameters input strategy)

theorem expectedMeeting_ge_gamma
    (hmass : InitialParameters.simultaneous δ / 2 ≤
      usefulMass parameters i j hij input strategy)
    (hpaired : pairedVariation parameters i j hij input strategy ≤ 10 * parameters.accuracy)
    (hcoarse : coarseVariation parameters i j hij input strategy ≤ 10 * parameters.accuracy) :
    FixedRankContradiction.gamma parameters (j.val + 1) ≤
      expectedMeeting parameters i j hij input strategy := by
  have hheight (o : Outer parameters j input) :
      Nodes.height (experiment parameters i j hij input strategy o).upper = j.val + 1 :=
    StoppedProjectedExperiment.upper_height (Nat.succ_le_of_lt j.isLt) o
  have hbound := HierarchicalFixedAdviceFamily.prediction_difference parameters
    (experiment parameters i j hij input strategy) (outerLaw parameters j input)
    (externalLaw parameters i j hij input) (background parameters i j hij input)
    (scalarLaw parameters i j hij input) (backgrounds parameters i j hij input strategy)
    (j.val + 1) (Nat.succ_le_of_lt j.isLt) hheight hmass hpaired hcoarse
  have hmeeting := HierarchicalProjectedOuterAverage.expectedMeeting_ge_prediction_difference
    parameters.plan (StoppedProjectedExperiment.nativeSlots (clauses input))
    (StoppedProjectedExperiment.projectedSlots (clauses input) (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij (designated parameters i))
    (StoppedProjectedExperiment.projection (clauses input) (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij (designated parameters i))
    (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt)) (i.val + 1)
    (StoppedProjectedExperiment.lower (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij)
    (StoppedProjectedExperiment.cut (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij)
    (StoppedProjectedExperiment.direction (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij)
    (fun _ => StoppedProjectedExperiment.innerLaw (FixedRows.rows parameters.plan) hij
      (fun k _ => FixedParameters.branch_pos parameters k)
      (StoppedProjectedMeetingLaw.rows_positive parameters.plan)
      (FixedStoppedDecoderLaw.flag parameters i))
    (outerLaw parameters j input) (FixedStoppedDecoderLaw.labeling parameters input strategy)
    hδ (FixedRows.rows parameters.plan (j.val + 1))
    (fun o => congrArg (FixedRows.rows parameters.plan)
      (StoppedProjectedExperiment.upper_height (Nat.succ_le_of_lt j.isLt) o))
  calc
    _ = HierarchicalProjectedOuterAverage.factor parameters.plan
        (FixedRows.rows parameters.plan (j.val + 1)) *
        UpperParameterScalars.b (InitialParameters.useful δ) parameters.plan.density
          (InitialParameters.inverse δ) parameters.plan.order
          (FixedRows.rows parameters.plan (j.val + 1)) :=
      (HierarchicalProjectedOuterAverage.factor_mul_b_eq_gamma parameters.plan _).symm
    _ ≤ HierarchicalProjectedOuterAverage.factor parameters.plan
        (FixedRows.rows parameters.plan (j.val + 1)) *
        HierarchicalFixedAdviceFamily.predictionDifference parameters
          (experiment parameters i j hij input strategy) (outerLaw parameters j input) :=
      mul_le_mul_of_nonneg_left hbound
        (HierarchicalProjectedOuterAverage.factor_nonneg parameters.plan _)
    _ ≤ _ := hmeeting

end
end PerfectCompleteness.FixedStoppedInverseBound

end

end OAI
