import OAI.Computability.PerfectCompleteness.Construction.HierarchicalBucketFamily
import OAI.Computability.PerfectCompleteness.Construction.StoppedProjectedBuckets
import OAI.Computability.PerfectCompleteness.Foundations.DependentPredictionDifferenceLemmas
import OAI.Computability.PerfectCompleteness.Foundations.HeterogeneousPairAdvice
import OAI.Computability.PerfectCompleteness.Foundations.StoppedProjectedOldRecord

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedCoarse

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n i j t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)
  (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

local notation "O" => StoppedProjectedExperiment.Outer
  (branch := branch) (n := n) (j := j) (t := t) (m := m)

local notation "S" => StoppedProjectedExperiment.experiment clauses rows repeats hupper hij
  designated hbranch hrows flag σ

local instance fixedBackgroundFintype
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) slots upper) :=
  HierarchicalUsefulCollision.backgroundFintype (rows := rows) slots upper

local instance backgroundFintype (o : O) :
    Fintype (HierarchicalAdviceExperiment.Background (S o)) :=
  HierarchicalAdviceExperiment.backgroundFintype (S o)

local instance rowSpaceFintype (o : O) :
    Fintype (NodeEmbedding.RowSpace (S o).slots (S o).upper) :=
  HierarchicalPairCoarse.rowSpaceFintype (S o)

local instance coarseFintype (o : O) :
    Fintype (HierarchicalAdviceExperiment.Coarse (S o)) :=
  HierarchicalAdviceFamily.coarseFintype S o

local instance inputFintype (o : O) (background : HierarchicalAdviceExperiment.Background (S o)) :
    Fintype (HierarchicalAdviceExperiment.Input (S o) background) :=
  HierarchicalAdviceExperiment.inputFintype (S o) background

local instance inputFiniteDimensional (o : O)
    (background : HierarchicalAdviceExperiment.Background (S o)) :
    FiniteDimensional F2 (HierarchicalAdviceExperiment.Input (S o) background) :=
  HierarchicalAdviceExperiment.inputFiniteDimensional (S o) background

local instance projectedSampleFintype (o : O) :
    Fintype (HierarchicalProjectedExperiment.Sample (rows := rows) (repeats := repeats)
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
      (StoppedProjectedExperiment.upper hupper o)
      (StoppedProjectedExperiment.lower rows hupper hij o)
      (StoppedProjectedExperiment.cut rows hupper hij o)) := by
  letI : (k : StoppedProjectedExperiment.Inner
      (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) →
      Fintype (WholeArraySampler.Tape rows repeats
        (WholeArrayInteriorOwnInputLaw.fullPath (StoppedProjectedExperiment.upper hupper o)
          (StoppedProjectedExperiment.lower rows hupper hij o k)
          (StoppedProjectedExperiment.cut rows hupper hij o k))
        (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o k)) :=
    fun k => WholeArraySampler.tapeFintype rows repeats
      (WholeArrayInteriorOwnInputLaw.fullPath (StoppedProjectedExperiment.upper hupper o)
        (StoppedProjectedExperiment.lower rows hupper hij o k)
        (StoppedProjectedExperiment.cut rows hupper hij o k))
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o k)
  exact Sigma.instFintype

local instance adviceFintype (o : O) (r : Nat) :
    Fintype (HierarchicalAdviceExperiment.Advice (S o) r) := linearMapFintype

local instance originalFiberFintype (o : O) (r : Nat) :
    Fintype (HierarchicalProjectedExperiment.Sample (rows := rows) (repeats := repeats)
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
      (StoppedProjectedExperiment.upper hupper o)
      (StoppedProjectedExperiment.lower rows hupper hij o)
      (StoppedProjectedExperiment.cut rows hupper hij o) ×
      HierarchicalAdviceExperiment.Advice (S o) r) := by
  infer_instance

def pairLaw (outer : FiniteDistribution O) :=
  HierarchicalBucketFamily.actualPairLaw S outer
    (fun o => StoppedProjectedBuckets.externalLaw clauses rows repeats hupper hij designated hrows o hbranch flag)
    (fun o => StoppedProjectedBuckets.background clauses rows repeats hupper hij designated hrows o)
    (fun o => StoppedProjectedBuckets.scalarLaw clauses rows repeats hupper hij designated hrows o)
    (fun o => StoppedProjectedBuckets.rows_positive rows hupper hrows o)

theorem original_observe_law (outer : FiniteDistribution O) (r : Nat) :
    HeterogeneousPairAdvice.observedLaw S
        (pairLaw clauses rows repeats hupper hij designated hbranch hrows flag σ outer) r =
      (HierarchicalAdviceFamily.originalLaw S outer r).pushforward
        (HierarchicalAdviceFamily.observe S r) := by
  calc
    _ = CompletionSoundness.sigmaLaw outer (fun o =>
        ((HierarchicalAdviceExperiment.adviceLaw (S o) r).product
          (StoppedProjectedOldRecord.pairLaw clauses rows repeats hupper hij designated hrows o
            hbranch flag)).pushforward (HierarchicalPairCoarse.observe (S o) r)) :=
      HeterogeneousPairAdvice.observed_sigmaLaw S outer
        (fun o => StoppedProjectedOldRecord.pairLaw clauses rows repeats hupper hij designated
          hrows o hbranch flag) r
    _ = CompletionSoundness.sigmaLaw outer (fun o =>
        (HierarchicalAdviceExperiment.originalLaw (S o) r).pushforward
          (HierarchicalAdviceExperiment.observe (S o) r)) := by
      apply congrArg (CompletionSoundness.sigmaLaw outer)
      funext o
      exact HierarchicalPairCoarse.original_observe_law_of_oldRecord (S o)
        (StoppedProjectedOldRecord.pairLaw clauses rows repeats hupper hij designated hrows o
          hbranch flag) r
        (StoppedProjectedOldRecord.original_oldRecord_law clauses rows repeats hupper hij designated
          hrows o hbranch flag σ).symm
    _ = _ := by
      exact (SigmaObservation.pushforward_fiber outer
        (fun o => HierarchicalAdviceExperiment.originalLaw (S o) r)
        (fun o => HierarchicalAdviceExperiment.observe (S o) r)).symm

theorem totalVariation_le_pair (outer : FiniteDistribution O)
    (backgrounds : (o : O) → FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (r : Nat) :
    ((HierarchicalAdviceFamily.originalLaw S outer r).pushforward
      (HierarchicalAdviceFamily.observe S r)).totalVariation
        ((HierarchicalAdviceFamily.referenceLaw S outer backgrounds r).pushforward
          (HierarchicalAdviceFamily.referenceObserve S r)) ≤
      (pairLaw clauses rows repeats hupper hij designated hbranch hrows flag σ outer).totalVariation
        (HierarchicalBucketFamily.referencePairLaw S outer backgrounds
          (fun o => StoppedProjectedBuckets.rows_positive rows hupper hrows o)) :=
  HeterogeneousPairAdvice.original_totalVariation_le_of_observed S
    (pairLaw clauses rows repeats hupper hij designated hbranch hrows flag σ outer)
    outer backgrounds (fun o => StoppedProjectedBuckets.rows_positive rows hupper hrows o) r
    (original_observe_law clauses rows repeats hupper hij designated hbranch hrows flag σ outer r)

end
end PerfectCompleteness.StoppedProjectedCoarse

end

section

namespace PerfectCompleteness.StoppedProjectedPairMean

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n i j t v m : Nat}

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalAgreementMean.Background (rows := rows) slots (upperNode p)) :=
  Fintype.ofFinite _

local instance rowSpaceFintype (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _

theorem proper_pair_law (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (hij : i < j)
    (native right : Slots branch n → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (hrows : 0 < rows (j + 1)) :
    ((StoppedUsefulPairLaw.directionLaw rows j hrows).product
      ((WholeArraySampler.tapeLaw rows repeats (p.append r) right).product
        (RecursiveSampler.law F2 repeats r (LeafDomain (cutSlots p right))))).pushforward
          (UpperScalarCutProjection.stoppedProjectedPair rows repeats p r
            (Nat.succ_lt_succ hij) native right projection) =
      HierarchicalUsefulCollision.pairLaw native (upperNode p)
        (StoppedUsefulPairLaw.externalLaw rows repeats p (StoppedPathHead.child hij r)
          (StoppedPathHead.tail hij r) right)
        (StoppedUsefulPairLaw.background rows repeats p (StoppedPathHead.child hij r)
          (StoppedPathHead.tail hij r) native right projection)
        (StoppedUsefulPairLaw.scalarLaw rows repeats p (StoppedPathHead.child hij r)
          (StoppedPathHead.tail hij r) native right projection)
        (by simpa only [upperNode_height] using hrows) := by
  cases r with
  | refl => exact False.elim ((Nat.lt_irrefl _) hij)
  | step child q =>
      exact StoppedUsefulPairLaw.stoppedProjectedPair_law rows repeats p child q
        (Nat.succ_lt_succ hij) native right projection hrows

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)
  (hrows : ∀ k, 0 < rows (k + 1))
  (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))

local instance nativeBackgroundFintype :
    Fintype (HierarchicalAgreementMean.Background (rows := rows)
      (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o)) :=
  Fintype.ofFinite _

local instance nativeRowSpaceFintype :
    Fintype (NodeEmbedding.RowSpace (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o)) :=
  Fintype.ofFinite _

def fixedPair (base : StoppedProjectedBucketIndex.Base
    (branch := branch) (i := i) (j := j) (t := t)) :
    FiniteDistribution (HierarchicalAgreementMean.PairRecord (rows := rows)
      (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)) :=
  ((StoppedUsefulPairLaw.directionLaw rows j (hrows j)).product
    ((WholeArraySampler.tapeLaw rows repeats
      ((StoppedProjectedExperiment.upperPath hupper o).append
        (StoppedProjectedBuckets.lowerPath (n := n) rows hij hrows base))
      (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base)).product
        (RecursiveSampler.law F2 repeats
          (StoppedProjectedBuckets.lowerPath (n := n) rows hij hrows base)
          (LeafDomain (cutSlots (StoppedProjectedExperiment.upperPath hupper o)
            (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base)))))).pushforward
    (UpperScalarCutProjection.stoppedProjectedPair rows repeats
      (StoppedProjectedExperiment.upperPath hupper o)
      (StoppedProjectedBuckets.lowerPath (n := n) rows hij hrows base) (Nat.succ_lt_succ hij)
      (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base)
      (StoppedProjectedBuckets.projection clauses rows hupper hij designated hrows o base))

theorem fixedPair_eq (base : StoppedProjectedBucketIndex.Base
    (branch := branch) (i := i) (j := j) (t := t)) :
    fixedPair clauses rows repeats hupper hij designated hrows o base =
      HierarchicalUsefulCollision.pairLaw (StoppedProjectedExperiment.nativeSlots clauses o)
        (StoppedProjectedExperiment.upper hupper o)
        (StoppedProjectedBuckets.exteriorLaw clauses rows repeats hupper hij designated hrows o base)
        (fun external => StoppedProjectedBuckets.background clauses rows repeats hupper hij
          designated hrows o ⟨base, external⟩)
        (fun external => StoppedProjectedBuckets.scalarLaw clauses rows repeats hupper hij
          designated hrows o ⟨base, external⟩)
        (StoppedProjectedBuckets.rows_positive rows hupper hrows o) :=
  proper_pair_law rows repeats (StoppedProjectedExperiment.upperPath hupper o)
    (StoppedProjectedBuckets.lowerPath (n := n) rows hij hrows base) hij
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base)
    (StoppedProjectedBuckets.projection clauses rows hupper hij designated hrows o base) (hrows j)

theorem pairedLaw_eq_mixture (hbranch : ∀ k < j + 1, 0 < branch k)
    (flag : Fin (branch i) → FiniteDistribution Bool)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t)) :
    HierarchicalAdviceFromBuckets.pairedLaw
        (StoppedProjectedBuckets.experiment clauses rows repeats hupper hij designated hrows o hbranch flag σ)
        (StoppedProjectedBuckets.externalLaw clauses rows repeats hupper hij designated hrows o hbranch flag)
        (StoppedProjectedBuckets.background clauses rows repeats hupper hij designated hrows o)
        (StoppedProjectedBuckets.scalarLaw clauses rows repeats hupper hij designated hrows o)
        (StoppedProjectedBuckets.rows_positive rows hupper hrows o) =
      (StoppedProjectedBucketIndex.baseLaw (t := t) hij hbranch flag).mixture
        (fixedPair clauses rows repeats hupper hij designated hrows o) := by
  apply SigmaObservation.eq_of_probability_eq
    (X := HierarchicalAgreementMean.PairRecord (rows := rows)
      (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o))
  intro event
  change (HierarchicalUsefulCollision.pairLaw
      (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o)
      (StoppedProjectedBuckets.externalLaw clauses rows repeats hupper hij designated hrows o hbranch flag)
      (StoppedProjectedBuckets.background clauses rows repeats hupper hij designated hrows o)
      (StoppedProjectedBuckets.scalarLaw clauses rows repeats hupper hij designated hrows o)
      (StoppedProjectedBuckets.rows_positive rows hupper hrows o)).probability event =
    ((StoppedProjectedBucketIndex.baseLaw (t := t) hij hbranch flag).mixture
      (fixedPair clauses rows repeats hupper hij designated hrows o)).probability event
  rw [HierarchicalUsefulCollision.pairLaw, FiniteDistribution.probability_pushforward,
    HierarchicalUsefulCollision.law, CompletionSoundness.sigmaLaw_probability,
    StoppedProjectedBuckets.externalLaw, CandidateCoupling.expectation_sigmaLaw,
    FiniteDistribution.probability_mixture]
  apply FiniteDistribution.expectation_congr
  intro base
  rw [fixedPair_eq]
  rw [HierarchicalUsefulCollision.pairLaw, FiniteDistribution.probability_pushforward,
    HierarchicalUsefulCollision.law, CompletionSoundness.sigmaLaw_probability]
  rfl

end
end PerfectCompleteness.StoppedProjectedPairMean

end

end OAI
