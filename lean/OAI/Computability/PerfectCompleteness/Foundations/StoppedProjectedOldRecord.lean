import OAI.Computability.PerfectCompleteness.Construction.StoppedProjectedBuckets
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalPairCoarse
import OAI.Computability.PerfectCompleteness.Sampling.StoppedProjectedGlobalLawLemmas

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedOldRecord

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n i j t v m : Nat}

local instance fixedBackgroundFintype (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) slots upper) :=
  HierarchicalUsefulCollision.backgroundFintype (rows := rows) slots upper

private theorem fixed_old_probability (rows repeats : Nat → Nat)
    (p : Path branch n (j + 1)) (chosen : Fin (branch j)) (q : Path branch j (i + 1))
    (native right : Slots branch n → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (hrows : 0 < rows (j + 1))
    (event : HierarchicalMatrixTable.Background (rows := rows) native
        (WholeArrayInteriorExterior.upperNode p) ×
      HierarchicalMatrixTable.Matrix (rows := rows) native
        (WholeArrayInteriorExterior.upperNode p) → Bool) :
    (WholeArraySampler.law rows repeats (p.append (.step chosen q)) right).probability
        (fun arrays => event
          (HierarchicalMatrixTable.backgroundOf native (WholeArrayInteriorExterior.upperNode p)
              (ChildBlockProjection.arraysPullback rows projection arrays),
            NodeEmbedding.matrix (ChildBlockProjection.arraysPullback rows projection arrays)
              (WholeArrayInteriorExterior.upperNode p))) =
      (HierarchicalUsefulCollision.pairLaw native (WholeArrayInteriorExterior.upperNode p)
        (StoppedUsefulPairLaw.externalLaw rows repeats p chosen q right)
        (StoppedUsefulPairLaw.background rows repeats p chosen q native right projection)
        (StoppedUsefulPairLaw.scalarLaw rows repeats p chosen q native right projection)
        (by simpa only [WholeArrayInteriorExterior.upperNode_height] using hrows)).probability
          (fun record => event (record.1, record.2.1)) := by
  rw [← StoppedUsefulPairLaw.actualPair_law rows repeats p chosen q native right projection hrows,
    FiniteDistribution.probability_pushforward, WholeArraySampler.probability_law]
  simp only [StoppedUsefulPairLaw.actualLaw, StoppedUsefulPairLaw.actualPair,
    UpperScalarCutProjection.projectedPair, CandidateCoupling.probability_eq_expectation,
    FiniteDistribution.expectation_product]
  let directions := StoppedUsefulPairLaw.directionLaw rows j hrows
  let tapes := WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) right
  let fresh := RecursiveSampler.law TreeSourceSpaces.F2 repeats (.step chosen q)
    (LeafDomain (OriginalWholeCutTape.cutSlots p right))
  let oldValue : WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) right → ℝ :=
    fun tape => if event
      (HierarchicalMatrixTable.backgroundOf native (WholeArrayInteriorExterior.upperNode p)
          (ChildBlockProjection.arraysPullback rows projection
            (WholeArraySampler.evaluate rows repeats (p.append (.step chosen q)) right tape)),
        NodeEmbedding.matrix (ChildBlockProjection.arraysPullback rows projection
          (WholeArraySampler.evaluate rows repeats (p.append (.step chosen q)) right tape))
          (WholeArrayInteriorExterior.upperNode p)) then 1 else 0
  change tapes.expectation oldValue = directions.expectation
    (fun _ => tapes.expectation (fun tape => fresh.expectation (fun _ => oldValue tape)))
  symm
  calc
    _ = tapes.expectation (fun tape => fresh.expectation (fun _ => oldValue tape)) :=
      SmallBias.expectation_const directions
        (tapes.expectation (fun tape => fresh.expectation (fun _ => oldValue tape)))
    _ = tapes.expectation oldValue := by
      apply FiniteDistribution.expectation_congr
      intro tape
      exact SmallBias.expectation_const fresh (oldValue tape)

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)
  (hrows : ∀ k, 0 < rows (k + 1))
  (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))

abbrev OldRecord :=
  HierarchicalMatrixTable.Background (rows := rows)
      (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o) ×
    HierarchicalMatrixTable.Matrix (rows := rows)
      (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)

local instance backgroundFintype : Fintype (HierarchicalMatrixTable.Background (rows := rows)
    (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)) :=
  StoppedProjectedBuckets.backgroundFintype clauses rows hupper o

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace
    (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)) :=
  StoppedProjectedBuckets.rowSpaceFintype clauses hupper o

def arrayRecord (arrays : Arrays (StoppedProjectedExperiment.nativeSlots clauses o) rows) :
    OldRecord clauses rows hupper o :=
  (HierarchicalMatrixTable.backgroundOf (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o) arrays,
    NodeEmbedding.matrix arrays (StoppedProjectedExperiment.upper hupper o))

def baseProbability
    (event : OldRecord clauses rows hupper o → Bool)
    (base : StoppedProjectedBuckets.Base (branch := branch) (i := i) (j := j) (t := t)) : ℝ :=
  (WholeArraySampler.law rows repeats
    (StoppedProjectedExperiment.stoppedPath rows hupper hij o
      (StoppedProjectedBuckets.key (n := n) rows hrows base))
    (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base)).probability
      (fun arrays => event (arrayRecord clauses rows hupper o
        (ChildBlockProjection.arraysPullback rows
          (StoppedProjectedBuckets.projection clauses rows hupper hij designated hrows o base)
          arrays)))

theorem base_probability_eq_pair
    (event : OldRecord clauses rows hupper o → Bool)
    (base : StoppedProjectedBuckets.Base (branch := branch) (i := i) (j := j) (t := t)) :
    baseProbability clauses rows repeats hupper hij designated hrows o event base =
      (HierarchicalUsefulCollision.pairLaw
        (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)
        (StoppedProjectedBuckets.exteriorLaw clauses rows repeats hupper hij designated hrows o base)
        (fun external => StoppedProjectedBuckets.background clauses rows repeats hupper hij
          designated hrows o ⟨base, external⟩)
        (fun external => StoppedProjectedBuckets.scalarLaw clauses rows repeats hupper hij
          designated hrows o ⟨base, external⟩)
        (StoppedProjectedBuckets.rows_positive rows hupper hrows o)).probability
          (fun record => event (record.1, record.2.1)) := by
  have hp : StoppedProjectedExperiment.stoppedPath rows hupper hij o
      (StoppedProjectedBuckets.key (n := n) rows hrows base) =
      (StoppedProjectedExperiment.upperPath hupper o).append
        (.step (StoppedProjectedBuckets.chosen (n := n) rows hij hrows base)
          (StoppedProjectedBuckets.continuation (n := n) rows hij hrows base)) :=
    congrArg (fun path => (StoppedProjectedExperiment.upperPath hupper o).append path)
      (StoppedProjectedBuckets.lowerPath_eq_step (n := n) rows hij hrows base)
  unfold baseProbability
  rw [hp]
  exact fixed_old_probability rows repeats (StoppedProjectedExperiment.upperPath hupper o)
    (StoppedProjectedBuckets.chosen (n := n) rows hij hrows base)
    (StoppedProjectedBuckets.continuation (n := n) rows hij hrows base)
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base)
    (StoppedProjectedBuckets.projection clauses rows hupper hij designated hrows o base)
    (hrows j) event

variable (hbranch : ∀ k < j + 1, 0 < branch k)
  (flag : Fin (branch i) → FiniteDistribution Bool)

abbrev pairLaw :=
  HierarchicalUsefulCollision.pairLaw
    (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)
    (StoppedProjectedBuckets.externalLaw clauses rows repeats hupper hij designated hrows o hbranch flag)
    (StoppedProjectedBuckets.background clauses rows repeats hupper hij designated hrows o)
    (StoppedProjectedBuckets.scalarLaw clauses rows repeats hupper hij designated hrows o)
    (StoppedProjectedBuckets.rows_positive rows hupper hrows o)

theorem pair_probability_eq_mean (event : OldRecord clauses rows hupper o → Bool) :
    (pairLaw clauses rows repeats hupper hij designated hrows o hbranch flag).probability
        (fun record => event (record.1, record.2.1)) =
      (StoppedProjectedBucketIndex.baseLaw (t := t) hij hbranch flag).expectation
        (baseProbability clauses rows repeats hupper hij designated hrows o event) := by
  simp only [pairLaw, HierarchicalUsefulCollision.pairLaw,
    FiniteDistribution.probability_pushforward, HierarchicalUsefulCollision.law,
    CompletionSoundness.sigmaLaw_probability, StoppedProjectedBuckets.externalLaw,
    CandidateCoupling.expectation_sigmaLaw]
  apply FiniteDistribution.expectation_congr
  intro base
  simpa only [HierarchicalUsefulCollision.pairLaw,
    FiniteDistribution.probability_pushforward, HierarchicalUsefulCollision.law,
    CompletionSoundness.sigmaLaw_probability, HierarchicalUsefulCollision.pairRecord,
    HierarchicalAgreementMean.pairRecord] using
    (base_probability_eq_pair clauses rows repeats hupper hij designated hrows o event base).symm

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

theorem original_probability_eq_mean (event : OldRecord clauses rows hupper o → Bool) :
    (StoppedProjectedBuckets.experiment clauses rows repeats hupper hij designated hrows o
      hbranch flag σ).original.probability (fun x =>
        event (HierarchicalAdviceExperiment.background
            (StoppedProjectedBuckets.experiment clauses rows repeats hupper hij designated hrows o
              hbranch flag σ) x,
          HierarchicalAdviceExperiment.matrix
            (StoppedProjectedBuckets.experiment clauses rows repeats hupper hij designated hrows o
              hbranch flag σ) x)) =
      (StoppedProjectedBucketIndex.baseLaw (t := t) hij hbranch flag).expectation
        (baseProbability clauses rows repeats hupper hij designated hrows o event) := by
  rw [← StoppedProjectedExperiment.tapeRead_law clauses rows repeats hupper hij designated
    hbranch hrows flag σ o, FiniteDistribution.probability_pushforward]
  have hread : (fun sample : StoppedProjectedExperiment.TapeSample clauses rows repeats
      hupper hij designated o =>
      event (HierarchicalAdviceExperiment.background
          (StoppedProjectedBuckets.experiment clauses rows repeats hupper hij designated hrows o
            hbranch flag σ)
          (StoppedProjectedExperiment.tapeRead clauses rows repeats hupper hij designated o sample),
        HierarchicalAdviceExperiment.matrix
          (StoppedProjectedBuckets.experiment clauses rows repeats hupper hij designated hrows o
            hbranch flag σ)
          (StoppedProjectedExperiment.tapeRead clauses rows repeats hupper hij designated o sample))) =
      (fun sample => event (arrayRecord clauses rows hupper o
        (ChildBlockProjection.arraysPullback rows
          (StoppedProjectedExperiment.projection clauses rows hupper hij designated o sample.1)
          (WholeArraySampler.evaluate rows repeats
            (StoppedProjectedExperiment.stoppedPath rows hupper hij o sample.1)
            (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o sample.1)
            sample.2)))) := by
    funext sample
    unfold HierarchicalAdviceExperiment.background HierarchicalAdviceExperiment.matrix arrayRecord
    rw [StoppedProjectedExperiment.arrays_tapeRead clauses rows repeats hupper hij designated
      hbranch hrows flag σ o sample]
    rfl
  rw [hread, CandidateCoupling.probability_eq_expectation]
  let level : Fin n := ⟨j, Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hupper⟩
  have hcoord := StoppedProjectedBucketIndex.expectation_coordinate clauses rows repeats
    hupper hij designated hrows o hbranch flag level
    (fun base _ tape => if event (arrayRecord clauses rows hupper o
      (ChildBlockProjection.arraysPullback rows
        (StoppedProjectedBuckets.projection clauses rows hupper hij designated hrows o base)
        (WholeArraySampler.evaluate rows repeats
          (StoppedProjectedExperiment.stoppedPath rows hupper hij o
            (StoppedProjectedBuckets.key (n := n) rows hrows base))
          (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base)
          tape))) then 1 else 0)
  simp only [SmallBias.expectation_const, StoppedProjectedBucketIndex.tapeLaw] at hcoord
  unfold baseProbability
  simp only [CandidateCoupling.probability_eq_expectation, WholeArraySampler.law,
    FiniteDistribution.expectation_pushforward]
  exact hcoord

theorem original_oldRecord_law :
    (StoppedProjectedBuckets.experiment clauses rows repeats hupper hij designated hrows o
      hbranch flag σ).original.pushforward (fun x =>
        (HierarchicalAdviceExperiment.background
            (StoppedProjectedBuckets.experiment clauses rows repeats hupper hij designated hrows o
              hbranch flag σ) x,
          HierarchicalAdviceExperiment.matrix
            (StoppedProjectedBuckets.experiment clauses rows repeats hupper hij designated hrows o
              hbranch flag σ) x)) =
      (pairLaw clauses rows repeats hupper hij designated hrows o hbranch flag).pushforward
        (HierarchicalPairCoarse.oldRecord
          (StoppedProjectedBuckets.experiment clauses rows repeats hupper hij designated hrows o
            hbranch flag σ)) := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  calc
    _ = (StoppedProjectedBuckets.experiment clauses rows repeats hupper hij designated hrows o
        hbranch flag σ).original.probability (fun x => event
          (HierarchicalAdviceExperiment.background
              (StoppedProjectedBuckets.experiment clauses rows repeats hupper hij designated hrows o
                hbranch flag σ) x,
            HierarchicalAdviceExperiment.matrix
              (StoppedProjectedBuckets.experiment clauses rows repeats hupper hij designated hrows o
                hbranch flag σ) x)) :=
      FiniteDistribution.probability_pushforward _ _ event
    _ = (pairLaw clauses rows repeats hupper hij designated hrows o hbranch flag).probability
        (fun record => event (record.1, record.2.1)) :=
      (original_probability_eq_mean clauses rows repeats hupper hij designated hrows o
        hbranch flag σ event).trans
        (pair_probability_eq_mean clauses rows repeats hupper hij designated hrows o
          hbranch flag event).symm
    _ = _ := (FiniteDistribution.probability_pushforward
      (pairLaw clauses rows repeats hupper hij designated hrows o hbranch flag)
      (fun record => (record.1, record.2.1)) event).symm

theorem global_oldRecord_law [NeZero m] (hbranchAll : ∀ k < n, 0 < branch k) :
    (StoppedProjectedGlobalLaw.experimentLaw clauses rows repeats hupper hij designated
      hbranchAll hrows flag σ).pushforward
        (fun x => (⟨x.1,
          (HierarchicalAdviceExperiment.background
              (StoppedProjectedGlobalLaw.experiment clauses rows repeats hupper hij designated
                hbranchAll hrows flag σ x.1) x.2,
            HierarchicalAdviceExperiment.matrix
              (StoppedProjectedGlobalLaw.experiment clauses rows repeats hupper hij designated
                hbranchAll hrows flag σ x.1) x.2)⟩ :
          (o : StoppedProjectedExperiment.Outer
            (branch := branch) (n := n) (j := j) (t := t) (m := m)) ×
              OldRecord clauses rows hupper o)) =
      (CompletionSoundness.sigmaLaw (StoppedProjectedExperiment.outerLaw hupper hbranchAll)
        (fun o => pairLaw clauses rows repeats hupper hij designated hrows o
          (fun k hk => hbranchAll k (Nat.lt_of_lt_of_le hk hupper)) flag)).pushforward
        (fun record => (⟨record.1, (record.2.1, record.2.2.1)⟩ :
          (o : StoppedProjectedExperiment.Outer
            (branch := branch) (n := n) (j := j) (t := t) (m := m)) ×
              OldRecord clauses rows hupper o)) := by
  let originalFiber := fun context : StoppedProjectedExperiment.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m) =>
    (StoppedProjectedGlobalLaw.experiment clauses rows repeats hupper hij designated
      hbranchAll hrows flag σ context).original
  let pairedFiber := fun context : StoppedProjectedExperiment.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m) =>
    pairLaw clauses rows repeats hupper hij designated hrows context
      (fun k hk => hbranchAll k (Nat.lt_of_lt_of_le hk hupper)) flag
  let originalRecord := fun (context : StoppedProjectedExperiment.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m)) x =>
    ((HierarchicalAdviceExperiment.background
        (StoppedProjectedGlobalLaw.experiment clauses rows repeats hupper hij designated
          hbranchAll hrows flag σ context) x,
      HierarchicalAdviceExperiment.matrix
        (StoppedProjectedGlobalLaw.experiment clauses rows repeats hupper hij designated
          hbranchAll hrows flag σ context) x) : OldRecord clauses rows hupper context)
  let pairedRecord := fun (context : StoppedProjectedExperiment.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m))
      (record : HierarchicalAgreementMean.PairRecord (rows := rows)
        (StoppedProjectedExperiment.nativeSlots clauses context)
        (StoppedProjectedExperiment.upper hupper context)) =>
    ((record.1, record.2.1) : OldRecord clauses rows hupper context)
  calc
    _ = CompletionSoundness.sigmaLaw (StoppedProjectedExperiment.outerLaw hupper hbranchAll)
        (fun context => (originalFiber context).pushforward (originalRecord context)) :=
      SigmaObservation.pushforward_fiber
        (Y := fun context => OldRecord clauses rows hupper context)
        (StoppedProjectedExperiment.outerLaw hupper hbranchAll) originalFiber originalRecord
    _ = CompletionSoundness.sigmaLaw (StoppedProjectedExperiment.outerLaw hupper hbranchAll)
        (fun context => (pairedFiber context).pushforward (pairedRecord context)) := by
      apply congrArg (CompletionSoundness.sigmaLaw
        (StoppedProjectedExperiment.outerLaw hupper hbranchAll))
      funext context
      exact original_oldRecord_law clauses rows repeats hupper hij designated hrows context
        (fun k hk => hbranchAll k (Nat.lt_of_lt_of_le hk hupper)) flag σ
    _ = _ := (SigmaObservation.pushforward_fiber
      (Y := fun context => OldRecord clauses rows hupper context)
      (StoppedProjectedExperiment.outerLaw hupper hbranchAll) pairedFiber pairedRecord).symm

end
end PerfectCompleteness.StoppedProjectedOldRecord

end

end OAI
