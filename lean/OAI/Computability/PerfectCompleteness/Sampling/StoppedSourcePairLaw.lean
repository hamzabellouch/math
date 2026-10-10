import OAI.Computability.PerfectCompleteness.Decoding.ProjectedUpperPair
import OAI.Computability.PerfectCompleteness.Decoding.UpperCutTriangle
import OAI.Computability.PerfectCompleteness.Foundations.SourceProjectedWholeChoices
import OAI.Computability.PerfectCompleteness.Foundations.StoppedProjectedCoarseLemmas
import OAI.Computability.UniqueGames.Games.CompletedSamplingLemmas

namespace OAI

section

namespace PerfectCompleteness.StoppedSourcePairLaw

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

private theorem pair_law_congr (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (hproper : i + 1 < j + 1)
    (native right right' : Slots branch n → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (projection' : ∀ s a, MixedSupport.Projection (native s a) (right' s a))
    (hright : right = right') (hprojection : HEq projection projection')
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1)))) :
    (directions.product ((WholeArraySampler.tapeLaw rows repeats (p.append r) right).product
      (RecursiveSampler.law F2 repeats r (LeafDomain (cutSlots p right))))).pushforward
        (UpperScalarCutProjection.stoppedProjectedPair rows repeats p r hproper native right projection) =
    (directions.product ((WholeArraySampler.tapeLaw rows repeats (p.append r) right').product
      (RecursiveSampler.law F2 repeats r (LeafDomain (cutSlots p right'))))).pushforward
        (UpperScalarCutProjection.stoppedProjectedPair rows repeats p r hproper native right' projection') := by
  subst right'
  have hprojection' : projection = projection' := eq_of_heq hprojection
  subst projection'
  rfl

private theorem mixture_product {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (P : A × B → FiniteDistribution X) :
    (μ.product ν).mixture P = μ.mixture (fun a => ν.mixture (fun b => P (a, b))) := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  simp only [FiniteDistribution.probability_mixture]
  exact FiniteDistribution.expectation_product μ ν
    (fun z : A × B => (P z).probability event)

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

theorem fixed_choice_pair
    (lowerPref : GeometricCutSplit.Prefix branch (j + 1) (i + 1))
    (choices : SourceProjectedChoices.Choices (branch := branch) (n := i) (t := t)) :
    ((OriginalCutPairLaw.directionsLaw rows j (hrows j)).product
      ((WholeArraySampler.tapeLaw rows repeats
        ((StoppedProjectedExperiment.upperPath hupper o).append
          (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lowerPref))
        (ProjectedWholeCut.fullSlots
          ((StoppedProjectedExperiment.upperPath hupper o).append
            (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lowerPref))
          (StoppedProjectedExperiment.nativeSlots clauses o)
          (SourceProjectedWholeChoices.projected clauses hupper hij o lowerPref) choices)).product
        (RecursiveSampler.law F2 repeats
          (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lowerPref)
          (LeafDomain (cutSlots (StoppedProjectedExperiment.upperPath hupper o)
            (ProjectedWholeCut.fullSlots
              ((StoppedProjectedExperiment.upperPath hupper o).append
                (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lowerPref))
              (StoppedProjectedExperiment.nativeSlots clauses o)
              (SourceProjectedWholeChoices.projected clauses hupper hij o lowerPref) choices)))))).pushforward
      (UpperScalarCutProjection.stoppedProjectedPair rows repeats
        (StoppedProjectedExperiment.upperPath hupper o)
        (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lowerPref)
        (Nat.succ_lt_succ hij) (StoppedProjectedExperiment.nativeSlots clauses o)
        (ProjectedWholeCut.fullSlots
          ((StoppedProjectedExperiment.upperPath hupper o).append
            (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lowerPref))
          (StoppedProjectedExperiment.nativeSlots clauses o)
          (SourceProjectedWholeChoices.projected clauses hupper hij o lowerPref) choices)
        (ProjectedWholeCut.fullProjection
          ((StoppedProjectedExperiment.upperPath hupper o).append
            (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lowerPref))
          (StoppedProjectedExperiment.nativeSlots clauses o)
          (SourceProjectedWholeChoices.projected clauses hupper hij o lowerPref)
          (SourceProjectedWholeChoices.projection clauses hupper hij o lowerPref) choices)) =
      StoppedProjectedPairMean.fixedPair clauses rows repeats hupper hij designated hrows o
        (lowerPref, SourceProjectedChoices.tagEquiv choices) := by
  exact pair_law_congr rows repeats (StoppedProjectedExperiment.upperPath hupper o)
    (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lowerPref) (Nat.succ_lt_succ hij)
    (StoppedProjectedExperiment.nativeSlots clauses o) _ _ _ _
    (SourceProjectedWholeChoices.fullSlots_eq clauses rows hupper hij designated hrows o lowerPref choices)
    (SourceProjectedWholeChoices.fullProjection_heq clauses rows hupper hij designated hrows o lowerPref choices)
    (OriginalCutPairLaw.directionsLaw rows j (hrows j))

theorem prefix_pair_law
    (lowerPref : GeometricCutSplit.Prefix branch (j + 1) (i + 1))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    UpperScalarPairComparison.pairLaw rows repeats (StoppedProjectedExperiment.upperPath hupper o)
        (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lowerPref)
        (StoppedProjectedExperiment.nativeSlots clauses o)
        (OriginalCutPairLaw.directionsLaw rows j (hrows j))
        (ProjectedPrefixComparison.assembledLaw
          (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows
          (cutSlots ((StoppedProjectedExperiment.upperPath hupper o).append
            (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lowerPref))
            (StoppedProjectedExperiment.nativeSlots clauses o))
          (SourceProjectedWholeChoices.projected clauses hupper hij o lowerPref)
          (SourceProjectedWholeChoices.projection clauses hupper hij o lowerPref)
          (SourceProjectedChoices.choiceLaw (t := t)) β hβ hβ') =
      (SourceProjectedTag.law (t := t)
        (fun _ : Fin (branch i) => ProjectionPosterior.bernoulli β hβ hβ')).mixture
          (fun tag => StoppedProjectedPairMean.fixedPair clauses rows repeats hupper hij
            designated hrows o (lowerPref, tag)) := by
  rw [ProjectedUpperPair.reconstruct_assembled_law _ _ _ _ _ rows repeats
    (Nat.succ_lt_succ hij)]
  unfold ProjectedUpperPair.pairLaw
  rw [← SourceProjectedChoices.tagLaw_choices β hβ hβ',
    UniqueGamesTheorem.Foundations.Repetition.CompletedSampling.mixture_pushforward_base]
  apply congrArg ((SourceProjectedTag.law (t := t)
    (fun _ : Fin (branch i) => ProjectionPosterior.bernoulli β hβ hβ')).mixture)
  funext tag
  simpa only [Equiv.apply_symm_apply] using
    fixed_choice_pair clauses rows repeats hupper hij designated hrows o lowerPref
      (SourceProjectedChoices.tagEquiv.symm tag)

theorem pairedLaw_eq_modified (hbranch : ∀ k < j + 1, 0 < branch k)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t)) :
    HierarchicalAdviceFromBuckets.pairedLaw
      (StoppedProjectedBuckets.experiment clauses rows repeats hupper hij designated hrows o hbranch
        (fun _ => ProjectionPosterior.bernoulli β hβ hβ') σ)
      (StoppedProjectedBuckets.externalLaw clauses rows repeats hupper hij designated hrows o hbranch
        (fun _ => ProjectionPosterior.bernoulli β hβ hβ'))
      (StoppedProjectedBuckets.background clauses rows repeats hupper hij designated hrows o)
      (StoppedProjectedBuckets.scalarLaw clauses rows repeats hupper hij designated hrows o)
      (StoppedProjectedBuckets.rows_positive rows hupper hrows o) =
      UpperCutTriangle.modifiedPairLaw rows repeats (StoppedProjectedExperiment.upperPath hupper o)
        (Nat.succ_le_succ hij.le) (StoppedProjectedExperiment.nativeSlots clauses o)
        hbranch (hrows j) (SourceProjectedWholeChoices.projected clauses hupper hij o)
        (SourceProjectedWholeChoices.projection clauses hupper hij o)
        (fun _ => SourceProjectedChoices.choiceLaw (t := t)) β hβ hβ' := by
  rw [StoppedProjectedPairMean.pairedLaw_eq_mixture]
  unfold StoppedProjectedBucketIndex.baseLaw UpperCutTriangle.modifiedPairLaw
  rw [mixture_product]
  apply congrArg ((GeometricCutSplit.prefixLaw (Nat.succ_le_succ hij.le) hbranch).mixture)
  funext lowerPref
  exact (prefix_pair_law clauses rows repeats hupper hij designated hrows o lowerPref β hβ hβ').symm

end
end PerfectCompleteness.StoppedSourcePairLaw

end

end OAI
