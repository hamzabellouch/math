import OAI.Computability.PerfectCompleteness.Construction.HierarchicalBucketFamily
import OAI.Computability.PerfectCompleteness.Construction.StoppedProjectedBuckets
import OAI.Computability.PerfectCompleteness.Foundations.StoppedProjectedUsefulAverage
import OAI.Computability.PerfectCompleteness.Sampling.StoppedBucketUsefulProbability

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedUsefulProbability

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
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t)) (κ : ℝ)

local notation "S" => StoppedProjectedExperiment.experiment clauses rows repeats hupper hij
  designated hbranch hrows flag σ

variable (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))

local instance nativeRowSpaceFintype :
    Fintype (NodeEmbedding.RowSpace (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o)) := Fintype.ofFinite _

theorem stepTape_law
    (base : StoppedProjectedBucketIndex.Base (branch := branch) (i := i) (j := j) (t := t)) :
    (StoppedProjectedBucketIndex.tapeLaw clauses rows repeats hupper hij designated hrows o base).pushforward
      (fun tape => StoppedProjectedUsefulEvent.stepTape clauses rows repeats hupper hij designated o
        ⟨StoppedProjectedBucketIndex.key (n := n) rows hrows base, tape⟩) =
      WholeArraySampler.tapeLaw rows repeats
        ((StoppedProjectedExperiment.upperPath hupper o).append
          (.step (StoppedProjectedBuckets.chosen (n := n) rows hij hrows base)
            (StoppedProjectedBuckets.continuation (n := n) rows hij hrows base)))
        (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base) :=
  StoppedOwnInputGeometry.pathTapeEquiv_law rows repeats
    (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base)
    (congrArg (fun p : Path branch n (i + 1) =>
      (⟨i + 1, p⟩ : Σ height, Path branch n height))
      (StoppedProjectedUsefulEvent.stepPath_eq rows hupper hij o
        (StoppedProjectedBucketIndex.key (n := n) rows hrows base)))

theorem directionLaw_eq :
    CanonicalDirections.levelLaw rows hrows (StoppedProjectedUsefulEvent.upperLevel hupper) =
      StoppedUsefulPairLaw.directionLaw rows j (hrows j) := rfl

theorem mean_eq_usefulProbability :
    StoppedProjectedUsefulAverage.mean clauses rows repeats hupper hij designated
      hbranch hrows flag σ κ o =
      StoppedProjectedBuckets.usefulProbability clauses rows repeats hupper hij designated
        hrows o hbranch flag σ κ := by
  rw [StoppedProjectedBuckets.usefulProbability_eq_mean]
  unfold StoppedProjectedUsefulAverage.mean
  apply FiniteDistribution.expectation_congr
  intro base
  have hfixed := StoppedBucketUsefulProbability.useful_probability_eq rows repeats
    (StoppedProjectedExperiment.upperPath hupper o)
    (StoppedProjectedBuckets.chosen (n := n) rows hij hrows base)
    (StoppedProjectedBuckets.continuation (n := n) rows hij hrows base)
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base)
    (StoppedProjectedBuckets.projection clauses rows hupper hij designated hrows o base)
    (hrows j) (i + 1) (S o).original (S o).arrays
    (HierarchicalAdviceExperiment.lowerEvent (S o)) κ σ
  change _ = (HierarchicalUsefulCollision.law
    (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)
    (StoppedProjectedBuckets.exteriorLaw clauses rows repeats hupper hij designated hrows o base)
    (fun external => StoppedProjectedBuckets.scalarLaw clauses rows repeats hupper hij designated
      hrows o ⟨base, external⟩) (StoppedProjectedBuckets.rows_positive rows hupper hrows o)).probability
      (HierarchicalUsefulCollision.usefulEvent
        (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)
        (i + 1) (S o).original (S o).arrays (HierarchicalAdviceExperiment.lowerEvent (S o)) κ σ
        (fun external => StoppedProjectedBuckets.background clauses rows repeats hupper hij designated
          hrows o ⟨base, external⟩))
  refine Eq.trans ?_ hfixed.symm
  rw [directionLaw_eq rows hupper hrows]
  apply FiniteDistribution.expectation_congr
  intro direction
  rw [← stepTape_law clauses rows repeats hupper hij designated hrows o base]
  let event (tape : WholeArraySampler.Tape rows repeats
      ((StoppedProjectedExperiment.upperPath hupper o).append
        (.step (StoppedProjectedBuckets.chosen (n := n) rows hij hrows base)
          (StoppedProjectedBuckets.continuation (n := n) rows hij hrows base)))
      (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base)) : Bool :=
    let readout := StoppedUsefulPairLaw.readout rows repeats
      (StoppedProjectedExperiment.upperPath hupper o)
      (StoppedProjectedBuckets.chosen (n := n) rows hij hrows base)
      (StoppedProjectedBuckets.continuation (n := n) rows hij hrows base)
      (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base)
      (StoppedProjectedBuckets.projection clauses rows hupper hij designated hrows o base) tape
    HierarchicalUsefulCollision.usefulAccepted
      (StoppedProjectedExperiment.nativeSlots clauses o)
      (WholeArrayInteriorExterior.upperNode (StoppedProjectedExperiment.upperPath hupper o))
      (i + 1) (S o).original (S o).arrays (HierarchicalAdviceExperiment.lowerEvent (S o)) κ σ
      (StoppedUsefulPairLaw.background rows repeats
        (StoppedProjectedExperiment.upperPath hupper o)
        (StoppedProjectedBuckets.chosen (n := n) rows hij hrows base)
        (StoppedProjectedBuckets.continuation (n := n) rows hij hrows base)
        (StoppedProjectedExperiment.nativeSlots clauses o)
        (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base)
        (StoppedProjectedBuckets.projection clauses rows hupper hij designated hrows o base)
        readout.1)
      (CutNodeRows.directionEquiv rows (StoppedProjectedExperiment.upperPath hupper o) direction)
      (CutNodeRows.bucketTapeEquiv rows (StoppedProjectedExperiment.upperPath hupper o)
        (StoppedProjectedExperiment.nativeSlots clauses o) readout.2)
  have hp := FiniteDistribution.probability_pushforward
    (Ω := StoppedProjectedBucketIndex.Tape clauses rows repeats hupper hij designated hrows o base)
    (Γ := WholeArraySampler.Tape rows repeats
      ((StoppedProjectedExperiment.upperPath hupper o).append
        (.step (StoppedProjectedBuckets.chosen (n := n) rows hij hrows base)
          (StoppedProjectedBuckets.continuation (n := n) rows hij hrows base)))
      (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base))
    (StoppedProjectedBucketIndex.tapeLaw clauses rows repeats hupper hij designated hrows o base)
    (fun tape => StoppedProjectedUsefulEvent.stepTape clauses rows repeats hupper hij designated o
      ⟨StoppedProjectedBucketIndex.key (n := n) rows hrows base, tape⟩) event
  have hevent :
      StoppedProjectedUsefulAverage.bucketEvent clauses rows repeats hupper hij designated
        hbranch hrows flag σ κ o base direction =
      fun tape => event (StoppedProjectedUsefulEvent.stepTape clauses rows repeats hupper hij designated o
        ⟨StoppedProjectedBucketIndex.key (n := n) rows hrows base, tape⟩) := by
    funext tape
    rfl
  exact (congrArg
    (StoppedProjectedBucketIndex.tapeLaw clauses rows repeats hupper hij designated hrows o base).probability
    hevent).trans hp.symm

theorem original_probability_eq_usefulProbability :
    (S o).original.probability (fun x => HierarchicalUsefulFamily.usefulEvent S κ
      (StoppedProjectedUsefulEvent.upperEvent clauses rows repeats hupper hij designated
        hbranch hrows flag σ) ⟨o, x⟩) =
      StoppedProjectedBuckets.usefulProbability clauses rows repeats hupper hij designated
        hrows o hbranch flag σ κ :=
  (StoppedProjectedUsefulAverage.original_probability_eq_mean clauses rows repeats hupper hij
    designated hbranch hrows flag σ κ o).trans
      (mean_eq_usefulProbability clauses rows repeats hupper hij designated hbranch hrows flag σ κ o)

local instance backgroundFintype (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m)) :
    Fintype (HierarchicalAdviceExperiment.Background (S o)) :=
  HierarchicalAdviceExperiment.backgroundFintype (S o)

local instance rowSpaceFintype (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m)) :
    Fintype (NodeEmbedding.RowSpace (S o).slots (S o).upper) := Fintype.ofFinite _

theorem usefulMass_eq_original
    (outer : FiniteDistribution (StoppedProjectedExperiment.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m))) :
    HierarchicalBucketFamily.usefulMass S κ outer
      (fun o => StoppedProjectedBuckets.externalLaw clauses rows repeats hupper hij designated
        hrows o hbranch flag)
      (fun o => StoppedProjectedBuckets.background clauses rows repeats hupper hij designated hrows o)
      (fun o => StoppedProjectedBuckets.scalarLaw clauses rows repeats hupper hij designated hrows o)
      (fun o => StoppedProjectedBuckets.rows_positive rows hupper hrows o) =
      (HierarchicalUsefulFamily.originalLaw S outer).probability
        (HierarchicalUsefulFamily.usefulEvent S κ
          (StoppedProjectedUsefulEvent.upperEvent clauses rows repeats hupper hij designated
            hbranch hrows flag σ)) := by
  have hmean := FiniteDistribution.expectation_congr outer (fun context =>
    (original_probability_eq_usefulProbability clauses rows repeats hupper hij designated
      hbranch hrows flag σ κ context).symm)
  exact hmean.trans (HierarchicalUsefulFamily.useful_probability_eq_mean S outer κ
    (StoppedProjectedUsefulEvent.upperEvent clauses rows repeats hupper hij designated
      hbranch hrows flag σ)).symm

end
end PerfectCompleteness.StoppedProjectedUsefulProbability

end

end OAI
