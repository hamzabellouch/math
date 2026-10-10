import OAI.Computability.PerfectCompleteness.Foundations.StoppedProjectedUsefulEvent

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedUsefulAverage

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
  (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))

local notation "S" => StoppedProjectedExperiment.experiment clauses rows repeats hupper hij
  designated hbranch hrows flag σ

def bucketEvent
    (base : StoppedProjectedBucketIndex.Base (branch := branch) (i := i) (j := j) (t := t))
    (direction : PrefixTests.LevelDirection rows (StoppedProjectedUsefulEvent.upperLevel hupper))
    (tape : StoppedProjectedBucketIndex.Tape clauses rows repeats hupper hij designated hrows o base) : Bool :=
  let sample : StoppedProjectedExperiment.TapeSample clauses rows repeats hupper hij designated o :=
    ⟨StoppedProjectedBucketIndex.key (n := n) rows hrows base, tape⟩
  HierarchicalUsefulCollision.usefulAccepted
    (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)
    (i + 1) (S o).original (S o).arrays (HierarchicalAdviceExperiment.lowerEvent (S o)) κ σ
    (StoppedProjectedUsefulEvent.background clauses rows repeats hupper hij designated o sample)
    (StoppedProjectedUsefulEvent.upperDirection rows hupper o direction)
    (StoppedProjectedUsefulEvent.buckets clauses rows repeats hupper hij designated o sample)

def mean : ℝ :=
  (StoppedProjectedBucketIndex.baseLaw (t := t) hij hbranch flag).expectation (fun base =>
    (CanonicalDirections.levelLaw rows hrows (StoppedProjectedUsefulEvent.upperLevel hupper)).expectation
      (fun direction =>
        (StoppedProjectedBucketIndex.tapeLaw clauses rows repeats hupper hij designated hrows o base).probability
          (bucketEvent clauses rows repeats hupper hij designated hbranch hrows flag σ κ o base direction)))

theorem usefulEvent_eq_bucketEvent
    (sample : StoppedProjectedExperiment.TapeSample clauses rows repeats hupper hij designated o) :
    HierarchicalUsefulFamily.usefulEvent S κ
        (StoppedProjectedUsefulEvent.upperEvent clauses rows repeats hupper hij designated
          hbranch hrows flag σ)
        ⟨o, StoppedProjectedExperiment.tapeRead clauses rows repeats hupper hij designated o sample⟩ =
      bucketEvent clauses rows repeats hupper hij designated hbranch hrows flag σ κ o
        (StoppedProjectedBucketIndex.baseOf rows sample.1)
        (sample.1.2.2 (StoppedProjectedUsefulEvent.upperLevel hupper)) sample.2 := by
  exact StoppedProjectedUsefulEvent.usefulEvent_eq clauses rows repeats hupper hij designated
    hbranch hrows flag σ κ o sample

theorem original_probability_eq_mean :
    (S o).original.probability (fun x =>
      HierarchicalUsefulFamily.usefulEvent S κ
        (StoppedProjectedUsefulEvent.upperEvent clauses rows repeats hupper hij designated
          hbranch hrows flag σ) ⟨o, x⟩) =
      mean clauses rows repeats hupper hij designated hbranch hrows flag σ κ o := by
  rw [← StoppedProjectedExperiment.tapeRead_law clauses rows repeats hupper hij designated
    hbranch hrows flag σ o, FiniteDistribution.probability_pushforward,
    CandidateCoupling.probability_eq_expectation]
  calc
    _ = (StoppedProjectedExperiment.tapeLaw clauses rows repeats hupper hij designated
        hbranch hrows flag o).expectation (fun sample =>
          if bucketEvent clauses rows repeats hupper hij designated hbranch hrows flag σ κ o
            (StoppedProjectedBucketIndex.baseOf rows sample.1)
            (sample.1.2.2 (StoppedProjectedUsefulEvent.upperLevel hupper)) sample.2 then 1 else 0) := by
      apply FiniteDistribution.expectation_congr
      intro sample
      rw [usefulEvent_eq_bucketEvent]
    _ = _ := by
      have hcoordinate := StoppedProjectedBucketIndex.expectation_coordinate
        clauses rows repeats hupper hij designated hrows o hbranch flag
        (StoppedProjectedUsefulEvent.upperLevel hupper)
        (fun base direction tape =>
          if bucketEvent clauses rows repeats hupper hij designated hbranch hrows flag σ κ o
            base direction tape then (1 : ℝ) else 0)
      exact hcoordinate.trans (by
        unfold mean
        simp only [CandidateCoupling.probability_eq_expectation])

end
end PerfectCompleteness.StoppedProjectedUsefulAverage

end

end OAI
