import OAI.Computability.PerfectCompleteness.Construction.HierarchicalAdviceFromBuckets
import OAI.Computability.PerfectCompleteness.Construction.StoppedProjectedBucketIndex
import OAI.Computability.PerfectCompleteness.Foundations.StoppedPathHead
import OAI.Computability.PerfectCompleteness.Sampling.StoppedUsefulPairLaw

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedBuckets

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
  (hrows : ∀ k, 0 < rows (k + 1))
  (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))

abbrev Base := StoppedProjectedBucketIndex.Base (branch := branch) (i := i) (j := j) (t := t)

abbrev key (base : Base (branch := branch) (i := i) (j := j) (t := t)) :=
  StoppedProjectedBucketIndex.key (n := n) rows hrows base

abbrev lowerPath (base : Base (branch := branch) (i := i) (j := j) (t := t)) :=
  StoppedProjectedExperiment.lowerPath rows hij (key (n := n) rows hrows base)

def chosen (base : Base (branch := branch) (i := i) (j := j) (t := t)) : Fin (branch j) :=
  StoppedPathHead.child hij (lowerPath (n := n) rows hij hrows base)

def continuation (base : Base (branch := branch) (i := i) (j := j) (t := t)) :
    Path branch j (i + 1) :=
  StoppedPathHead.tail hij (lowerPath (n := n) rows hij hrows base)

theorem lowerPath_eq_step (base : Base (branch := branch) (i := i) (j := j) (t := t)) :
    lowerPath (n := n) rows hij hrows base =
      .step (chosen (n := n) rows hij hrows base) (continuation (n := n) rows hij hrows base) :=
  StoppedPathHead.step_eq hij _

abbrev projected (base : Base (branch := branch) (i := i) (j := j) (t := t)) :=
  StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o
    (key (n := n) rows hrows base)

abbrev projection (base : Base (branch := branch) (i := i) (j := j) (t := t)) :=
  StoppedProjectedExperiment.projection clauses rows hupper hij designated o
    (key (n := n) rows hrows base)

abbrev Exterior (base : Base (branch := branch) (i := i) (j := j) (t := t)) :=
  StoppedUsefulPairLaw.Descriptor rows repeats (StoppedProjectedExperiment.upperPath hupper o)
    (chosen (n := n) rows hij hrows base) (continuation (n := n) rows hij hrows base)
    (projected clauses rows hupper hij designated hrows o base)

abbrev Descriptor := (base : Base (branch := branch) (i := i) (j := j) (t := t)) ×
  Exterior clauses rows repeats hupper hij designated hrows o base

def exteriorLaw (base : Base (branch := branch) (i := i) (j := j) (t := t)) :
    FiniteDistribution (Exterior clauses rows repeats hupper hij designated hrows o base) :=
  StoppedUsefulPairLaw.externalLaw rows repeats (StoppedProjectedExperiment.upperPath hupper o)
    (chosen (n := n) rows hij hrows base) (continuation (n := n) rows hij hrows base)
    (projected clauses rows hupper hij designated hrows o base)

def externalLaw (hbranch : ∀ k < j + 1, 0 < branch k)
    (flag : Fin (branch i) → FiniteDistribution Bool) :
    FiniteDistribution (Descriptor clauses rows repeats hupper hij designated hrows o) :=
  CompletionSoundness.sigmaLaw
    (StoppedProjectedBucketIndex.baseLaw (t := t) hij hbranch flag)
    (exteriorLaw clauses rows repeats hupper hij designated hrows o)

local instance backgroundFintype : Fintype (HierarchicalMatrixTable.Background (rows := rows)
    (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)) :=
  Fintype.ofFinite _

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace
    (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)) :=
  Fintype.ofFinite _

def background (descriptor : Descriptor clauses rows repeats hupper hij designated hrows o) :
    HierarchicalMatrixTable.Background (rows := rows)
      (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o) :=
  StoppedUsefulPairLaw.background rows repeats (StoppedProjectedExperiment.upperPath hupper o)
    (chosen (n := n) rows hij hrows descriptor.1)
    (continuation (n := n) rows hij hrows descriptor.1)
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (projected clauses rows hupper hij designated hrows o descriptor.1)
    (projection clauses rows hupper hij designated hrows o descriptor.1) descriptor.2

def scalarLaw (descriptor : Descriptor clauses rows repeats hupper hij designated hrows o) :
    FiniteDistribution (NodeEmbedding.RowSpace
      (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)) :=
  StoppedUsefulPairLaw.scalarLaw rows repeats (StoppedProjectedExperiment.upperPath hupper o)
    (chosen (n := n) rows hij hrows descriptor.1)
    (continuation (n := n) rows hij hrows descriptor.1)
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (projected clauses rows hupper hij designated hrows o descriptor.1)
    (projection clauses rows hupper hij designated hrows o descriptor.1) descriptor.2

variable (hbranch : ∀ k < j + 1, 0 < branch k)
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

abbrev experiment :=
  StoppedProjectedExperiment.experiment clauses rows repeats hupper hij designated
    hbranch hrows flag σ o

include hrows in
theorem rows_positive : 0 < rows (Nodes.height (StoppedProjectedExperiment.upper hupper o)) := by
  rw [StoppedProjectedExperiment.upper_height]
  exact hrows j

def usefulProbability (κ : ℝ) : ℝ :=
  HierarchicalAdviceFromBuckets.usefulProbability
    (experiment clauses rows repeats hupper hij designated hrows o hbranch flag σ) κ
    (externalLaw clauses rows repeats hupper hij designated hrows o hbranch flag)
    (background clauses rows repeats hupper hij designated hrows o)
    (scalarLaw clauses rows repeats hupper hij designated hrows o)
    (rows_positive rows hupper hrows o)

theorem usefulProbability_eq_mean (κ : ℝ) :
    usefulProbability clauses rows repeats hupper hij designated hrows o hbranch flag σ κ =
      (StoppedProjectedBucketIndex.baseLaw (t := t) hij hbranch flag).expectation (fun base =>
        HierarchicalAdviceFromBuckets.usefulProbability
          (experiment clauses rows repeats hupper hij designated hrows o hbranch flag σ) κ
          (exteriorLaw clauses rows repeats hupper hij designated hrows o base)
          (fun external => background clauses rows repeats hupper hij designated hrows o
            ⟨base, external⟩)
          (fun external => scalarLaw clauses rows repeats hupper hij designated hrows o
            ⟨base, external⟩)
          (rows_positive rows hupper hrows o)) := by
  simp only [usefulProbability, HierarchicalAdviceFromBuckets.usefulProbability,
    HierarchicalUsefulCollision.law, CompletionSoundness.sigmaLaw_probability,
    externalLaw, CandidateCoupling.expectation_sigmaLaw,
    HierarchicalUsefulCollision.usefulEvent]

end
end PerfectCompleteness.StoppedProjectedBuckets

end

end OAI
