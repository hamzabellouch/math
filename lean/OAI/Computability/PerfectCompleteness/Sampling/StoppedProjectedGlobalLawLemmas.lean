import OAI.Computability.PerfectCompleteness.Foundations.StoppedProjectedArrays
import OAI.Computability.PerfectCompleteness.Foundations.StoppedProjectedContext

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedGlobalLaw

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n i j t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j) (hi : i + 1 ≤ n)
  (designated : Fin (branch i) → Slots branch i)

abbrev Context := StoppedProjectedContext.Sample (branch := branch) (n := n)
  (i := i) (t := t) (m := m) rows

abbrev Outer := StoppedProjectedExperiment.Outer (branch := branch) (n := n)
  (j := j) (t := t) (m := m)

def projectedSlots (x : Context (branch := branch) (n := n) (i := i) (t := t) (m := m) rows) :=
  StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated
    (StoppedProjectedContext.splitEquiv rows hupper hij x).1
    (StoppedProjectedContext.splitEquiv rows hupper hij x).2

theorem projectedSlots_eq
    (x : Context (branch := branch) (n := n) (i := i) (t := t) (m := m) rows) :
    projectedSlots clauses rows hupper hij designated x =
      CutSlotAssembly.fill (GeometricCutSplit.prefixPath hi x.1.2.1)
        (sourceSlots clauses (PreliminarySampler.endpoints x.1.1))
        (SourceProjectedTag.mixedInside clauses designated
          (fun leaf a => x.1.1 ((GeometricCutSplit.prefixPath hi x.1.2.1).slotEmbedding leaf) a)
          x.2.1 x.2.2) := by
  unfold projectedSlots StoppedProjectedExperiment.projectedSlots
    StoppedProjectedExperiment.cutQuestions
  rw [StoppedProjectedContext.stoppedPath_split rows hupper hij hi x]
  rfl

abbrev Sample :=
  (x : Context (branch := branch) (n := n) (i := i) (t := t) (m := m) rows) ×
    WholeArraySampler.Tape rows repeats (GeometricCutSplit.prefixPath hi x.1.2.1)
      (projectedSlots clauses rows hupper hij designated x)

abbrev ExperimentSample :=
  (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) ×
    HierarchicalProjectedExperiment.Sample (rows := rows) (repeats := repeats)
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
      (StoppedProjectedExperiment.upper hupper o)
      (StoppedProjectedExperiment.lower rows hupper hij o)
      (StoppedProjectedExperiment.cut rows hupper hij o)

def read (sample : Sample (t := t) clauses rows repeats hupper hij hi designated) :
    ExperimentSample (t := t) clauses rows repeats hupper hij designated :=
  let parts := StoppedProjectedContext.splitEquiv rows hupper hij sample.1
  ⟨parts.1, ⟨parts.2, StoppedOwnInputGeometry.pathTapeEquiv rows repeats
    (projectedSlots clauses rows hupper hij designated sample.1)
    (StoppedProjectedContext.fullPath_split_spec rows hupper hij hi sample.1).symm sample.2⟩⟩

variable [NeZero m] (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

def law : FiniteDistribution (Sample (t := t) clauses rows repeats hupper hij hi designated) :=
  CompletionSoundness.sigmaLaw
    ((StoppedSharedSampler.contextLaw (t := t) (m := m) (cut := i) hi hbranch hrows).product
      (SourceProjectedTag.law (t := t) flag))
    (fun x => WholeArraySampler.tapeLaw rows repeats
      (GeometricCutSplit.prefixPath hi x.1.2.1) (projectedSlots clauses rows hupper hij designated x))

abbrev experiment (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :=
  StoppedProjectedExperiment.experiment clauses rows repeats hupper hij designated
    (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag σ o

def experimentLaw : FiniteDistribution (ExperimentSample (t := t) clauses rows repeats hupper hij designated) :=
  CompletionSoundness.sigmaLaw (StoppedProjectedExperiment.outerLaw (t := t) (m := m) hupper hbranch)
    (fun o => (experiment clauses rows repeats hupper hij designated hbranch hrows flag σ o).original)

omit [NeZero m] in
theorem fiber_probability
    (x : Context (branch := branch) (n := n) (i := i) (t := t) (m := m) rows)
    (event : ExperimentSample (t := t) clauses rows repeats hupper hij designated → Bool) :
    (WholeArraySampler.tapeLaw rows repeats (GeometricCutSplit.prefixPath hi x.1.2.1)
      (projectedSlots clauses rows hupper hij designated x)).probability
        (fun tape => event (read clauses rows repeats hupper hij hi designated ⟨x, tape⟩)) =
      (WholeArraySampler.tapeLaw rows repeats
        (WholeArrayInteriorOwnInputLaw.fullPath
          (StoppedProjectedExperiment.upper hupper (StoppedProjectedContext.splitEquiv rows hupper hij x).1)
          (StoppedProjectedExperiment.lower rows hupper hij
            (StoppedProjectedContext.splitEquiv rows hupper hij x).1
            (StoppedProjectedContext.splitEquiv rows hupper hij x).2)
          (StoppedProjectedExperiment.cut rows hupper hij
            (StoppedProjectedContext.splitEquiv rows hupper hij x).1
            (StoppedProjectedContext.splitEquiv rows hupper hij x).2))
        (projectedSlots clauses rows hupper hij designated x)).probability
          (fun tape => event ⟨(StoppedProjectedContext.splitEquiv rows hupper hij x).1,
            ⟨(StoppedProjectedContext.splitEquiv rows hupper hij x).2, tape⟩⟩) := by
  let observed := fun tape => event
    (⟨(StoppedProjectedContext.splitEquiv rows hupper hij x).1,
      ⟨(StoppedProjectedContext.splitEquiv rows hupper hij x).2, tape⟩⟩ :
        ExperimentSample (t := t) clauses rows repeats hupper hij designated)
  have h := congrArg (fun μ => FiniteDistribution.probability μ observed)
    (StoppedOwnInputGeometry.pathTapeEquiv_law rows repeats
      (projectedSlots clauses rows hupper hij designated x)
      (StoppedProjectedContext.fullPath_split_spec rows hupper hij hi x).symm)
  exact (FiniteDistribution.probability_pushforward
    (WholeArraySampler.tapeLaw rows repeats (GeometricCutSplit.prefixPath hi x.1.2.1)
      (projectedSlots clauses rows hupper hij designated x))
    (StoppedOwnInputGeometry.pathTapeEquiv rows repeats
      (projectedSlots clauses rows hupper hij designated x)
      (StoppedProjectedContext.fullPath_split_spec rows hupper hij hi x).symm)
    observed).symm.trans h

theorem probability_read
    (event : ExperimentSample (t := t) clauses rows repeats hupper hij designated → Bool) :
    (law clauses rows repeats hupper hij hi designated hbranch hrows flag).probability
        (fun sample => event (read clauses rows repeats hupper hij hi designated sample)) =
      (experimentLaw clauses rows repeats hupper hij designated hbranch hrows flag σ).probability event := by
  unfold law
  rw [CompletionSoundness.sigmaLaw_probability]
  let value := fun z : StoppedProjectedContext.SplitSample
      (branch := branch) (n := n) (i := i) (j := j) (t := t) (m := m) rows =>
    (WholeArraySampler.tapeLaw rows repeats
      (WholeArrayInteriorOwnInputLaw.fullPath (StoppedProjectedExperiment.upper hupper z.1)
        (StoppedProjectedExperiment.lower rows hupper hij z.1 z.2)
        (StoppedProjectedExperiment.cut rows hupper hij z.1 z.2))
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated z.1 z.2)).probability
      (fun tape => event ⟨z.1, ⟨z.2, tape⟩⟩)
  calc
    _ = ((StoppedSharedSampler.contextLaw (t := t) (m := m) (cut := i) hi hbranch hrows).product
        (SourceProjectedTag.law (t := t) flag)).expectation
          (fun x => value (StoppedProjectedContext.splitEquiv rows hupper hij x)) := by
      apply FiniteDistribution.expectation_congr
      intro x
      exact fiber_probability clauses rows repeats hupper hij hi designated x event
    _ = ((StoppedProjectedExperiment.outerLaw (t := t) (m := m) hupper hbranch).product
        (StoppedProjectedExperiment.innerLaw rows hij
          (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag)).expectation value :=
      StoppedProjectedContext.expectation_split rows hupper hij hi hbranch hrows flag value
    _ = _ := by
      simp only [experimentLaw, experiment, StoppedProjectedExperiment.experiment,
        HierarchicalProjectedExperiment.experiment, HierarchicalProjectedExperiment.originalLaw,
        CompletionSoundness.sigmaLaw_probability, FiniteDistribution.expectation_product]
      rfl

theorem read_law :
    (law clauses rows repeats hupper hij hi designated hbranch hrows flag).pushforward
        (read clauses rows repeats hupper hij hi designated) =
      experimentLaw clauses rows repeats hupper hij designated hbranch hrows flag σ := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward]
  exact probability_read clauses rows repeats hupper hij hi designated hbranch hrows flag σ event

omit [NeZero m] in
theorem arrays_read
    (sample : Sample (t := t) clauses rows repeats hupper hij hi designated) :
    (experiment clauses rows repeats hupper hij designated hbranch hrows flag σ
      (read clauses rows repeats hupper hij hi designated sample).1).arrays
        (read clauses rows repeats hupper hij hi designated sample).2 =
      ChildBlockProjection.arraysPullback rows
        (StoppedProjectedExperiment.projection clauses rows hupper hij designated
          (StoppedProjectedContext.splitEquiv rows hupper hij sample.1).1
          (StoppedProjectedContext.splitEquiv rows hupper hij sample.1).2)
        (WholeArraySampler.evaluate rows repeats (GeometricCutSplit.prefixPath hi sample.1.1.2.1)
          (projectedSlots clauses rows hupper hij designated sample.1) sample.2) :=
  congrArg (ChildBlockProjection.arraysPullback rows
    (StoppedProjectedExperiment.projection clauses rows hupper hij designated
      (StoppedProjectedContext.splitEquiv rows hupper hij sample.1).1
      (StoppedProjectedContext.splitEquiv rows hupper hij sample.1).2))
    (StoppedOwnInputGeometry.evaluate_pathTapeEquiv rows repeats
      (projectedSlots clauses rows hupper hij designated sample.1)
      (StoppedProjectedContext.fullPath_split_spec rows hupper hij hi sample.1).symm sample.2)

end
end PerfectCompleteness.StoppedProjectedGlobalLaw

end

section

namespace PerfectCompleteness.StoppedProjectedPhysicalLaw

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n i j t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)

abbrev Outer := StoppedProjectedExperiment.Outer (branch := branch) (n := n)
  (j := j) (t := t) (m := m)

abbrev Sample :=
  (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) ×
    StoppedProjectedExperiment.PhysicalSample clauses rows repeats hupper hij designated o

def read (sample : Sample (t := t) clauses rows repeats hupper hij designated) :
    StoppedProjectedGlobalLaw.ExperimentSample (t := t) clauses rows repeats hupper hij designated :=
  ⟨sample.1, StoppedProjectedExperiment.physicalExperimentRead
    clauses rows repeats hupper hij designated sample.1 sample.2⟩

variable [NeZero m]
  (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

def law : FiniteDistribution (Sample (t := t) clauses rows repeats hupper hij designated) :=
  CompletionSoundness.sigmaLaw (StoppedProjectedExperiment.outerLaw (t := t) (m := m) hupper hbranch)
    (StoppedProjectedExperiment.physicalLaw clauses rows repeats hupper hij designated
      (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag)

theorem read_law :
    (law clauses rows repeats hupper hij designated hbranch hrows flag).pushforward
        (read clauses rows repeats hupper hij designated) =
      StoppedProjectedGlobalLaw.experimentLaw clauses rows repeats hupper hij designated
        hbranch hrows flag σ := by
  unfold law read
  rw [SigmaObservation.pushforward_fiber]
  unfold StoppedProjectedGlobalLaw.experimentLaw
  congr 1
  funext o
  exact StoppedProjectedExperiment.physicalExperimentRead_law
    clauses rows repeats hupper hij designated
    (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag σ o

theorem expectation_read
    (value : StoppedProjectedGlobalLaw.ExperimentSample (t := t)
      clauses rows repeats hupper hij designated → ℝ) :
    (law clauses rows repeats hupper hij designated hbranch hrows flag).expectation
        (fun sample => value (read clauses rows repeats hupper hij designated sample)) =
      (StoppedProjectedGlobalLaw.experimentLaw clauses rows repeats hupper hij designated
        hbranch hrows flag σ).expectation value := by
  rw [← read_law clauses rows repeats hupper hij designated hbranch hrows flag σ]
  exact (FiniteDistribution.expectation_pushforward _ _ _).symm

theorem probability_read
    (event : StoppedProjectedGlobalLaw.ExperimentSample (t := t)
      clauses rows repeats hupper hij designated → Bool) :
    (law clauses rows repeats hupper hij designated hbranch hrows flag).probability
        (fun sample => event (read clauses rows repeats hupper hij designated sample)) =
      (StoppedProjectedGlobalLaw.experimentLaw clauses rows repeats hupper hij designated
        hbranch hrows flag σ).probability event := by
  rw [← read_law clauses rows repeats hupper hij designated hbranch hrows flag σ,
    FiniteDistribution.probability_pushforward]

omit [NeZero m] in
theorem arrays_read_heq (sample : Sample (t := t) clauses rows repeats hupper hij designated) :
    HEq ((StoppedProjectedGlobalLaw.experiment clauses rows repeats hupper hij designated
        hbranch hrows flag σ sample.1).arrays
      (read clauses rows repeats hupper hij designated sample).2)
      (StoppedProjectedArrays.physicalArrays clauses rows repeats hupper hij designated
        sample.1 sample.2) :=
  StoppedProjectedArrays.arrays_physicalExperimentRead_heq
    clauses rows repeats hupper hij designated
    (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag σ sample.1 sample.2

end
end PerfectCompleteness.StoppedProjectedPhysicalLaw

end

end OAI
