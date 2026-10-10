import OAI.Computability.PerfectCompleteness.Algebra.PrefixMatrixAcceptance
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalAdviceExperimentLemmas
import OAI.Computability.PerfectCompleteness.Reduction.FixedPhysicalStoppedComparison
import OAI.Computability.PerfectCompleteness.Reduction.FixedStoppedPair
import OAI.Computability.PerfectCompleteness.Repetition.CutChildCleanLawLemmas
import OAI.Computability.PerfectCompleteness.Sampling.StoppedProjectedGlobalLawLemmas

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedUsefulMass

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

private theorem probability_cast_array_law
    {branch : Nat → Nat} {n h t : Nat} (rows repeats : Nat → Nat)
    (p : Path branch n (h + 1))
    {slots slots' : Slots branch n → Fin t → MixedSupport.Slot}
    (hs : slots = slots') (event : Arrays slots' rows → Bool) :
    (WholeArraySampler.law rows repeats p slots).probability
        (fun arrays => event (cast (congrArg (fun s => Arrays s rows) hs) arrays)) =
      (WholeArraySampler.law rows repeats p slots').probability event := by
  cases hs
  rfl

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

abbrev clauses := PCPSource.clauseFamily (BinaryLanguage.totalRename input)

abbrev Outer := StoppedProjectedExperiment.Outer
  (branch := FixedParameters.branch parameters) (n := parameters.plan.depth)
  (j := j.val) (t := FixedRows.sourceLength parameters.plan hδ)
  (m := (PCPSource.normalizedFormula (BinaryLanguage.totalRename input)).clauses.length)

abbrev Base := StoppedProjectedExperiment.PhysicalBase
  (branch := FixedParameters.branch parameters) (n := parameters.plan.depth)
  (i := i.val) (j := j.val) (t := FixedRows.sourceLength parameters.plan hδ)
  (FixedRows.rows parameters.plan)

def flags : Fin (FixedParameters.branch parameters i.val) → FiniteDistribution Bool :=
  fun _ => ProjectionPosterior.bernoulli (FixedParameters.projectionProbability parameters i.val : ℝ)
    (FixedPhysicalStoppedComparison.beta_nonneg parameters)
    (FixedPhysicalStoppedComparison.beta_le_one parameters)

theorem flags_eq_projectionFlag (hcube : 0 < parameters.cubeSize i.val) :
    flags parameters i = fun _ =>
      ProjectedCleanRate.projectionFlag (parameters.cubeSize i.val) hcube := by
  have hprob : (FixedParameters.projectionProbability parameters i.val : ℝ) =
      ProjectedCleanRate.projectionDensity (parameters.cubeSize i.val) := by
    simp [FixedParameters.projectionProbability, ProjectedCleanRate.projectionDensity]
  funext child
  apply FiniteDistribution.eq_of_weight_eq
  intro b
  cases b <;> simp [flags, ProjectionPosterior.bernoulli,
    ProjectedCleanRate.projectionFlag, RepetitionRate.bernoulli, hprob]

def outerLaw : FiniteDistribution (Outer parameters j input) :=
  StoppedProjectedExperiment.outerLaw (Nat.succ_le_of_lt j.isLt)
    (fun k _ => FixedParameters.branch_pos parameters k)

def baseLaw : FiniteDistribution (Base parameters i j) :=
  StoppedProjectedExperiment.physicalBaseLaw (FixedRows.rows parameters.plan) hij
    (fun k _ => FixedParameters.branch_pos parameters k)
    (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1))

def record (o : Outer parameters j input)
    (pref : GeometricCutSplit.Prefix (FixedParameters.branch parameters) (j.val + 1) (i.val + 1))
    (directions : CanonicalDirections.Tuple (FixedRows.rows parameters.plan) parameters.plan.depth)
    (arrays : Arrays (StoppedProjectedExperiment.nativeSlots (clauses input) o)
      (FixedRows.rows parameters.plan)) :
    StoppedSharedSampler.Record (clauses input) (FixedParameters.branch parameters)
      parameters.plan.depth (FixedRows.sourceLength parameters.plan hδ) i.val
      (FixedRows.rows parameters.plan) :=
  ⟨(o.1, (GeometricPrefixSplit.joinEquiv (Nat.succ_le_succ hij.le)
      (Nat.succ_le_of_lt j.isLt) (o.2, pref), directions)), arrays⟩

variable (designated : Fin (FixedParameters.branch parameters i.val) →
  Slots (FixedParameters.branch parameters) i.val)

abbrev PhysicalSample := StoppedProjectedPhysicalLaw.Sample
  (t := FixedRows.sourceLength parameters.plan hδ)
  (clauses input) (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
  (Nat.succ_le_of_lt j.isLt) hij designated

abbrev OriginalSample := StoppedProjectedGlobalLaw.ExperimentSample
  (t := FixedRows.sourceLength parameters.plan hδ)
  (clauses input) (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
  (Nat.succ_le_of_lt j.isLt) hij designated

def physicalLaw : FiniteDistribution (PhysicalSample parameters i j hij input designated) :=
  StoppedProjectedPhysicalLaw.law
    (clauses input) (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij designated
    (fun k _ => FixedParameters.branch_pos parameters k)
    (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1)) (flags parameters i)

def physicalRecord (sample : PhysicalSample parameters i j hij input designated) :=
  record parameters i j hij input sample.1 sample.2.1.1 sample.2.1.2.2
    (cast (congrArg (fun slots => Arrays slots (FixedRows.rows parameters.plan))
      (StoppedProjectedArrays.nativeSlots_eq (clauses input) (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij designated sample.1 sample.2.1))
      (StoppedProjectedArrays.physicalArrays (clauses input) (FixedRows.rows parameters.plan)
        (FixedRows.repeats parameters.plan) (Nat.succ_le_of_lt j.isLt) hij designated
        sample.1 sample.2))

def referenceMass (event : StoppedSharedSampler.Record (clauses input)
    (FixedParameters.branch parameters) parameters.plan.depth
    (FixedRows.sourceLength parameters.plan hδ) i.val (FixedRows.rows parameters.plan) → Bool) : ℝ :=
  (outerLaw parameters j input).expectation (fun o =>
    (baseLaw parameters i j hij).expectation (fun base =>
      (WholeArraySampler.law (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
        (StoppedProjectedExperiment.stoppedPath (FixedRows.rows parameters.plan)
          (Nat.succ_le_of_lt j.isLt) hij o
          (StoppedProjectedExperiment.baseTag (FixedRows.rows parameters.plan) base))
        (StoppedProjectedExperiment.nativeSlots (clauses input) o)).probability
          (fun arrays => event (record parameters i j hij input o base.1 base.2.2 arrays))))

theorem physical_fiber_probability_lower
    (o : Outer parameters j input) (base : Base parameters i j)
    (event : StoppedSharedSampler.Record (clauses input) (FixedParameters.branch parameters)
      parameters.plan.depth (FixedRows.sourceLength parameters.plan hδ) i.val
      (FixedRows.rows parameters.plan) → Bool) :
    (WholeArraySampler.law (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
      (StoppedProjectedExperiment.stoppedPath (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij o
        (StoppedProjectedExperiment.baseTag (FixedRows.rows parameters.plan) base))
      (StoppedProjectedExperiment.nativeSlots (clauses input) o)).probability
        (fun arrays => event (record parameters i j hij input o base.1 base.2.2 arrays)) -
      parameters.accuracy ≤
    (StoppedProjectedExperiment.physicalFiberLaw (clauses input) (FixedRows.rows parameters.plan)
      (FixedRows.repeats parameters.plan) (Nat.succ_le_of_lt j.isLt) hij designated
      (flags parameters i) o base).probability
        (fun raw => event (physicalRecord parameters i j hij input designated ⟨o, ⟨base, raw⟩⟩)) := by
  let p := StoppedProjectedExperiment.stoppedPath (FixedRows.rows parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij o
    (StoppedProjectedExperiment.baseTag (FixedRows.rows parameters.plan) base)
  let outside := StoppedProjectedExperiment.nativeSlots (clauses input) o
  let placeholder := SourceProjectedTag.originalSlots (clauses input)
    (StoppedProjectedExperiment.cutQuestions (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij o
      (StoppedProjectedExperiment.baseTag (FixedRows.rows parameters.plan) base))
  let sources := StoppedProjectedExperiment.physicalSources (FixedRows.rows parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij designated o base
  have hslots : CutSlotAssembly.fill p outside
      (SourceChildKernel.parentLeftSlots (clauses input) designated sources) = outside := by
    simpa only [p, outside, sources, SourcePhysicalTapeLaw.nativeSlots] using
      (StoppedProjectedArrays.nativeSlots_eq (clauses input) (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij designated o base)
  let observed := fun arrays : SourcePhysicalStoppedComparison.NativeArrays
      (FixedRows.rows parameters.plan) p outside (clauses input) designated sources =>
    event (record parameters i j hij input o base.1 base.2.2
      (cast (congrArg (fun slots => Arrays slots (FixedRows.rows parameters.plan)) hslots) arrays))
  have htv := SourcePhysicalStoppedComparison.conditional_variation
    (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan) p outside placeholder
    (clauses input) designated (FixedParameters.branch_pos parameters i.val) sources
    (FixedParameters.projectionProbability parameters i.val : ℝ)
    (FixedPhysicalStoppedComparison.beta_nonneg parameters)
    (FixedPhysicalStoppedComparison.beta_le_one parameters)
  have herror : SourceChildProjectionComparison.error (FixedParameters.branch parameters)
      i.val (FixedRows.sourceLength parameters.plan hδ)
      (Fintype.card (WholeCutCalls.Index (FixedRows.rows parameters.plan)
        (FixedRows.repeats parameters.plan) p)) (FixedRows.rows parameters.plan)
      (FixedParameters.projectionProbability parameters i.val : ℝ) < parameters.accuracy := by
    simpa only [SourceChildProjectionComparison.error] using
      FixedProjectionError.sparse_error_lt parameters
        (FixedPhysicalStoppedComparison.calls_le parameters p (le_refl _)) i.val
  have hp := FiniteDistribution.probability_le_add_totalVariation
    (SourcePhysicalStoppedComparison.stoppedLaw (FixedRows.rows parameters.plan)
      (FixedRows.repeats parameters.plan) p outside (clauses input) designated sources)
    (SourcePhysicalStoppedComparison.modifiedLaw (FixedRows.rows parameters.plan)
      (FixedRows.repeats parameters.plan) p outside placeholder (clauses input) designated
      (FixedParameters.projectionProbability parameters i.val : ℝ)
      (FixedPhysicalStoppedComparison.beta_nonneg parameters)
      (FixedPhysicalStoppedComparison.beta_le_one parameters) sources) observed
  rw [FiniteDistribution.totalVariation_comm] at hp
  have hreference :
      (SourcePhysicalStoppedComparison.stoppedLaw (FixedRows.rows parameters.plan)
        (FixedRows.repeats parameters.plan) p outside (clauses input) designated sources).probability
        observed =
      (WholeArraySampler.law (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
        p outside).probability
        (fun arrays => event (record parameters i j hij input o base.1 base.2.2 arrays)) := by
    simpa only [SourcePhysicalStoppedComparison.stoppedLaw, observed] using
      (probability_cast_array_law (FixedRows.rows parameters.plan)
        (FixedRows.repeats parameters.plan) p
        (slots := CutSlotAssembly.fill p outside
          (SourceChildKernel.parentLeftSlots (clauses input) designated sources))
        (slots' := outside) hslots
        (fun arrays => event (record parameters i j hij input o base.1 base.2.2 arrays)))
  have hstrict := htv.trans_lt herror
  have hbound :
      (SourcePhysicalStoppedComparison.stoppedLaw (FixedRows.rows parameters.plan)
        (FixedRows.repeats parameters.plan) p outside (clauses input) designated sources).probability
        observed - parameters.accuracy ≤
      (SourcePhysicalStoppedComparison.modifiedLaw (FixedRows.rows parameters.plan)
        (FixedRows.repeats parameters.plan) p outside placeholder (clauses input) designated
        (FixedParameters.projectionProbability parameters i.val : ℝ)
        (FixedPhysicalStoppedComparison.beta_nonneg parameters)
        (FixedPhysicalStoppedComparison.beta_le_one parameters) sources).probability observed :=
    sub_le_iff_le_add.mpr (hp.trans (add_le_add (le_refl _) hstrict.le))
  rw [hreference, SourcePhysicalStoppedComparison.modifiedLaw,
    FiniteDistribution.probability_pushforward] at hbound
  change (WholeArraySampler.law (FixedRows.rows parameters.plan)
      (FixedRows.repeats parameters.plan) p outside).probability
        (fun arrays => event (record parameters i j hij input o base.1 base.2.2 arrays)) -
      parameters.accuracy ≤
    (SourcePhysicalWholeLaw.rawLaw (FixedRows.rows parameters.plan)
      (FixedRows.repeats parameters.plan) p outside placeholder (clauses input) designated
      (fun _ => ProjectionPosterior.bernoulli
        (FixedParameters.projectionProbability parameters i.val : ℝ)
        (FixedPhysicalStoppedComparison.beta_nonneg parameters)
        (FixedPhysicalStoppedComparison.beta_le_one parameters)) sources).probability
        (fun raw => observed (SourcePhysicalWholeLaw.observeLeft (FixedRows.rows parameters.plan)
          (FixedRows.repeats parameters.plan) p outside placeholder (clauses input) designated sources raw))
  exact hbound

theorem physical_probability_lower
    (event : StoppedSharedSampler.Record (clauses input) (FixedParameters.branch parameters)
      parameters.plan.depth (FixedRows.sourceLength parameters.plan hδ) i.val
      (FixedRows.rows parameters.plan) → Bool) :
    referenceMass parameters i j hij input event - parameters.accuracy ≤
      (physicalLaw parameters i j hij input designated).probability
        (fun sample => event (physicalRecord parameters i j hij input designated sample)) := by
  have hmean := SmallBias.expectation_mono (outerLaw parameters j input) (fun o =>
    SmallBias.expectation_mono (baseLaw parameters i j hij) (fun base =>
      physical_fiber_probability_lower parameters i j hij input designated o base event))
  simp only [DensityVariation.expectation_sub, SmallBias.expectation_const] at hmean
  simpa only [referenceMass, physicalLaw, StoppedProjectedPhysicalLaw.law,
    StoppedProjectedExperiment.physicalLaw, CompletionSoundness.sigmaLaw_probability,
    outerLaw, baseLaw] using hmean

theorem referenceMass_eq_stopped
    (event : StoppedSharedSampler.Record (clauses input)
      (FixedParameters.branch parameters) parameters.plan.depth
      (FixedRows.sourceLength parameters.plan hδ) i.val
      (FixedRows.rows parameters.plan) → Bool) :
    referenceMass parameters i j hij input event =
      (StoppedSharedSampler.stoppedLaw (clauses input)
        (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
        (Nat.succ_le_of_lt i.isLt)
        (fun k _ => FixedParameters.branch_pos parameters k)
        (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1))).probability event := by
  simp only [referenceMass, outerLaw, baseLaw,
    StoppedProjectedExperiment.outerLaw, StoppedProjectedExperiment.physicalBaseLaw,
    StoppedSharedSampler.stoppedLaw, CompletionSoundness.sigmaLaw_probability,
    StoppedSharedSampler.contextLaw, FiniteDistribution.expectation_product]
  apply FiniteDistribution.expectation_congr
  intro questions
  simp only [record, StoppedProjectedExperiment.stoppedPath,
    StoppedProjectedExperiment.upperPath, StoppedProjectedExperiment.lowerPath,
    StoppedProjectedExperiment.baseTag, StoppedProjectedExperiment.withFlags,
    StoppedProjectedExperiment.nativeSlots, SmallBias.expectation_const]
  let value := fun
      (upper : GeometricCutSplit.Prefix (FixedParameters.branch parameters)
        parameters.plan.depth (j.val + 1))
      (lower : GeometricCutSplit.Prefix (FixedParameters.branch parameters)
        (j.val + 1) (i.val + 1)) =>
    (CanonicalDirections.law (FixedRows.rows parameters.plan) parameters.plan.depth
      (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1))).expectation
      (fun directions =>
        (WholeArraySampler.law (FixedRows.rows parameters.plan)
          (FixedRows.repeats parameters.plan)
          ((GeometricCutSplit.prefixPath (Nat.succ_le_of_lt j.isLt) upper).append
            (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lower))
          (sourceSlots (clauses input) (PreliminarySampler.endpoints questions))).probability
          (fun arrays => event
            ⟨(questions, (GeometricPrefixSplit.joinEquiv (Nat.succ_le_succ hij.le)
              (Nat.succ_le_of_lt j.isLt) (upper, lower), directions)), arrays⟩))
  calc
    _ = (GeometricCutSplit.prefixLaw (Nat.succ_le_of_lt i.isLt)
        (fun k _ => FixedParameters.branch_pos parameters k)).expectation
        (fun pref => value
          (GeometricPrefixSplit.splitEquiv (Nat.succ_le_succ hij.le)
            (Nat.succ_le_of_lt j.isLt) pref).1
          (GeometricPrefixSplit.splitEquiv (Nat.succ_le_succ hij.le)
            (Nat.succ_le_of_lt j.isLt) pref).2) :=
      (GeometricPrefixSplit.expectation_split (Nat.succ_le_succ hij.le)
        (Nat.succ_le_of_lt j.isLt)
        (fun k _ => FixedParameters.branch_pos parameters k) value).symm
    _ = _ := by
      apply FiniteDistribution.expectation_congr
      intro pref
      dsimp only [value]
      rw [← GeometricPrefixSplit.prefixPath_split (Nat.succ_le_succ hij.le)
        (Nat.succ_le_of_lt j.isLt) pref, GeometricPrefixSplit.join_split]

theorem stopped_probability_lower
    (event : StoppedSharedSampler.Record (clauses input) (FixedParameters.branch parameters)
      parameters.plan.depth (FixedRows.sourceLength parameters.plan hδ) i.val
      (FixedRows.rows parameters.plan) → Bool) :
    (StoppedSharedSampler.stoppedLaw (clauses input)
      (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
      (Nat.succ_le_of_lt i.isLt) (fun k _ => FixedParameters.branch_pos parameters k)
      (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1))).probability event -
        parameters.accuracy ≤
      (physicalLaw parameters i j hij input designated).probability
        (fun sample => event (physicalRecord parameters i j hij input designated sample)) := by
  rw [← referenceMass_eq_stopped parameters i j hij input event]
  exact physical_probability_lower parameters i j hij input designated event

variable (strategy : FixedPreliminaryGame.Strategy parameters input)

abbrev canonicalStrategy := PreliminaryStrategy.extend (clauses input)
  (FixedParameters.branch parameters) parameters.plan.depth
  (FixedRows.sourceLength parameters.plan hδ) (FixedRows.rows parameters.plan)
  (FixedRows.repeats parameters.plan) strategy

abbrev experiment (o : Outer parameters j input) :=
  StoppedProjectedGlobalLaw.experiment (clauses input) (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) (Nat.succ_le_of_lt j.isLt) hij designated
    (fun k _ => FixedParameters.branch_pos parameters k)
    (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1)) (flags parameters i)
    (canonicalStrategy parameters input strategy) o

abbrev OriginalFiber (o : Outer parameters j input) :=
  HierarchicalProjectedExperiment.Sample (rows := FixedRows.rows parameters.plan)
    (repeats := FixedRows.repeats parameters.plan)
    (StoppedProjectedExperiment.projectedSlots (clauses input) (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij designated o)
    (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o)
    (StoppedProjectedExperiment.lower (FixedRows.rows parameters.plan) (Nat.succ_le_of_lt j.isLt) hij o)
    (StoppedProjectedExperiment.cut (FixedRows.rows parameters.plan) (Nat.succ_le_of_lt j.isLt) hij o)

def originalLaw : FiniteDistribution (OriginalSample parameters i j hij input designated) :=
  StoppedProjectedGlobalLaw.experimentLaw (clauses input) (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) (Nat.succ_le_of_lt j.isLt) hij designated
    (fun k _ => FixedParameters.branch_pos parameters k)
    (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1)) (flags parameters i)
    (canonicalStrategy parameters input strategy)

def originalRecord (sample : OriginalSample parameters i j hij input designated) :=
  record parameters i j hij input sample.1 sample.2.1.1 sample.2.1.2.2
    ((experiment parameters i j hij input designated strategy sample.1).arrays sample.2)

def upperEvent (o : Outer parameters j input)
    (x : OriginalFiber parameters i j hij input designated o) : Bool :=
  PrefixTests.observeAtLevelNode (clauses input) (canonicalStrategy parameters input strategy)
    o.1 ((experiment parameters i j hij input designated strategy o).arrays x) j
    ⟨StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o,
      StoppedProjectedExperiment.upper_height (Nat.succ_le_of_lt j.isLt) o⟩
    (x.1.2.2 j)

theorem lowerEvent_eq_win (o : Outer parameters j input)
    (x : OriginalFiber parameters i j hij input designated o) :
    HierarchicalAdviceExperiment.lowerEvent
        (experiment parameters i j hij input designated strategy o) x =
      StoppedSharedEvents.win (clauses input) strategy (Nat.succ_le_of_lt i.isLt)
        (fun k _ => FixedParameters.branch_pos parameters k) i
        (originalRecord parameters i j hij input designated strategy ⟨o, x⟩) := by
  symm
  unfold StoppedSharedEvents.win StoppedSharedEvents.representativeLeaf originalRecord record
  dsimp only
  rw [GeometricPrefixSplit.prefixPath_join]
  exact (PrefixMatrixAcceptance.observe_endpoint (clauses input)
    (canonicalStrategy parameters input strategy) o.1
    (StoppedProjectedExperiment.stoppedPath (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij o x.1)
    (StoppedSharedEvents.referenceSuffix (Nat.succ_le_of_lt i.isLt)
      (fun k _ => FixedParameters.branch_pos parameters k))
    ((experiment parameters i j hij input designated strategy o).arrays x)
    (x.1.2.2 i)).trans
      (PrefixMatrixAcceptance.observe_eq_lower (clauses input)
        (canonicalStrategy parameters input strategy) o.1
        ((experiment parameters i j hij input designated strategy o).arrays x) i
        ⟨StoppedProjectedExperiment.lower (FixedRows.rows parameters.plan)
          (Nat.succ_le_of_lt j.isLt) hij o x.1,
          StoppedProjectedExperiment.lower_height (FixedRows.rows parameters.plan)
            (Nat.succ_le_of_lt j.isLt) hij o x.1⟩ (x.1.2.2 i)
        (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o))

theorem upperEvent_eq_win (o : Outer parameters j input)
    (x : OriginalFiber parameters i j hij input designated o) :
    upperEvent parameters i j hij input designated strategy o x =
      StoppedSharedEvents.win (clauses input) strategy (Nat.succ_le_of_lt i.isLt)
        (fun k _ => FixedParameters.branch_pos parameters k) j
        (originalRecord parameters i j hij input designated strategy ⟨o, x⟩) := by
  symm
  unfold StoppedSharedEvents.win StoppedSharedEvents.representativeLeaf originalRecord record
  dsimp only
  rw [GeometricPrefixSplit.prefixPath_join, Path.slotEmbedding_append]
  exact PrefixMatrixAcceptance.observe_endpoint (clauses input)
    (canonicalStrategy parameters input strategy) o.1
    (StoppedProjectedExperiment.upperPath (Nat.succ_le_of_lt j.isLt) o)
    ((StoppedProjectedExperiment.lowerPath (FixedRows.rows parameters.plan) hij x.1).slotEmbedding
      (StoppedSharedEvents.referenceSuffix (Nat.succ_le_of_lt i.isLt)
        (fun k _ => FixedParameters.branch_pos parameters k)))
    ((experiment parameters i j hij input designated strategy o).arrays x) (x.1.2.2 j)

theorem originalRecord_physicalRead
    (sample : PhysicalSample parameters i j hij input designated) :
    originalRecord parameters i j hij input designated strategy
        (StoppedProjectedPhysicalLaw.read (clauses input) (FixedRows.rows parameters.plan)
          (FixedRows.repeats parameters.plan) (Nat.succ_le_of_lt j.isLt) hij designated sample) =
      physicalRecord parameters i j hij input designated sample := by
  exact congrArg (record parameters i j hij input sample.1 sample.2.1.1 sample.2.1.2.2)
    (StoppedProjectedArrays.arrays_physicalExperimentRead_eq (clauses input)
      (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij designated
      (fun k _ => FixedParameters.branch_pos parameters k)
      (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1)) (flags parameters i)
      (canonicalStrategy parameters input strategy) sample.1 sample.2)

theorem joint_probability_eq_physical :
    (originalLaw parameters i j hij input designated strategy).probability
      (HierarchicalUsefulFamily.jointEvent
        (experiment parameters i j hij input designated strategy)
        (upperEvent parameters i j hij input designated strategy)) =
    (physicalLaw parameters i j hij input designated).probability (fun sample =>
      StoppedSharedEvents.pair (clauses input) strategy (Nat.succ_le_of_lt i.isLt)
        (fun k _ => FixedParameters.branch_pos parameters k) i j
        (physicalRecord parameters i j hij input designated sample)) := by
  have hevent : HierarchicalUsefulFamily.jointEvent
      (experiment parameters i j hij input designated strategy)
      (upperEvent parameters i j hij input designated strategy) =
      (fun sample => StoppedSharedEvents.pair (clauses input) strategy
        (Nat.succ_le_of_lt i.isLt) (fun k _ => FixedParameters.branch_pos parameters k) i j
        (originalRecord parameters i j hij input designated strategy sample)) := by
    funext sample
    exact congrArg₂ Bool.and
      (lowerEvent_eq_win parameters i j hij input designated strategy sample.1 sample.2)
      (upperEvent_eq_win parameters i j hij input designated strategy sample.1 sample.2)
  rw [hevent]
  have hread := StoppedProjectedPhysicalLaw.probability_read (clauses input)
    (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij designated
    (fun k _ => FixedParameters.branch_pos parameters k)
    (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1)) (flags parameters i)
    (canonicalStrategy parameters input strategy)
    (fun sample => StoppedSharedEvents.pair (clauses input) strategy
      (Nat.succ_le_of_lt i.isLt) (fun k _ => FixedParameters.branch_pos parameters k) i j
      (originalRecord parameters i j hij input designated strategy sample))
  simpa only [originalRecord_physicalRead, originalLaw, physicalLaw] using hread.symm

theorem joint_probability_ge_of_reserve
    (hreserve : InitialParameters.simultaneous δ + 2 * parameters.accuracy ≤
      (StoppedSharedSampler.stoppedLaw (clauses input)
        (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
        (Nat.succ_le_of_lt i.isLt) (fun k _ => FixedParameters.branch_pos parameters k)
        (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1))).probability
          (StoppedSharedEvents.pair (clauses input) strategy (Nat.succ_le_of_lt i.isLt)
            (fun k _ => FixedParameters.branch_pos parameters k) i j)) :
    InitialParameters.simultaneous δ ≤
      (originalLaw parameters i j hij input designated strategy).probability
        (HierarchicalUsefulFamily.jointEvent
          (experiment parameters i j hij input designated strategy)
          (upperEvent parameters i j hij input designated strategy)) := by
  rw [joint_probability_eq_physical]
  have hcompare := stopped_probability_lower parameters i j hij input designated
    (StoppedSharedEvents.pair (clauses input) strategy (Nat.succ_le_of_lt i.isLt)
      (fun k _ => FixedParameters.branch_pos parameters k) i j)
  have haccuracy := parameters.accuracy_pos
  linarith

theorem useful_probability_ge_of_reserve
    (hreserve : InitialParameters.simultaneous δ + 2 * parameters.accuracy ≤
      (StoppedSharedSampler.stoppedLaw (clauses input)
        (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
        (Nat.succ_le_of_lt i.isLt) (fun k _ => FixedParameters.branch_pos parameters k)
        (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1))).probability
          (StoppedSharedEvents.pair (clauses input) strategy (Nat.succ_le_of_lt i.isLt)
            (fun k _ => FixedParameters.branch_pos parameters k) i j)) :
    InitialParameters.simultaneous δ / 2 ≤
      (originalLaw parameters i j hij input designated strategy).probability
        (HierarchicalUsefulFamily.usefulEvent
          (experiment parameters i j hij input designated strategy) (InitialParameters.useful δ)
          (upperEvent parameters i j hij input designated strategy)) := by
  exact HierarchicalUsefulFamily.useful_probability_ge_half
    (experiment parameters i j hij input designated strategy) (outerLaw parameters j input)
    (upperEvent parameters i j hij input designated strategy) (InitialParameters.simultaneous δ)
    (InitialParameters.simultaneous_pos hδ).le
    (joint_probability_ge_of_reserve parameters i j hij input designated strategy hreserve)

end
end PerfectCompleteness.FixedStoppedUsefulMass

end

end OAI
