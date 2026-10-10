import OAI.Computability.PerfectCompleteness.Decoding.FixedStoppedDecoderContext
import OAI.Computability.PerfectCompleteness.Foundations.SourcePhysicalSourceSwapLemmas
import OAI.Computability.PerfectCompleteness.Foundations.StoppedPhysicalPrefixSwap

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedPhysicalLaw

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
attribute [local instance] linearMapFintype
attribute [local instance] StoppedProjectedPhysicalAdvice.adviceFintype
  StoppedProjectedPhysicalAdvice.physicalAdviceFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

abbrev clauses := PCPSource.clauseFamily (BinaryLanguage.totalRename input)

def designated : Fin (FixedParameters.branch parameters i.val) →
    Slots (FixedParameters.branch parameters) i.val :=
  fun _ => StoppedCleanGeometry.firstLeaf (FixedParameters.branch_pos parameters) i.val

def flag : Fin (FixedParameters.branch parameters i.val) → FiniteDistribution Bool :=
  fun _ => ProjectedCleanRate.projectionFlag (parameters.cubeSize i.val)
    (FixedDecoderCleanRate.cubePositive parameters i.val)

abbrev Prefixes := FixedStoppedDecoderContext.Prefixes parameters i j
abbrev Context := FixedStoppedDecoderContext.Context parameters i j hij input

def path (pref : Prefixes parameters i j) :=
  (FixedStoppedDecoderContext.upperPath parameters i j pref).append
    (FixedStoppedDecoderContext.lowerPath parameters i j hij pref)

abbrev ChildSample (pref : Prefixes parameters i j) :=
  SourceChildKernel.Sample
    (C := WholeCutCalls.Index (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
      (path parameters i j hij pref))
    (t := FixedRows.sourceLength parameters.plan hδ)
    (FixedRows.rows parameters.plan) (clauses input) (designated parameters i)

abbrev Sample := (context : Context parameters i j hij input) ×
  ChildSample parameters i j hij input context.1

abbrev PhysicalSample := StoppedProjectedPhysicalAdvice.Sample
  (t := FixedRows.sourceLength parameters.plan hδ)
  (clauses input) (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
  (Nat.succ_le_of_lt j.isLt) hij (designated parameters i) parameters.plan.order

def childLaw (pref : Prefixes parameters i j) :
    FiniteDistribution (ChildSample parameters i j hij input pref) :=
  SourceChildKernel.originalLaw
    (C := WholeCutCalls.Index (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
      (path parameters i j hij pref))
    (t := FixedRows.sourceLength parameters.plan hδ)
    (FixedRows.rows parameters.plan) (clauses input) (designated parameters i) (flag parameters i)

def law : FiniteDistribution (Sample parameters i j hij input) :=
  CompletionSoundness.sigmaLaw (FixedStoppedDecoderContext.law parameters i j hij input)
    (fun context => childLaw parameters i j hij input context.1)

def read (sample : Sample parameters i j hij input) :
    PhysicalSample parameters i j hij input :=
  let context := sample.1
  let inside := SourceQuestionRawSwap.insideQuestions (FixedRows.rows parameters.plan)
    (clauses input) (designated parameters i) sample.2
  let questions := SourceQuestionCutSplit.join (path parameters i j hij context.1)
    inside context.2.1
  let positions := SourceQuestionRawSwap.positions (FixedRows.rows parameters.plan)
    (clauses input) (designated parameters i) sample.2
  let exterior := SourcePhysicalSourceSwap.joinedExterior (clauses input)
    (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (path parameters i j hij context.1) inside context.2.1 context.2.2.2.2
  let raw := SourceQuestionRawSwap.raw (FixedRows.rows parameters.plan)
    (clauses input) (designated parameters i) sample.2
  ⟨(questions, context.1.1),
    (⟨(context.1.2, (positions, context.2.2.2.1)), (exterior, raw)⟩, context.2.2.1)⟩

abbrev physicalLaw := StoppedProjectedPhysicalAdvice.law
  (t := FixedRows.sourceLength parameters.plan hδ)
  (clauses input) (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
  (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
  (fun k _ => FixedParameters.branch_pos parameters k)
  (fun k => parameters.plan.rows_pos (parameters.plan.depth - (k + 1)))
  (flag parameters i) parameters.plan.order

theorem expectation_read (value : PhysicalSample parameters i j hij input → ℝ) :
    (physicalLaw parameters i j hij input).expectation value =
      (law parameters i j hij input).expectation
        (fun sample => value (read parameters i j hij input sample)) := by
  refine (StoppedPhysicalPrefixSwap.expectation_prefixes
    (t := FixedRows.sourceLength parameters.plan hδ)
    (clauses input) (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
    (fun k _ => FixedParameters.branch_pos parameters k)
    (fun k => parameters.plan.rows_pos (parameters.plan.depth - (k + 1)))
    (flag parameters i) parameters.plan.order value).trans ?_
  simp only [law, FixedStoppedDecoderContext.law, CandidateCoupling.expectation_sigmaLaw,
    FixedStoppedDecoderContext.fiberLaw]
  apply FiniteDistribution.expectation_congr
  intro pref
  simp only [FiniteDistribution.expectation_product]
  let questionLaw := PreliminarySampler.questionsLaw
    (branch := FixedParameters.branch parameters) (n := parameters.plan.depth)
    (t := FixedRows.sourceLength parameters.plan hδ)
    (m := (PCPSource.normalizedFormula (BinaryLanguage.totalRename input)).clauses.length)
  let adviceLaw := FiniteDistribution.uniform (FixedStoppedDecoderContext.Advice parameters i j pref)
  let directionsLaw := FixedStoppedDecoderContext.directionLaw parameters
  let outsideLaw := FiniteDistribution.uniform
    (FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref)
  let statistic := fun
      (questions : PreliminarySampler.Questions (FixedParameters.branch parameters)
        parameters.plan.depth (FixedRows.sourceLength parameters.plan hδ)
        (PCPSource.normalizedFormula (BinaryLanguage.totalRename input)).clauses.length)
      (A : FixedStoppedDecoderContext.Advice parameters i j pref)
      (directions : FixedStoppedDecoderContext.Directions parameters) =>
    (SourceProjectedTag.positionLaw (branch := FixedParameters.branch parameters)
      (n := i.val) (t := FixedRows.sourceLength parameters.plan hδ)).expectation
        (fun positions => (StoppedProjectedExperiment.physicalFiberLaw
          (clauses input) (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
          (Nat.succ_le_of_lt j.isLt) hij (designated parameters i) (flag parameters i)
          (questions, pref.1) (pref.2, (positions, directions))).expectation
            (fun raw => value ⟨(questions, pref.1), (⟨(pref.2, (positions, directions)), raw⟩, A)⟩))
  let rebuilt := fun (external : FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref)
      (A : FixedStoppedDecoderContext.Advice parameters i j pref)
      (directions : FixedStoppedDecoderContext.Directions parameters) =>
    (FiniteDistribution.uniform
      (FixedStoppedDecoderContext.Exterior parameters i j hij input pref external)).expectation
        (fun exterior => (childLaw parameters i j hij input pref).expectation
          (fun sample => value (read parameters i j hij input
            ⟨⟨pref, external, A, directions, exterior⟩, sample⟩)))
  change questionLaw.expectation (fun questions => adviceLaw.expectation (fun A =>
      directionsLaw.expectation (fun directions => statistic questions A directions))) =
    outsideLaw.expectation (fun external => adviceLaw.expectation (fun A =>
      directionsLaw.expectation (fun directions => rebuilt external A directions)))
  calc
    _ = adviceLaw.expectation (fun A => directionsLaw.expectation (fun directions =>
        questionLaw.expectation (fun questions => statistic questions A directions))) := by
      rw [FiniteDistribution.expectation_comm]
      apply FiniteDistribution.expectation_congr
      intro A
      exact FiniteDistribution.expectation_comm _ _ _
    _ = adviceLaw.expectation (fun A => directionsLaw.expectation (fun directions =>
        outsideLaw.expectation (fun external => rebuilt external A directions))) := by
      apply FiniteDistribution.expectation_congr
      intro A
      apply FiniteDistribution.expectation_congr
      intro directions
      exact SourcePhysicalSourceSwap.expectation_swap (clauses input)
        (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
        (path parameters i j hij pref) (designated parameters i) (flag parameters i)
        (fun questions positions exterior raw =>
          value ⟨(questions, pref.1), (⟨(pref.2, (positions, directions)), (exterior, raw)⟩, A)⟩)
    _ = _ := by
      calc
        _ = adviceLaw.expectation (fun A => outsideLaw.expectation (fun external =>
            directionsLaw.expectation (fun directions => rebuilt external A directions))) := by
          apply FiniteDistribution.expectation_congr
          intro A
          exact FiniteDistribution.expectation_comm _ _ _
        _ = _ := FiniteDistribution.expectation_comm _ _ _

theorem read_law :
    (law parameters i j hij input).pushforward (read parameters i j hij input) =
      physicalLaw parameters i j hij input := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward,
    CandidateCoupling.probability_eq_expectation, CandidateCoupling.probability_eq_expectation]
  exact (expectation_read parameters i j hij input (fun sample => if event sample then 1 else 0)).symm

end
end PerfectCompleteness.FixedStoppedPhysicalLaw

end

section

namespace PerfectCompleteness.FixedStoppedNativeLaw

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] StoppedProjectedPhysicalAdvice.adviceFintype
  StoppedProjectedPhysicalAdvice.physicalAdviceFintype

section PathTransport

variable {branch : Nat → Nat} {root h t v m : Nat}
  (rows repeats : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)
  {p q : Path branch root (h + 1)}

def sourceSampleEquiv (hp : p = q) :
    SourceChildKernel.Sample (C := WholeCutCalls.Index rows repeats p) (t := t)
      rows clauses designated ≃
    SourceChildKernel.Sample (C := WholeCutCalls.Index rows repeats q) (t := t)
      rows clauses designated :=
  Equiv.cast (congrArg (fun path : Path branch root (h + 1) =>
    SourceChildKernel.Sample (C := WholeCutCalls.Index rows repeats path) (t := t)
      rows clauses designated) hp)

theorem sourceSampleEquiv_law [NeZero m] (hp : p = q)
    (flag : Fin (branch h) → FiniteDistribution Bool) :
    (SourceChildKernel.originalLaw (C := WholeCutCalls.Index rows repeats p) (t := t)
      rows clauses designated flag).pushforward
        (sourceSampleEquiv rows repeats clauses designated hp) =
      SourceChildKernel.originalLaw (C := WholeCutCalls.Index rows repeats q) (t := t)
        rows clauses designated flag := by
  cases hp
  exact FiniteDistribution.pushforward_id _

end PathTransport

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

local instance contextAdviceFintype
    (pref : FixedStoppedDecoderContext.Prefixes parameters i j) :
    Fintype (FixedStoppedDecoderContext.Advice parameters i j pref) :=
  UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

abbrev Context := FixedStoppedDecoderContext.Context parameters i j hij input

abbrev setup (context : Context parameters i j hij input) :=
  FixedDecoderCleanRate.setup parameters
    (FixedStoppedDecoderContext.geometry parameters i j hij input context) input

abbrev Sample := (context : Context parameters i j hij input) ×
  CleanDecoderRate.Sample (setup parameters i j hij input context)

theorem path_eq (context : Context parameters i j hij input) :
    CleanDecoderRate.path (setup parameters i j hij input context) =
      FixedStoppedPhysicalLaw.path parameters i j hij context.1 :=
  StoppedCleanGeometry.geometry_path parameters input
    (FixedStoppedDecoderContext.upperPath parameters i j context.1)
    (FixedStoppedDecoderContext.lowerPath parameters i j hij context.1) hij
    context.2.1 context.2.2.2.2

def childRead (context : Context parameters i j hij input) :
    CleanDecoderRate.Sample (setup parameters i j hij input context) ≃
      FixedStoppedPhysicalLaw.ChildSample parameters i j hij input context.1 :=
  sourceSampleEquiv (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (FixedStoppedPhysicalLaw.clauses input) (FixedStoppedPhysicalLaw.designated parameters i)
    (path_eq parameters i j hij input context)

theorem childRead_law (context : Context parameters i j hij input) :
    (CleanDecoderRate.rawLaw (setup parameters i j hij input context)
      (parameters.cubeSize i.val) (FixedDecoderCleanRate.cubePositive parameters i.val)).pushforward
        (childRead parameters i j hij input context) =
      FixedStoppedPhysicalLaw.childLaw parameters i j hij input context.1 :=
  sourceSampleEquiv_law (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (FixedStoppedPhysicalLaw.clauses input) (FixedStoppedPhysicalLaw.designated parameters i)
    (path_eq parameters i j hij input context) (FixedStoppedPhysicalLaw.flag parameters i)

def law : FiniteDistribution (Sample parameters i j hij input) :=
  CompletionSoundness.sigmaLaw (FixedStoppedDecoderContext.law parameters i j hij input)
    (fun context => CleanDecoderRate.rawLaw (setup parameters i j hij input context)
      (parameters.cubeSize i.val) (FixedDecoderCleanRate.cubePositive parameters i.val))

def sourceRead (sample : Sample parameters i j hij input) :
    FixedStoppedPhysicalLaw.Sample parameters i j hij input :=
  ⟨sample.1, childRead parameters i j hij input sample.1 sample.2⟩

theorem sourceRead_law :
    (law parameters i j hij input).pushforward (sourceRead parameters i j hij input) =
      FixedStoppedPhysicalLaw.law parameters i j hij input := by
  have hsplit := SigmaObservation.pushforward_fiber
    (X := fun context : Context parameters i j hij input =>
      CleanDecoderRate.Sample (setup parameters i j hij input context))
    (Y := fun context : Context parameters i j hij input =>
      FixedStoppedPhysicalLaw.ChildSample parameters i j hij input context.1)
    (FixedStoppedDecoderContext.law parameters i j hij input)
    (fun context => CleanDecoderRate.rawLaw (setup parameters i j hij input context)
      (parameters.cubeSize i.val) (FixedDecoderCleanRate.cubePositive parameters i.val))
    (fun context => childRead parameters i j hij input context)
  exact hsplit.trans (congrArg
    (fun P : (context : Context parameters i j hij input) →
        FiniteDistribution (FixedStoppedPhysicalLaw.ChildSample parameters i j hij input
          context.1) =>
      CompletionSoundness.sigmaLaw (FixedStoppedDecoderContext.law parameters i j hij input) P)
    (funext (fun context => childRead_law parameters i j hij input context)))

def read (sample : Sample parameters i j hij input) :
    FixedStoppedPhysicalLaw.PhysicalSample parameters i j hij input :=
  FixedStoppedPhysicalLaw.read parameters i j hij input
    (sourceRead parameters i j hij input sample)

theorem read_law :
    (law parameters i j hij input).pushforward (read parameters i j hij input) =
      FixedStoppedPhysicalLaw.physicalLaw parameters i j hij input := by
  change (law parameters i j hij input).pushforward
    (fun sample => FixedStoppedPhysicalLaw.read parameters i j hij input
      (sourceRead parameters i j hij input sample)) = _
  rw [← FiniteDistribution.pushforward_comp, sourceRead_law]
  exact FixedStoppedPhysicalLaw.read_law parameters i j hij input

theorem expectation_read
    (value : FixedStoppedPhysicalLaw.PhysicalSample parameters i j hij input → ℝ) :
    (law parameters i j hij input).expectation
        (fun sample => value (read parameters i j hij input sample)) =
      (FixedStoppedPhysicalLaw.physicalLaw parameters i j hij input).expectation value := by
  rw [← read_law parameters i j hij input, FiniteDistribution.expectation_pushforward]

end
end PerfectCompleteness.FixedStoppedNativeLaw

end

end OAI
