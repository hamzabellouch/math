import OAI.Computability.PerfectCompleteness.Decoding.FixedStoppedDecoderLaw
import OAI.Computability.PerfectCompleteness.Decoding.FixedStoppedNativeProjection
import OAI.Computability.PerfectCompleteness.Foundations.ProjectedMeetingTransport
import OAI.Computability.PerfectCompleteness.Machines.FixedStoppedNativeTape
import OAI.Computability.PerfectCompleteness.Repetition.CleanPhysicalProjectedMeeting
import OAI.Computability.PerfectCompleteness.Repetition.StoppedCleanCutEquality
import OAI.Computability.PerfectCompleteness.Sampling.FixedStoppedPhysicalLawLemmas
import OAI.Computability.PerfectCompleteness.Sampling.StoppedProjectedMeetingLaw

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedMeetingEquality

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
attribute [local instance] linearMapFintype
attribute [local instance] RightDecoder.scalarFintype

local instance physicalLeftFintype {branch : Nat → Nat} {n t : Nat}
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n) :
    Fintype (Module.Dual (ZMod 2) (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)

private theorem expectation_congr_on_support {X : Type*} [Fintype X]
    (μ : FiniteDistribution X) (f g : X → ℝ)
    (h : ∀ x, μ.weight x ≠ 0 → f x = g x) :
    μ.expectation f = μ.expectation g := by
  unfold FiniteDistribution.expectation
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : μ.weight x = 0
  · simp only [hx, zero_mul]
  · rw [h x hx]

private theorem nodeDirection_val_heq {branch rows : Nat → Nat} {n : Nat}
    (level : Fin n) (node other : PrefixTests.LevelNode branch level)
    (hn : node = other) (direction : PrefixTests.LevelDirection rows level) :
    HEq (PrefixTests.nodeDirection rows level node direction).val
      (PrefixTests.nodeDirection rows level other direction).val := by
  cases hn
  rfl

private theorem familyMeetingProbability_eq_of_useful
    {δ : ℚ} (plan : FixedRows.Plan δ) {branch : Nat → Nat} {t : Nat}
    {Sample : OriginalDecoderMark.SlotFamily branch plan.depth t → Type*}
    [∀ slots, Fintype (Sample slots)]
    (F : OriginalDecoderMark.Family branch (FixedRows.rows plan) plan.depth t Sample)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))
    (slots projected : Slots branch plan.depth → Fin t → MixedSupport.Slot)
    (projection : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (upper lower : Nodes branch plan.depth) (lowerLevel : Nat)
    {Ω : Type*} [Fintype Ω] (original : FiniteDistribution Ω)
    (arrays : Ω → Arrays slots (FixedRows.rows plan)) (lowerEvent : Ω → Bool)
    (A : ManyGoodRows.RowMap (Block (FixedRows.rows plan) upper) plan.order)
    (a : Block (FixedRows.rows plan) lower) (cut : OwnInputReference.Cut upper lower)
    (threshold : ℝ)
    (visible : HierarchicalProjectedRawPrediction.Visible projected (FixedRows.rows plan)
      upper lower A (FixedRows.repeats plan) cut)
    (huseful : ∀ background : HierarchicalMatrixTable.Background
        (rows := FixedRows.rows plan) slots upper,
      HierarchicalProjectedMeeting.useful slots upper lowerLevel background
          (F.original slots) (F.arrays slots) (F.lowerEvent slots) (InitialParameters.useful δ) =
        HierarchicalProjectedMeeting.useful slots upper lowerLevel background
          original arrays lowerEvent (InitialParameters.useful δ))
    (hthreshold : threshold = UpperParameterScalars.tau (InitialParameters.useful δ)
      plan.density plan.order (FixedRows.rows plan (Nodes.height upper))) :
    ProjectedMeetingTransport.familyMeetingProbability plan F σ slots projected projection
        upper lower lowerLevel A a cut threshold visible =
      HierarchicalProjectedRawMeeting.meetingProbability plan slots projected projection
        upper lower lowerLevel original arrays lowerEvent σ A a cut visible := by
  unfold ProjectedMeetingTransport.familyMeetingProbability
    HierarchicalProjectedRawMeeting.meetingProbability HierarchicalProjectedMeeting.leftLaw
  rw [huseful, hthreshold]

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

theorem flag_eq :
    FixedStoppedDecoderLaw.flag parameters i = FixedStoppedPhysicalLaw.flag parameters i := by
  funext child
  apply FiniteDistribution.eq_of_weight_eq
  intro b
  cases b <;> simp [FixedStoppedDecoderLaw.flag, FixedStoppedPhysicalLaw.flag,
    ProjectionPosterior.bernoulli, ProjectedCleanRate.projectionFlag,
    RepetitionRate.bernoulli, ProjectedCleanRate.projectionDensity,
    FixedParameters.projectionProbability]

variable (strategy : FixedPreliminaryGame.Strategy parameters input)

private abbrev OriginalRaw := StoppedProjectedMeetingLaw.RawSample
  (t := FixedRows.sourceLength parameters.plan hδ) parameters.plan
  (FixedStoppedPhysicalLaw.clauses input) (Nat.succ_le_of_lt j.isLt) hij
  (FixedStoppedPhysicalLaw.designated parameters i)

private def familyMeetingOnRaw (sample : OriginalRaw parameters i j hij input) : ℝ :=
  ProjectedMeetingTransport.familyMeetingProbability parameters.plan
    (FixedStoppedDecoderLaw.markFamily parameters i j hij input strategy
      (sample.1.2, sample.2.2.1.1))
    (FixedStoppedDecoderLaw.labeling parameters input strategy)
    (StoppedProjectedExperiment.nativeSlots (FixedStoppedPhysicalLaw.clauses input) sample.1)
    (StoppedProjectedExperiment.projectedSlots (FixedStoppedPhysicalLaw.clauses input)
      (FixedRows.rows parameters.plan) (Nat.succ_le_of_lt j.isLt) hij
      (FixedStoppedPhysicalLaw.designated parameters i) sample.1 sample.2.2.1)
    (StoppedProjectedExperiment.projection (FixedStoppedPhysicalLaw.clauses input)
      (FixedRows.rows parameters.plan) (Nat.succ_le_of_lt j.isLt) hij
      (FixedStoppedPhysicalLaw.designated parameters i) sample.1 sample.2.2.1)
    (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) sample.1)
    (StoppedProjectedExperiment.lower (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij sample.1 sample.2.2.1) (i.val + 1)
    sample.2.1
    (StoppedProjectedExperiment.direction (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij sample.1 sample.2.2.1)
    (StoppedProjectedExperiment.cut (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij sample.1 sample.2.2.1)
    (FixedStoppedDecoderLaw.threshold parameters j) sample.2.2.2.2

private theorem familyMeetingOnRaw_eq
    (sample : OriginalRaw parameters i j hij input) :
    familyMeetingOnRaw parameters i j hij input strategy sample =
      StoppedProjectedMeetingLaw.rawMeetingProbability parameters.plan
        (branch := FixedParameters.branch parameters)
        (t := FixedRows.sourceLength parameters.plan hδ)
        (FixedStoppedPhysicalLaw.clauses input) (Nat.succ_le_of_lt j.isLt) hij
        (FixedStoppedPhysicalLaw.designated parameters i)
        (fun k _ => FixedParameters.branch_pos parameters k)
        (FixedStoppedDecoderLaw.flag parameters i)
        (FixedStoppedDecoderLaw.labeling parameters input strategy) sample := by
  let F := FixedStoppedDecoderLaw.markFamily parameters i j hij input strategy
    (sample.1.2, sample.2.2.1.1)
  let S := StoppedProjectedExperiment.experiment
    (FixedStoppedPhysicalLaw.clauses input) (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) (Nat.succ_le_of_lt j.isLt) hij
    (FixedStoppedPhysicalLaw.designated parameters i)
    (fun k _ => FixedParameters.branch_pos parameters k)
    (StoppedProjectedMeetingLaw.rows_positive parameters.plan)
    (FixedStoppedDecoderLaw.flag parameters i)
    (FixedStoppedDecoderLaw.labeling parameters input strategy) sample.1
  have hmark (background : HierarchicalMatrixTable.Background
      (rows := FixedRows.rows parameters.plan) S.slots S.upper) :
      HierarchicalProjectedMeeting.useful S.slots S.upper (i.val + 1) background
        (F.original S.slots) (F.arrays S.slots) (F.lowerEvent S.slots)
        (InitialParameters.useful δ) =
      HierarchicalProjectedMeeting.useful S.slots S.upper (i.val + 1) background
        S.original S.arrays (HierarchicalAdviceExperiment.lowerEvent S)
        (InitialParameters.useful δ) := by
    funext X
    exact propext (SlotProjectedExperiment.mark_source
      (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij sample.1.2
      (fun k _ => FixedParameters.branch_pos parameters k)
      (StoppedProjectedMeetingLaw.rows_positive parameters.plan)
      (FixedStoppedDecoderLaw.flag parameters i)
      (FixedStoppedDecoderLaw.labeling parameters input strategy)
      (FixedStoppedPhysicalLaw.clauses input) (FixedStoppedPhysicalLaw.designated parameters i)
      sample.1.1 (InitialParameters.useful δ) background X)
  have hthreshold : FixedStoppedDecoderLaw.threshold parameters j =
      UpperParameterScalars.tau (InitialParameters.useful δ) parameters.plan.density
        parameters.plan.order (FixedRows.rows parameters.plan (Nodes.height S.upper)) := by
    simp only [FixedStoppedDecoderLaw.threshold, S,
      HierarchicalProjectedExperiment.experiment, StoppedProjectedExperiment.upper_height]
  exact familyMeetingProbability_eq_of_useful parameters.plan F
    (FixedStoppedDecoderLaw.labeling parameters input strategy) S.slots
    (StoppedProjectedExperiment.projectedSlots (FixedStoppedPhysicalLaw.clauses input)
      (FixedRows.rows parameters.plan) (Nat.succ_le_of_lt j.isLt) hij
      (FixedStoppedPhysicalLaw.designated parameters i) sample.1 sample.2.2.1)
    (StoppedProjectedExperiment.projection (FixedStoppedPhysicalLaw.clauses input)
      (FixedRows.rows parameters.plan) (Nat.succ_le_of_lt j.isLt) hij
      (FixedStoppedPhysicalLaw.designated parameters i) sample.1 sample.2.2.1)
    S.upper
    (StoppedProjectedExperiment.lower (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij sample.1 sample.2.2.1) (i.val + 1)
    S.original S.arrays (HierarchicalAdviceExperiment.lowerEvent S) sample.2.1
    (StoppedProjectedExperiment.direction (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij sample.1 sample.2.2.1)
    (StoppedProjectedExperiment.cut (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij sample.1 sample.2.2.1)
    (FixedStoppedDecoderLaw.threshold parameters j) sample.2.2.2.2 hmark hthreshold

def nativeMeetingProbability
    (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) : ℝ :=
  (CleanDecoderPairLaw.pairKernel
    (FixedStoppedDecoderLaw.setups parameters i j hij input sample.1)
    (FixedStoppedDecoderLaw.labeling parameters input strategy)
    (FixedStoppedDecoderLaw.useful parameters i j hij input strategy sample.1)
    parameters.plan.order parameters.plan.density
    (FixedStoppedDecoderContext.advice parameters i j hij input sample.1)
    (LinearMap.ker (FixedStoppedDecoderContext.advice parameters i j hij input sample.1))
    (FixedStoppedDecoderContext.direction parameters i j hij input sample.1)
    (FixedStoppedDecoderLaw.threshold parameters j) sample.2).probability
      (DecoderRankSplit.meeting
        (FixedStoppedDecoderLaw.setups parameters i j hij input sample.1) sample.2)

def physicalMeetingProbability
    (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) : ℝ :=
  StoppedProjectedMeetingLaw.meetingProbability parameters.plan
    (FixedStoppedPhysicalLaw.clauses input) (Nat.succ_le_of_lt j.isLt) hij
    (FixedStoppedPhysicalLaw.designated parameters i)
    (fun k _ => FixedParameters.branch_pos parameters k)
    (FixedStoppedDecoderLaw.flag parameters i)
    (FixedStoppedDecoderLaw.labeling parameters input strategy)
    (FixedStoppedNativeLaw.read parameters i j hij input sample)

def cleanMeetingProbability
    (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) : ℝ :=
  (CleanPhysicalProjectedMeeting.visiblePairKernel
    (FixedStoppedNativeLaw.setup parameters i j hij input sample.1)
    (FixedStoppedDecoderLaw.markFamily parameters i j hij input strategy sample.1.1)
    (InitialParameters.useful δ)
    (FixedStoppedDecoderLaw.labeling parameters input strategy)
    parameters.plan.order parameters.plan.density
    (FixedStoppedDecoderContext.advice parameters i j hij input sample.1)
    (FixedStoppedDecoderContext.direction parameters i j hij input sample.1)
    (FixedStoppedDecoderLaw.threshold parameters j) sample.2).probability
      (fun answer => decide ((ProjectedNodeEmbedding.intoOriginal
        (CleanPhysicalDecoderLaw.physicalProjection
          (FixedStoppedNativeLaw.setup parameters i j hij input sample.1) sample.2)
        (FixedStoppedDecoderContext.upperNode parameters i j hij input sample.1)).dualMap
          answer.1 = answer.2))

private theorem direction_heq
    (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :
    HEq (FixedStoppedDecoderContext.direction parameters i j hij input sample.1)
      (StoppedProjectedExperiment.direction (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij
        (FixedStoppedNativeProjection.physicalSample parameters i j hij input sample).1
        (FixedStoppedNativeProjection.innerTag parameters i j hij input sample)) := by
  let physical := FixedStoppedNativeProjection.physicalSample parameters i j hij input sample
  let tag := FixedStoppedNativeProjection.innerTag parameters i j hij input sample
  have hlower := (StoppedCleanCutEquality.stopped_lower_eq (FixedRows.rows parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij physical.1 tag).symm
  have hnodes :
      (⟨CleanPhysicalDecoderLaw.lower
        (FixedStoppedNativeLaw.setup parameters i j hij input sample.1),
        CleanDecoderContext.lowerHeight
          (FixedStoppedDecoderContext.upperNode parameters i j hij input sample.1)
          (FixedStoppedDecoderContext.lowerIndex parameters i j hij input sample.1)⟩ :
        PrefixTests.LevelNode (FixedParameters.branch parameters) i) =
      ⟨StoppedProjectedExperiment.lower (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij physical.1 tag,
        StoppedProjectedExperiment.lower_height (FixedRows.rows parameters.plan)
          (Nat.succ_le_of_lt j.isLt) hij physical.1 tag⟩ :=
    Subtype.ext hlower
  exact nodeDirection_val_heq (rows := FixedRows.rows parameters.plan) i _ _ hnodes
    (sample.1.2.2.2.1 i)

private theorem cleanMeetingProbability_eq_familyOnRaw
    (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :
    cleanMeetingProbability parameters i j hij input strategy sample =
      familyMeetingOnRaw parameters i j hij input strategy
        (StoppedProjectedPhysicalAdvice.read
          (FixedStoppedPhysicalLaw.clauses input) (FixedRows.rows parameters.plan)
          (FixedRows.repeats parameters.plan) (Nat.succ_le_of_lt j.isLt) hij
          (FixedStoppedPhysicalLaw.designated parameters i) parameters.plan.order
          (FixedStoppedNativeLaw.read parameters i j hij input sample)) := by
  let S := FixedStoppedNativeLaw.setup parameters i j hij input sample.1
  let physical := FixedStoppedNativeProjection.physicalSample parameters i j hij input sample
  let tag := FixedStoppedNativeProjection.innerTag parameters i j hij input sample
  let record := StoppedProjectedPhysicalAdvice.read
    (FixedStoppedPhysicalLaw.clauses input) (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) (Nat.succ_le_of_lt j.isLt) hij
    (FixedStoppedPhysicalLaw.designated parameters i) parameters.plan.order physical
  exact ProjectedMeetingTransport.familyMeetingProbability_congr parameters.plan
    (FixedStoppedDecoderLaw.markFamily parameters i j hij input strategy sample.1.1)
    (FixedStoppedDecoderLaw.labeling parameters input strategy)
    (CleanNativeReplay.leftSlots S sample.2) (CleanNativeReplay.rightSlots S sample.2)
    (CleanPhysicalDecoderLaw.physicalProjection S sample.2)
    (FixedStoppedDecoderContext.upperNode parameters i j hij input sample.1)
    (CleanPhysicalDecoderLaw.lower S) (i.val + 1)
    (FixedStoppedDecoderContext.advice parameters i j hij input sample.1)
    (FixedStoppedDecoderContext.direction parameters i j hij input sample.1) S.cut
    (FixedStoppedDecoderLaw.threshold parameters j)
    (CleanPhysicalProjectedMeeting.visible S
      (LinearMap.ker (FixedStoppedDecoderContext.advice parameters i j hij input sample.1)) sample.2)
    (StoppedProjectedExperiment.nativeSlots (FixedStoppedPhysicalLaw.clauses input) physical.1)
    (StoppedProjectedExperiment.projectedSlots (FixedStoppedPhysicalLaw.clauses input)
      (FixedRows.rows parameters.plan) (Nat.succ_le_of_lt j.isLt) hij
      (FixedStoppedPhysicalLaw.designated parameters i) physical.1 tag)
    (StoppedProjectedExperiment.lower (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij physical.1 tag)
    (StoppedProjectedExperiment.projection (FixedStoppedPhysicalLaw.clauses input)
      (FixedRows.rows parameters.plan) (Nat.succ_le_of_lt j.isLt) hij
      (FixedStoppedPhysicalLaw.designated parameters i) physical.1 tag)
    (StoppedProjectedExperiment.direction (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij physical.1 tag)
    (StoppedProjectedExperiment.cut (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij physical.1 tag) record.2.2.2.2
    (FixedStoppedNativeProjection.leftSlots_eq parameters i j hij input sample)
    (FixedStoppedNativeProjection.rightSlots_eq parameters i j hij input sample)
    (StoppedCleanCutEquality.stopped_lower_eq (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij physical.1 tag).symm
    (FixedStoppedNativeProjection.projection_heq parameters i j hij input sample)
    (direction_heq parameters i j hij input sample)
    (StoppedCleanCutEquality.stopped_cut_heq (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij physical.1 tag).symm
    (FixedStoppedNativeTape.visible_heq parameters i j hij input sample).symm

private theorem cleanMeetingProbability_eq_physical
    (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :
    cleanMeetingProbability parameters i j hij input strategy sample =
      physicalMeetingProbability parameters i j hij input strategy sample :=
  (cleanMeetingProbability_eq_familyOnRaw parameters i j hij input strategy sample).trans
    (familyMeetingOnRaw_eq parameters i j hij input strategy _)

theorem cleanMeetingProbability_eq_native
    (context : FixedStoppedNativeLaw.Context parameters i j hij input)
    (x : CleanDecoderRate.Sample (FixedStoppedNativeLaw.setup parameters i j hij input context))
    (hx : (CleanDecoderRate.rawLaw (FixedStoppedNativeLaw.setup parameters i j hij input context)
      (parameters.cubeSize i.val) (FixedDecoderCleanRate.cubePositive parameters i.val)).weight x ≠ 0) :
    cleanMeetingProbability parameters i j hij input strategy ⟨context, x⟩ =
      nativeMeetingProbability parameters i j hij input strategy ⟨context, x⟩ :=
  CleanPhysicalProjectedMeeting.meeting_probability_eq
    (FixedStoppedNativeLaw.setup parameters i j hij input context)
    (FixedStoppedDecoderLaw.markFamily parameters i j hij input strategy context.1)
    (InitialParameters.useful δ)
    (FixedStoppedDecoderLaw.labeling parameters input strategy)
    parameters.plan.order parameters.plan.density
    (FixedStoppedDecoderContext.advice parameters i j hij input context)
    (FixedStoppedDecoderContext.direction parameters i j hij input context)
    (FixedStoppedDecoderLaw.threshold parameters j)
    (parameters.cubeSize i.val) (FixedDecoderCleanRate.cubePositive parameters i.val) x hx

abbrev expectedMeeting : ℝ :=
  StoppedProjectedMeetingLaw.expectedMeeting parameters.plan
    (FixedStoppedPhysicalLaw.clauses input) (Nat.succ_le_of_lt j.isLt) hij
    (FixedStoppedPhysicalLaw.designated parameters i)
    (fun k _ => FixedParameters.branch_pos parameters k)
    (FixedStoppedDecoderLaw.flag parameters i)
    (FixedStoppedDecoderLaw.labeling parameters input strategy)

theorem native_probability_eq_expectation :
    (FixedStoppedDecoderLaw.law parameters i j hij input strategy).probability
        (FixedStoppedDecoderLaw.meeting parameters i j hij input) =
      (FixedStoppedNativeLaw.law parameters i j hij input).expectation
        (nativeMeetingProbability parameters i j hij input strategy) := by
  simp only [FixedStoppedDecoderLaw.law, DecoderFamilyLaw.law,
    DecoderFamilyLaw.fiberLaw, CleanDecoderPairLaw.pairLaw,
    CompletionSoundness.sigmaLaw_probability, FixedStoppedNativeLaw.law,
    CandidateCoupling.expectation_sigmaLaw, nativeMeetingProbability,
    FixedStoppedDecoderLaw.meeting, DecoderFamilyLaw.meeting]
  rfl

theorem native_expectation_eq_cleanMeeting :
    (FixedStoppedNativeLaw.law parameters i j hij input).expectation
        (nativeMeetingProbability parameters i j hij input strategy) =
      (FixedStoppedNativeLaw.law parameters i j hij input).expectation
        (cleanMeetingProbability parameters i j hij input strategy) := by
  simp only [FixedStoppedNativeLaw.law, CandidateCoupling.expectation_sigmaLaw]
  apply FiniteDistribution.expectation_congr
  intro context
  apply expectation_congr_on_support
  intro x hx
  exact (cleanMeetingProbability_eq_native parameters i j hij input strategy context x hx).symm

theorem physical_expectation_eq_expectedMeeting :
    (FixedStoppedNativeLaw.law parameters i j hij input).expectation
        (physicalMeetingProbability parameters i j hij input strategy) =
      expectedMeeting parameters i j hij input strategy := by
  unfold physicalMeetingProbability
  rw [FixedStoppedNativeLaw.expectation_read]
  unfold expectedMeeting
  rw [flag_eq parameters i]
  exact StoppedProjectedMeetingLaw.expectation_meetingProbability parameters.plan
    (FixedStoppedPhysicalLaw.clauses input) (Nat.succ_le_of_lt j.isLt) hij
    (FixedStoppedPhysicalLaw.designated parameters i)
    (fun k _ => FixedParameters.branch_pos parameters k)
    (FixedStoppedPhysicalLaw.flag parameters i)
    (FixedStoppedDecoderLaw.labeling parameters input strategy)

theorem meeting_probability_eq_expectedMeeting :
    (FixedStoppedDecoderLaw.law parameters i j hij input strategy).probability
        (FixedStoppedDecoderLaw.meeting parameters i j hij input) =
      expectedMeeting parameters i j hij input strategy := by
  rw [native_probability_eq_expectation, native_expectation_eq_cleanMeeting]
  calc
    _ = (FixedStoppedNativeLaw.law parameters i j hij input).expectation
        (physicalMeetingProbability parameters i j hij input strategy) :=
      FiniteDistribution.expectation_congr _
        (cleanMeetingProbability_eq_physical parameters i j hij input strategy)
    _ = _ := physical_expectation_eq_expectedMeeting parameters i j hij input strategy

end
end PerfectCompleteness.FixedStoppedMeetingEquality

end

end OAI
