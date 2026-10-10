import OAI.Computability.PerfectCompleteness.Algebra.TensorRowAdviceLemmas
import OAI.Computability.PerfectCompleteness.Decoding.HierarchicalDecoderMeetingLemmas
import OAI.Computability.PerfectCompleteness.Decoding.RightDecoderWitness
import OAI.Computability.PerfectCompleteness.Machines.OwnInputAffineSliceLemmas

namespace OAI


namespace PerfectCompleteness.HierarchicalRawPrediction

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n) (lowerLevel : Nat)

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _

local instance valueFintype : Fintype
    (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (originalArrays : Ω → Arrays slots rows)
  (lowerEvent : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  {r : Nat} (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper lower)

abbrev Raw := OwnInputReference.RawSample slots rows upper lower (LinearMap.ker A) repeats cut
abbrev Visible := OwnInputAffineSlice.VisibleSample slots rows upper lower (LinearMap.ker A) repeats cut

abbrev rawArrays (sample : Raw slots rows upper lower A repeats cut) :=
  OwnInputRawAssembly.arrays slots rows upper lower (LinearMap.ker A) repeats cut sample

abbrev rawBackground (sample : Raw slots rows upper lower A repeats cut) :=
  HierarchicalMatrixTable.backgroundOf slots upper
    (rawArrays slots rows upper lower A repeats cut sample)

abbrev rawMatrix (sample : Raw slots rows upper lower A repeats cut) :=
  NodeEmbedding.matrix (rawArrays slots rows upper lower A repeats cut sample) upper

abbrev visibleBackground (v : Visible slots rows upper lower A repeats cut) :=
  OwnInputRawAssembly.background slots rows upper lower (LinearMap.ker A) repeats cut v

abbrev known (v : Visible slots rows upper lower A repeats cut) :=
  OwnInputRawAssembly.knownVisible slots rows upper lower (LinearMap.ker A) repeats cut v

abbrev hidden (sample : Raw slots rows upper lower A repeats cut) :=
  OwnInputAffineSlice.hiddenOutput slots rows upper lower (LinearMap.ker A) repeats cut sample

def rawJ (sample : Raw slots rows upper lower A repeats cut) : Bool :=
  GoodAdviceEvents.J
    (HierarchicalUsefulness.table slots upper lowerLevel original originalArrays lowerEvent κ σ
      (rawBackground slots rows upper lower A repeats cut sample)) r ρ
    (A, HierarchicalPrediction.quotientMatrix slots upper lowerLevel
      (rawBackground slots rows upper lower A repeats cut sample)
      (rawMatrix slots rows upper lower A repeats cut sample))

def rawPrediction (a : Block rows lower)
    (sample : Raw slots rows upper lower A repeats cut) : Bool :=
  HierarchicalPrediction.prediction slots upper lowerLevel
    (rawBackground slots rows upper lower A repeats cut sample) σ lower cut.upper_ne_lower a
    original originalArrays lowerEvent κ r ρ A (rawMatrix slots rows upper lower A repeats cut sample)

abbrev VisibleGood (v : Visible slots rows upper lower A repeats cut) : Prop :=
  HierarchicalTensorSlice.VisibleGood slots upper lowerLevel
    (visibleBackground slots rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known slots rows upper lower A repeats cut v)

abbrev tensorJ (v : Visible slots rows upper lower A repeats cut)
    (T : HierarchicalTensorSlice.HiddenTensor slots upper A) : Bool :=
  HierarchicalTensorSlice.J slots upper lowerLevel
    (visibleBackground slots rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known slots rows upper lower A repeats cut v) T

abbrev columnSpace (v : Visible slots rows upper lower A repeats cut)
    (hgood : VisibleGood slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v) :=
  HierarchicalTensorSlice.columnSpace slots upper lowerLevel
    (visibleBackground slots rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known slots rows upper lower A repeats cut v) hgood

abbrev target (v : Visible slots rows upper lower A repeats cut)
    (hgood : VisibleGood slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v)
    (hne : ∃ T, tensorJ slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v T = true) :=
  HierarchicalTensorSlice.target slots upper lowerLevel
    (visibleBackground slots rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known slots rows upper lower A repeats cut v) hgood hne

abbrev nativeCorrection (v : Visible slots rows upper lower A repeats cut)
    (hgood : VisibleGood slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v) :=
  HierarchicalTensorSlice.nativeCorrection slots upper lowerLevel
    (visibleBackground slots rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known slots rows upper lower A repeats cut v) hgood

abbrev visibleOffset (v : Visible slots rows upper lower A repeats cut)
    (hgood : VisibleGood slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v) :=
  HierarchicalTensorSlice.visibleOffset slots upper lowerLevel
    (visibleBackground slots rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known slots rows upper lower A repeats cut v) hgood

theorem rawJ_eq_tensorJ (sample : Raw slots rows upper lower A repeats cut) :
    rawJ slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut sample =
      tensorJ slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut
        sample.2 (hidden slots rows upper lower A repeats cut sample) := by
  exact congrArg₂
    (fun (b : HierarchicalMatrixTable.Background (rows := rows) slots upper)
        (X : HierarchicalMatrixTable.Matrix (rows := rows) slots upper) =>
      GoodAdviceEvents.J
        (HierarchicalUsefulness.table slots upper lowerLevel original originalArrays lowerEvent κ σ b)
        r ρ (A, HierarchicalPrediction.quotientMatrix slots upper lowerLevel b X))
    (OwnInputRawAssembly.background_arrays slots rows upper lower (LinearMap.ker A) repeats cut sample)
    (OwnInputRawAssembly.matrix_arrays slots rows upper lower (LinearMap.ker A) repeats cut sample)

theorem rawJ_iff_restriction (v : Visible slots rows upper lower A repeats cut)
    (hgood : VisibleGood slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v)
    (hne : ∃ T, tensorJ slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v T = true)
    (sample : Raw slots rows upper lower A repeats cut) (hv : sample.2 = v) :
    rawJ slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut sample =
        true ↔
      TensorRestriction.restrictionMap
        (columnSpace slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood) (hidden slots rows upper lower A repeats cut sample) =
        target slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood hne := by
  rw [rawJ_eq_tensorJ, hv]
  exact HierarchicalTensorSlice.J_iff_restriction slots upper lowerLevel
    (visibleBackground slots rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known slots rows upper lower A repeats cut v)
    hgood hne _

def responseMatch (a : Block rows lower) (v : Visible slots rows upper lower A repeats cut)
    (hgood : VisibleGood slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v) (sample : Raw slots rows upper lower A repeats cut) : Bool :=
  decide (OwnInputReference.response slots rows upper lower (LinearMap.ker A) a σ
      (OwnInputReference.readInput slots rows upper lower (LinearMap.ker A) a
        (OwnInputRawAssembly.scalarEval slots upper lower repeats cut) sample.2)
      (hidden slots rows upper lower A repeats cut sample) =
    visibleOffset slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v hgood +
      TensorBucketEvaluation.tensorOutputLinear (LinearMap.ker A)
        (nativeCorrection slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood) (hidden slots rows upper lower A repeats cut sample))

theorem rawPrediction_eq (a : Block rows lower) (v : Visible slots rows upper lower A repeats cut)
    (hgood : VisibleGood slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v) (sample : Raw slots rows upper lower A repeats cut) (hv : sample.2 = v) :
    rawPrediction slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut a sample =
      (rawJ slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut sample &&
      responseMatch slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut a v hgood sample) := by
  have hbg := OwnInputRawAssembly.background_arrays slots rows upper lower (LinearMap.ker A)
    repeats cut sample
  have hmat := OwnInputRawAssembly.matrix_arrays slots rows upper lower (LinearMap.ker A)
    repeats cut sample
  have hresponse := OwnInputRawAssembly.response_eq_rightUpper_totalMatrix slots rows upper lower
    (LinearMap.ker A) repeats cut a σ sample
  rw [hv] at hbg hmat hresponse
  have hprediction := congrArg₂
    (fun (b : HierarchicalMatrixTable.Background (rows := rows) slots upper)
        (X : HierarchicalMatrixTable.Matrix (rows := rows) slots upper) =>
      HierarchicalPrediction.prediction slots upper lowerLevel b σ lower cut.upper_ne_lower a
        original originalArrays lowerEvent κ r ρ A X) hbg hmat
  unfold rawPrediction
  rw [hprediction, rawJ_eq_tensorJ]
  simp only [hv]
  dsimp only [HierarchicalPrediction.prediction]
  rw [HierarchicalTensorSlice.selectedValue_eq_some slots upper lowerLevel
    (visibleBackground slots rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known slots rows upper lower A repeats cut v)
    hgood (hidden slots rows upper lower A repeats cut sample)]
  dsimp only
  rw [HierarchicalTensorSlice.affinePrediction_eq_tensor slots upper lowerLevel
    (visibleBackground slots rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known slots rows upper lower A repeats cut v)
    hgood (hidden slots rows upper lower A repeats cut sample), ← hresponse]
  simp only [tensorJ, HierarchicalTensorSlice.J, responseMatch, hv,
    TensorBucketEvaluation.tensorOutput]
  apply congrArg₂ (fun first second : Bool => first && second)
  · rfl
  · exact (@decide_eq_decide _ _ _ _).mpr Iff.rfl

def given (v : Visible slots rows upper lower A repeats cut)
    (sample : Raw slots rows upper lower A repeats cut) : Bool :=
  rawJ slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
    A repeats cut sample && decide (sample.2 = v)

theorem given_eq_jointEvent (v : Visible slots rows upper lower A repeats cut)
    (hgood : VisibleGood slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v)
    (hne : ∃ T, tensorJ slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v T = true) :
    given slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v =
      OwnInputAffineSlice.jointEvent slots rows upper lower (LinearMap.ker A) repeats cut
        (fun data => decide (data = v))
        (columnSpace slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood)
        (target slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood hne) := by
  funext sample
  by_cases hv : sample.2 = v
  · have hJ : rawJ slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut sample =
      OwnInputAffineSlice.tensorSlice (LinearMap.ker A)
        (columnSpace slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood)
        (target slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood hne) (hidden slots rows upper lower A repeats cut sample) := by
      apply Bool.eq_iff_iff.mpr
      simp only [OwnInputAffineSlice.tensorSlice, decide_eq_true_eq]
      exact rawJ_iff_restriction slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut v hgood hne sample hv
    unfold given OwnInputAffineSlice.jointEvent
    rw [hJ]
  · simp only [given, OwnInputAffineSlice.jointEvent, hv, decide_false, Bool.and_false]

theorem selection_of_positive
    (externalLaw : FiniteDistribution (OwnInputReference.Exterior slots rows upper lower))
    (v : Visible slots rows upper lower A repeats cut)
    (positive : 0 <
      (OwnInputReference.rawLaw slots rows upper lower (LinearMap.ker A) repeats cut externalLaw).probability
        (given slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v)) :
    VisibleGood slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v ∧
      ∃ T, tensorJ slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut v T = true := by
  have hex : ∃ sample, given slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v sample = true := by
    by_contra hnone
    have hfalse : given slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut v = fun _ => false := by
      funext sample
      exact Bool.eq_false_iff.mpr (fun hs => hnone ⟨sample, hs⟩)
    rw [hfalse, FiniteDistribution.probability_false] at positive
    exact (lt_irrefl 0) positive
  obtain ⟨sample, hs⟩ := hex
  have hp := Bool.and_eq_true_iff.mp hs
  have hv : sample.2 = v := @of_decide_eq_true _ _ hp.2
  have ht := hp.1
  rw [rawJ_eq_tensorJ, hv] at ht
  refine ⟨?_, hidden slots rows upper lower A repeats cut sample, ht⟩
  by_contra hbad
  have hfalse := HierarchicalTensorSlice.J_false_of_not_good slots upper lowerLevel
    (visibleBackground slots rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known slots rows upper lower A repeats cut v)
    hbad (hidden slots rows upper lower A repeats cut sample)
  exact Bool.noConfusion (hfalse.symm.trans ht)

theorem conditional_prediction_eq (a : Block rows lower)
    (externalLaw : FiniteDistribution (OwnInputReference.Exterior slots rows upper lower))
    (v : Visible slots rows upper lower A repeats cut)
    (hgood : VisibleGood slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v)
    (hne : ∃ T, tensorJ slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v T = true)
    (positive : 0 <
      (OwnInputReference.rawLaw slots rows upper lower (LinearMap.ker A) repeats cut externalLaw).probability
        (given slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v)) :
    ((OwnInputReference.rawLaw slots rows upper lower (LinearMap.ker A) repeats cut externalLaw).condition
      (given slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v)
      positive).probability
        (rawPrediction slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut a) =
      RightDecoderWitness.conditionalMatch slots rows upper lower (LinearMap.ker A) a repeats cut σ
        (OwnInputReference.readInput slots rows upper lower (LinearMap.ker A) a
          (OwnInputRawAssembly.scalarEval slots upper lower repeats cut) v)
        (columnSpace slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood)
        (target slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood hne)
        (nativeCorrection slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood)
        (visibleOffset slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood) := by
  let μ := OwnInputReference.rawLaw slots rows upper lower (LinearMap.ker A) repeats cut externalLaw
  let joint := OwnInputAffineSlice.jointEvent slots rows upper lower (LinearMap.ker A) repeats cut
    (fun data => decide (data = v))
    (columnSpace slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v hgood)
    (target slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v hgood hne)
  have hgiven : given slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v = joint :=
    given_eq_jointEvent slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v hgood hne
  have hpositive : 0 < μ.probability joint := by
    rw [← hgiven]
    exact positive
  trans (μ.condition
    (given slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v)
    positive).probability
      (responseMatch slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut a v hgood)
  · apply OwnInputAffineSlice.probability_condition_congr
    intro sample hs
    have hp := Bool.and_eq_true_iff.mp hs
    have hv : sample.2 = v := @of_decide_eq_true _ _ hp.2
    rw [rawPrediction_eq slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut a v hgood sample hv, hp.1, Bool.true_and]
  trans (μ.condition joint hpositive).probability
    (responseMatch slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut a v hgood)
  · simp only [FiniteDistribution.probability_condition, hgiven]
  · exact OwnInputAffineSlice.conditional_response_probability slots rows upper lower (LinearMap.ker A)
      a repeats cut externalLaw (fun data => decide (data = v))
      (columnSpace slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut v hgood)
      (target slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut v hgood hne) hpositive σ
      (OwnInputReference.readInput slots rows upper lower (LinearMap.ker A) a
        (OwnInputRawAssembly.scalarEval slots upper lower repeats cut) v)
      (by
        intro data hdata
        have hv : data = v := @of_decide_eq_true _ _ hdata
        subst data
        rfl)
      (nativeCorrection slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut v hgood)
      (visibleOffset slots rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut v hgood)

end
end PerfectCompleteness.HierarchicalRawPrediction


namespace PerfectCompleteness.HierarchicalRawMeeting

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype
attribute [local instance] RightDecoder.characterFintype RightDecoder.scalarFintype

variable {δ : ℚ} (plan : FixedRows.Plan δ) {branch : Nat → Nat} {t : Nat}
  (slots : RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (upper lower : Nodes branch plan.depth) (lowerLevel : Nat)

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _

local instance valueFintype : Fintype
    (Block (FixedRows.rows plan) upper ×
      HierarchicalMatrixTable.SideOutput (rows := FixedRows.rows plan) upper) :=
  Fintype.ofFinite _

local instance upperDualFintype : Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (originalArrays : Ω → Arrays slots (FixedRows.rows plan))
  (lowerEvent : Ω → Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))
  (A : ManyGoodRows.RowMap (Block (FixedRows.rows plan) upper) plan.order)
  (a : Block (FixedRows.rows plan) lower)
  (cut : OwnInputReference.Cut upper lower)
  (v : HierarchicalRawPrediction.Visible slots (FixedRows.rows plan) upper lower A
    (FixedRows.repeats plan) cut)

def meetingProbability : ℝ :=
  ((HierarchicalDecoderMeeting.leftLaw slots upper lowerLevel
    (HierarchicalRawPrediction.visibleBackground slots (FixedRows.rows plan) upper lower A
      (FixedRows.repeats plan) cut v)
    original originalArrays lowerEvent (InitialParameters.useful δ) σ plan.density A
    (HierarchicalRawPrediction.known slots (FixedRows.rows plan) upper lower A
      (FixedRows.repeats plan) cut v)).product
    (RightDecoder.law slots (FixedRows.rows plan) upper lower (LinearMap.ker A) a
      (FixedRows.repeats plan) cut σ
      (OwnInputReference.readInput slots (FixedRows.rows plan) upper lower (LinearMap.ker A) a
        (OwnInputRawAssembly.scalarEval slots upper lower (FixedRows.repeats plan) cut) v)
      (tau (InitialParameters.useful δ) plan.density plan.order
        (FixedRows.rows plan (Nodes.height upper))))).probability
    (fun pair => decide ((NodeEmbedding.embed slots upper).dualMap pair.1 = pair.2))

theorem meetingProbability_nonneg :
    0 ≤ meetingProbability plan slots upper lower lowerLevel original originalArrays lowerEvent σ A a cut v :=
  FiniteDistribution.probability_nonnegative _ _

theorem meeting_probability_lower (hδ : 0 < δ)
    (externalLaw : FiniteDistribution
      (OwnInputReference.Exterior slots (FixedRows.rows plan) upper lower))
    (positive : 0 <
      (OwnInputReference.rawLaw slots (FixedRows.rows plan) upper lower (LinearMap.ker A)
        (FixedRows.repeats plan) cut externalLaw).probability
        (HierarchicalRawPrediction.given slots (FixedRows.rows plan) upper lower lowerLevel
          original originalArrays lowerEvent (InitialParameters.useful δ) σ plan.density A
          (FixedRows.repeats plan) cut v))
    (hprediction : rhoPred (InitialParameters.useful δ) plan.density ≤
      ((OwnInputReference.rawLaw slots (FixedRows.rows plan) upper lower (LinearMap.ker A)
        (FixedRows.repeats plan) cut externalLaw).condition
        (HierarchicalRawPrediction.given slots (FixedRows.rows plan) upper lower lowerLevel
          original originalArrays lowerEvent (InitialParameters.useful δ) σ plan.density A
          (FixedRows.repeats plan) cut v) positive).probability
        (HierarchicalRawPrediction.rawPrediction slots (FixedRows.rows plan) upper lower lowerLevel
          original originalArrays lowerEvent (InitialParameters.useful δ) σ plan.density A
          (FixedRows.repeats plan) cut a)) :
    (1 / (2 : ℝ) ^ plan.order) *
        (tau (InitialParameters.useful δ) plan.density plan.order
          (FixedRows.rows plan (Nodes.height upper)) ^ 2 /
            (2 * (2 : ℝ) ^ FixedRows.rows plan (Nodes.height upper))) ≤
      meetingProbability plan slots upper lower lowerLevel original originalArrays lowerEvent σ A a cut v := by
  obtain ⟨hgood, hne⟩ := HierarchicalRawPrediction.selection_of_positive slots (FixedRows.rows plan)
    upper lower lowerLevel original originalArrays lowerEvent (InitialParameters.useful δ)
    σ plan.density A (FixedRows.repeats plan) cut externalLaw v positive
  unfold meetingProbability
  apply HierarchicalFixedDecoderMeeting.meeting_probability_lower plan hδ slots upper lowerLevel
    (HierarchicalRawPrediction.visibleBackground slots (FixedRows.rows plan) upper lower A
      (FixedRows.repeats plan) cut v)
    original originalArrays lowerEvent σ A
    (HierarchicalRawPrediction.known slots (FixedRows.rows plan) upper lower A
      (FixedRows.repeats plan) cut v)
    lower a cut
    (OwnInputReference.readInput slots (FixedRows.rows plan) upper lower (LinearMap.ker A) a
      (OwnInputRawAssembly.scalarEval slots upper lower (FixedRows.repeats plan) cut) v)
    hgood hne
  exact hprediction.trans_eq
    (HierarchicalRawPrediction.conditional_prediction_eq slots (FixedRows.rows plan) upper lower lowerLevel
      original originalArrays lowerEvent (InitialParameters.useful δ) σ plan.density A
      (FixedRows.repeats plan) cut a externalLaw v hgood hne positive)

end
end PerfectCompleteness.HierarchicalRawMeeting

end OAI
