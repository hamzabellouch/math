import Mathlib.Tactic.Ring
import OAI.Computability.PerfectCompleteness.Construction.HierarchicalAdviceFromBuckets
import OAI.Computability.PerfectCompleteness.Decoding.HierarchicalDecoderMeetingLemmas
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalProjectedSliceLemmas
import OAI.Computability.PerfectCompleteness.Reduction.FixedCallBudgetLemmas

namespace OAI


namespace PerfectCompleteness.FixedComparisonErrors

open FixedParameters ChildBlockCardinality

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

theorem comparison_errors {retained : Nat} (hcalls : retained ≤ calls p.plan)
    (height : Nat) :
    let L : ℝ := bound (branch p) height (FixedRows.sourceLength p.plan hδ)
      retained (FixedRows.rows p.plan)
    let m := p.cubeSize height
    Real.sqrt (L ^ 2 / (m : ℝ) ^ 3) / 2 < p.accuracy ∧
      Real.sqrt ((1 + L ^ 2 / (m : ℝ) ^ 4) ^ (m ^ 3) - 1) / 2 < p.accuracy ∧
      2 * ((1 / (m : ℝ) ^ 2) * L / (1 - 1 / (m : ℝ) ^ 2)) < p.accuracy := by
  let L : ℝ := bound (branch p) height (FixedRows.sourceLength p.plan hδ)
    retained (FixedRows.rows p.plan)
  let B : ℝ := bound (branch p) height (FixedRows.sourceLength p.plan hδ)
    (calls p.plan) (FixedRows.rows p.plan)
  let m := p.cubeSize height
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hLB : L ≤ B := by
    dsimp only [L, B]
    exact_mod_cast FixedCallBudget.child_bound_mono hcalls (branch p) height
      (FixedRows.sourceLength p.plan hδ) (FixedRows.rows p.plan)
  have hsq : L ^ 2 ≤ B ^ 2 := (sq_le_sq₀ hL hB).mpr hLB
  have hm : (2 : ℝ) ≤ m := by exact_mod_cast (p.cube_errors height).1
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have hprob : (1 : ℝ) / (m : ℝ) ^ 2 < 1 := by
    apply (div_lt_one hm2).mpr
    nlinarith
  have hfixed := (p.cube_errors height).2
  change Real.sqrt (L ^ 2 / (m : ℝ) ^ 3) / 2 < p.accuracy ∧
    Real.sqrt ((1 + L ^ 2 / (m : ℝ) ^ 4) ^ (m ^ 3) - 1) / 2 < p.accuracy ∧
    2 * ((1 / (m : ℝ) ^ 2) * L / (1 - 1 / (m : ℝ) ^ 2)) < p.accuracy
  refine ⟨?_, ?_, ?_⟩
  · apply lt_of_le_of_lt _ hfixed.1
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right hsq (by positivity)
  · apply lt_of_le_of_lt _ hfixed.2.1
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.sqrt_le_sqrt
    apply sub_le_sub_right
    apply pow_le_pow_left₀ (by positivity)
    exact add_le_add_right
      (div_le_div_of_nonneg_right hsq
        (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 4)) 1
  · apply lt_of_le_of_lt _ hfixed.2.2.1
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_left hLB (by positivity)

end
end PerfectCompleteness.FixedComparisonErrors


namespace PerfectCompleteness.HierarchicalFixedAdvice

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open InitialParameters UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)
  {branch : Nat → Nat} {t : Nat} {Ω P : Type*} [Fintype Ω] [Fintype P]
  (S : HierarchicalAdviceExperiment.Experiment branch (FixedRows.rows p.plan) p.plan.depth t Ω)

local instance backgroundFintype : Fintype (HierarchicalAdviceExperiment.Background S) :=
  Fintype.ofFinite _

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace S.slots S.upper) :=
  Fintype.ofFinite _

local instance inputFintype :
    (b : HierarchicalAdviceExperiment.Background S) → Fintype (HierarchicalAdviceExperiment.Input S b) :=
  HierarchicalAdviceExperiment.inputFintype S

local instance inputFiniteDimensional :
    (b : HierarchicalAdviceExperiment.Background S) →
      FiniteDimensional F2 (HierarchicalAdviceExperiment.Input S b) :=
  HierarchicalAdviceExperiment.inputFiniteDimensional S

theorem rows_positive : 0 < FixedRows.rows p.plan (Nodes.height S.upper) := by
  exact p.plan.rows_pos (p.plan.depth - Nodes.height S.upper)

theorem adviceFactor_eq :
    HierarchicalAdviceFromBuckets.adviceFactor S p.plan.order (inverse δ) =
      q (inverse δ) p.plan.order (FixedRows.rows p.plan (Nodes.height S.upper)) := by
  simp only [HierarchicalAdviceFromBuckets.adviceFactor, q, g, h,
    div_eq_mul_inv, pow_two]
  ring

theorem paired_error_small : 10 * p.accuracy ≤ simultaneous δ ^ 2 / 16 := by
  have hs := p.accuracy_small 0 (Nat.zero_le _)
  simp only [CommonAccuracy.tolerance, lt_min_iff] at hs
  linarith [hs.2.1]

theorem coarse_error_small :
    10 * p.accuracy ≤ p.plan.density *
      HierarchicalAdviceFromBuckets.adviceFactor S p.plan.order (inverse δ) / 16 := by
  rw [adviceFactor_eq p S]
  have hs := p.accuracy_small (Nodes.height S.upper) (Nodes.height_le S.upper)
  simp only [CommonAccuracy.tolerance, lt_min_iff] at hs
  linarith [hs.2.2.1]

variable (externalLaw : FiniteDistribution P)
  (background : P → HierarchicalAdviceExperiment.Background S)
  (scalarLaw : P → FiniteDistribution (NodeEmbedding.RowSpace S.slots S.upper))

theorem prediction_difference
    (hmass : simultaneous δ / 2 ≤ HierarchicalAdviceFromBuckets.usefulProbability
      S (useful δ) externalLaw background scalarLaw (rows_positive p S))
    (hpaired : (HierarchicalAdviceFromBuckets.pairedLaw S externalLaw background
      scalarLaw (rows_positive p S)).totalVariation
        (HierarchicalAgreementMean.referenceLaw S.slots S.upper
          (HierarchicalAdviceFromBuckets.backgroundLaw S externalLaw background)
          (rows_positive p S)) ≤ 10 * p.accuracy)
    (hcoarse : ((HierarchicalAdviceExperiment.originalLaw S p.plan.order).pushforward
      (HierarchicalAdviceExperiment.observe S p.plan.order)).totalVariation
        ((HierarchicalAdviceExperiment.referenceLaw S
          (HierarchicalAdviceFromBuckets.backgroundLaw S externalLaw background) p.plan.order).pushforward (HierarchicalAdviceExperiment.referenceObserve S p.plan.order)) ≤
        10 * p.accuracy) :
    b (useful δ) p.plan.density (inverse δ) p.plan.order
        (FixedRows.rows p.plan (Nodes.height S.upper)) ≤
      (HierarchicalAdviceExperiment.originalLaw S p.plan.order).probability
        (HierarchicalAdviceExperiment.prediction S (useful δ) p.plan.order p.plan.density) -
      rhoPred (useful δ) p.plan.density *
        (HierarchicalAdviceExperiment.originalLaw S p.plan.order).probability
          (fun x => HierarchicalAdviceExperiment.J S (useful δ) p.plan.order p.plan.density
            (HierarchicalAdviceExperiment.observe S p.plan.order x)) := by
  have hbound := HierarchicalAdviceFromBuckets.prediction_difference S (useful δ)
    externalLaw background scalarLaw (rows_positive p S) (useful_pos hδ).le
    (simultaneous δ) (simultaneous_pos hδ).le hmass
    (hpaired.trans (paired_error_small p))
    p.plan.order p.plan.density (inverse δ) (10 * p.accuracy)
    (inverse_pos hδ) (by unfold inverse; linarith)
    p.plan.density_pos p.plan.density_lt p.plan.spectral
    (by have := p.accuracy_pos; positivity) (coarse_error_small p S) hcoarse
  rw [adviceFactor_eq p S] at hbound
  have hfactor : useful δ * p.plan.density *
      q (inverse δ) p.plan.order (FixedRows.rows p.plan (Nodes.height S.upper)) / 4 =
      b (useful δ) p.plan.density (inverse δ) p.plan.order
        (FixedRows.rows p.plan (Nodes.height S.upper)) := by
    unfold b rhoPred
    ring
  rw [hfactor] at hbound
  exact hbound

theorem good_record_mass_ge {R : Type*} [Fintype R]
    (hmass : simultaneous δ / 2 ≤ HierarchicalAdviceFromBuckets.usefulProbability
      S (useful δ) externalLaw background scalarLaw (rows_positive p S))
    (hpaired : (HierarchicalAdviceFromBuckets.pairedLaw S externalLaw background
      scalarLaw (rows_positive p S)).totalVariation
        (HierarchicalAgreementMean.referenceLaw S.slots S.upper
          (HierarchicalAdviceFromBuckets.backgroundLaw S externalLaw background)
          (rows_positive p S)) ≤ 10 * p.accuracy)
    (hcoarse : ((HierarchicalAdviceExperiment.originalLaw S p.plan.order).pushforward
      (HierarchicalAdviceExperiment.observe S p.plan.order)).totalVariation
        ((HierarchicalAdviceExperiment.referenceLaw S
          (HierarchicalAdviceFromBuckets.backgroundLaw S externalLaw background) p.plan.order).pushforward (HierarchicalAdviceExperiment.referenceObserve S p.plan.order)) ≤
        10 * p.accuracy)
    (record : Ω × HierarchicalAdviceExperiment.Advice S p.plan.order → R) :
    b (useful δ) p.plan.density (inverse δ) p.plan.order
        (FixedRows.rows p.plan (Nodes.height S.upper)) ≤
      (HierarchicalAdviceExperiment.originalLaw S p.plan.order).probability
        (fun x => HierarchicalAdviceExperiment.J S (useful δ) p.plan.order p.plan.density
          (HierarchicalAdviceExperiment.observe S p.plan.order x) &&
          PositiveFiberMass.goodRecord (HierarchicalAdviceExperiment.originalLaw S p.plan.order) record
            (fun y => HierarchicalAdviceExperiment.J S (useful δ) p.plan.order p.plan.density
              (HierarchicalAdviceExperiment.observe S p.plan.order y))
            (HierarchicalAdviceExperiment.prediction S (useful δ) p.plan.order p.plan.density)
            (rhoPred (useful δ) p.plan.density) (record x)) :=
  (prediction_difference p S externalLaw background scalarLaw hmass hpaired hcoarse).trans
    (HierarchicalAdviceExperiment.prediction_difference_le_good_mass S (useful δ)
      (useful_pos hδ).le p.plan.order p.plan.density p.plan.density_pos.le record)

end
end PerfectCompleteness.HierarchicalFixedAdvice


namespace PerfectCompleteness.HierarchicalFixedProjectedMeeting

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays HierarchicalProjectedSlice
open UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype
attribute [local instance] RightDecoder.characterFintype RightDecoder.scalarFintype

variable {δ : ℚ} (plan : FixedRows.Plan δ) (hδ : 0 < δ)
  {branch : Nat → Nat} {t : Nat}
  (slots projected : RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (slots s j) (projected s j))
  (upper : Nodes branch plan.depth) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background
    (rows := FixedRows.rows plan) slots upper)

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _

local instance valueFintype : Fintype
    (Block (FixedRows.rows plan) upper ×
      HierarchicalMatrixTable.SideOutput (rows := FixedRows.rows plan) upper) :=
  Fintype.ofFinite _

local instance upperDualFintype : Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (arrays : Ω → Arrays slots (FixedRows.rows plan))
  (lowerEvent : Ω → Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))
  (A : ManyGoodRows.RowMap (Block (FixedRows.rows plan) upper) plan.order)
  (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) → NodeEmbedding.NodeH projected upper)
  (lower : Nodes branch plan.depth) (a : Block (FixedRows.rows plan) lower)
  (cut : OwnInputReference.Cut upper lower)
  (input : OwnInputReference.Input projected (FixedRows.rows plan) upper lower (LinearMap.ker A) a)

include hδ

theorem meeting_probability_lower
    (hgood : VisibleGood slots projected projection upper lowerLevel background
      original arrays lowerEvent (InitialParameters.useful δ) σ plan.density A known)
    (hne : ∃ T, J slots projected projection upper lowerLevel background
      original arrays lowerEvent (InitialParameters.useful δ) σ plan.density A known T = true)
    (hmatch : rhoPred (InitialParameters.useful δ) plan.density ≤
      RightDecoderWitness.conditionalMatch projected (FixedRows.rows plan) upper lower
        (LinearMap.ker A) a (FixedRows.repeats plan) cut σ input
        (columnSpace slots projected projection upper lowerLevel background
          original arrays lowerEvent (InitialParameters.useful δ) σ plan.density A known hgood)
        (target slots projected projection upper lowerLevel background
          original arrays lowerEvent (InitialParameters.useful δ) σ plan.density A known hgood hne)
        (nativeCorrection slots projected projection upper lowerLevel background
          original arrays lowerEvent (InitialParameters.useful δ) σ plan.density A known hgood)
        (visibleOffset slots projected projection upper lowerLevel background
          original arrays lowerEvent (InitialParameters.useful δ) σ plan.density A known hgood)) :
    (1 / (2 : ℝ) ^ plan.order) *
        (tau (InitialParameters.useful δ) plan.density plan.order
          (FixedRows.rows plan (Nodes.height upper)) ^ 2 /
            (2 * (2 : ℝ) ^ FixedRows.rows plan (Nodes.height upper))) ≤
      ((HierarchicalProjectedMeeting.leftLaw slots projected projection upper lowerLevel
        background original arrays lowerEvent (InitialParameters.useful δ) σ plan.density A known).product
        (RightDecoder.law projected (FixedRows.rows plan) upper lower (LinearMap.ker A) a
          (FixedRows.repeats plan) cut σ input
          (tau (InitialParameters.useful δ) plan.density plan.order
            (FixedRows.rows plan (Nodes.height upper))))).probability
          (fun pair => decide ((ProjectedNodeEmbedding.intoOriginal projection upper).dualMap
            pair.1 = pair.2)) := by
  simpa only [UpperParameterScalars.tau] using
    (HierarchicalProjectedMeeting.meeting_probability_lower slots projected projection upper lowerLevel
      background original arrays lowerEvent (InitialParameters.useful δ) σ plan.density A known
      lower a (FixedRows.repeats plan) cut input hgood hne
      (rhoPred (InitialParameters.useful δ) plan.density)
      (h plan.order (FixedRows.rows plan (Nodes.height upper)))
      (rhoPred_pos (InitialParameters.useful_pos hδ) plan.density_pos)
      (h_pos plan.order (FixedRows.rows plan (Nodes.height upper)))
      (HierarchicalFixedDecoderMeeting.repetitionsBalanced plan)
      (HierarchicalFixedDecoderMeeting.slice_error plan (Nodes.height upper))
      (HierarchicalFixedDecoderMeeting.list_error plan (Nodes.height upper))
      (HierarchicalFixedDecoderMeeting.kernel_excluded plan (Nodes.height upper) A)
      le_rfl hmatch)

end
end PerfectCompleteness.HierarchicalFixedProjectedMeeting

end OAI
