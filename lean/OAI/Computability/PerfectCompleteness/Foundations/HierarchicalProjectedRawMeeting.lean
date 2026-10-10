import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalProjectedSliceLemmas
import OAI.Computability.PerfectCompleteness.Reduction.FixedComparisonErrorsLemmas

namespace OAI

section

namespace PerfectCompleteness.HierarchicalProjectedRawMeeting

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype
attribute [local instance] RightDecoder.characterFintype RightDecoder.scalarFintype

variable {δ : ℚ} (plan : FixedRows.Plan δ) {branch : Nat → Nat} {t : Nat}
  (slots projected : RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (slots s j) (projected s j))
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
  (original : FiniteDistribution Ω)
  (originalArrays : Ω → Arrays slots (FixedRows.rows plan))
  (lowerEvent : Ω → Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))
  (A : ManyGoodRows.RowMap (Block (FixedRows.rows plan) upper) plan.order)
  (a : Block (FixedRows.rows plan) lower)
  (cut : OwnInputReference.Cut upper lower)
  (v : HierarchicalProjectedRawPrediction.Visible projected (FixedRows.rows plan) upper lower A
    (FixedRows.repeats plan) cut)

def meetingProbability : ℝ :=
  ((HierarchicalProjectedMeeting.leftLaw slots projected projection upper lowerLevel
    (HierarchicalProjectedRawPrediction.visibleBackground slots projected projection
      (FixedRows.rows plan) upper lower A (FixedRows.repeats plan) cut v)
    original originalArrays lowerEvent (InitialParameters.useful δ) σ plan.density A
    (HierarchicalProjectedRawPrediction.known projected (FixedRows.rows plan) upper lower A
      (FixedRows.repeats plan) cut v)).product
    (RightDecoder.law projected (FixedRows.rows plan) upper lower (LinearMap.ker A) a
      (FixedRows.repeats plan) cut σ
      (OwnInputReference.readInput projected (FixedRows.rows plan) upper lower (LinearMap.ker A) a
        (OwnInputRawAssembly.scalarEval projected upper lower (FixedRows.repeats plan) cut) v)
      (tau (InitialParameters.useful δ) plan.density plan.order
        (FixedRows.rows plan (Nodes.height upper))))).probability
    (fun pair => decide ((ProjectedNodeEmbedding.intoOriginal projection upper).dualMap
      pair.1 = pair.2))

theorem meetingProbability_nonneg :
    0 ≤ meetingProbability plan slots projected projection upper lower lowerLevel
      original originalArrays lowerEvent σ A a cut v :=
  FiniteDistribution.probability_nonnegative _ _

theorem meeting_probability_lower (hδ : 0 < δ)
    (externalLaw : FiniteDistribution
      (OwnInputReference.Exterior projected (FixedRows.rows plan) upper lower))
    (positive : 0 <
      (OwnInputReference.rawLaw projected (FixedRows.rows plan) upper lower (LinearMap.ker A)
        (FixedRows.repeats plan) cut externalLaw).probability
        (HierarchicalProjectedRawPrediction.given slots projected projection (FixedRows.rows plan)
          upper lower lowerLevel original originalArrays lowerEvent (InitialParameters.useful δ)
          σ plan.density A (FixedRows.repeats plan) cut v))
    (hprediction : rhoPred (InitialParameters.useful δ) plan.density ≤
      ((OwnInputReference.rawLaw projected (FixedRows.rows plan) upper lower (LinearMap.ker A)
        (FixedRows.repeats plan) cut externalLaw).condition
        (HierarchicalProjectedRawPrediction.given slots projected projection (FixedRows.rows plan)
          upper lower lowerLevel original originalArrays lowerEvent (InitialParameters.useful δ)
          σ plan.density A (FixedRows.repeats plan) cut v) positive).probability
        (HierarchicalProjectedRawPrediction.rawPrediction slots projected projection (FixedRows.rows plan)
          upper lower lowerLevel original originalArrays lowerEvent (InitialParameters.useful δ)
          σ plan.density A (FixedRows.repeats plan) cut a)) :
    (1 / (2 : ℝ) ^ plan.order) *
        (tau (InitialParameters.useful δ) plan.density plan.order
          (FixedRows.rows plan (Nodes.height upper)) ^ 2 /
            (2 * (2 : ℝ) ^ FixedRows.rows plan (Nodes.height upper))) ≤
      meetingProbability plan slots projected projection upper lower lowerLevel
        original originalArrays lowerEvent σ A a cut v := by
  obtain ⟨hgood, hne⟩ := HierarchicalProjectedRawPrediction.selection_of_positive
    slots projected projection (FixedRows.rows plan) upper lower lowerLevel
    original originalArrays lowerEvent (InitialParameters.useful δ) σ plan.density A
    (FixedRows.repeats plan) cut externalLaw v positive
  unfold meetingProbability
  apply HierarchicalFixedProjectedMeeting.meeting_probability_lower plan hδ
    slots projected projection upper lowerLevel
    (HierarchicalProjectedRawPrediction.visibleBackground slots projected projection
      (FixedRows.rows plan) upper lower A (FixedRows.repeats plan) cut v)
    original originalArrays lowerEvent σ A
    (HierarchicalProjectedRawPrediction.known projected (FixedRows.rows plan) upper lower A
      (FixedRows.repeats plan) cut v)
    lower a cut
    (OwnInputReference.readInput projected (FixedRows.rows plan) upper lower (LinearMap.ker A) a
      (OwnInputRawAssembly.scalarEval projected upper lower (FixedRows.repeats plan) cut) v)
    hgood hne
  exact hprediction.trans_eq
    (HierarchicalProjectedRawPrediction.conditional_prediction_eq slots projected projection
      (FixedRows.rows plan) upper lower lowerLevel original originalArrays lowerEvent
      (InitialParameters.useful δ) σ plan.density A (FixedRows.repeats plan) cut
      a externalLaw v hgood hne positive)

end
end PerfectCompleteness.HierarchicalProjectedRawMeeting

end

end OAI
