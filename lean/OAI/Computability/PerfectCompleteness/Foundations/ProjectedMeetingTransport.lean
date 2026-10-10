import OAI.Computability.PerfectCompleteness.Reduction.FixedRows
import OAI.Computability.PerfectCompleteness.Repetition.CleanPhysicalProjectedMeeting

namespace OAI

section

namespace PerfectCompleteness.ProjectedMeetingTransport

noncomputable section

open scoped Classical
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype RightDecoder.scalarFintype

local instance physicalLeftFintype {branch : Nat → Nat} {n t : Nat}
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n) :
    Fintype (Module.Dual (ZMod 2) (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)

variable {δ : ℚ} (plan : FixedRows.Plan δ) {branch : Nat → Nat} {t : Nat}
  {Sample : OriginalDecoderMark.SlotFamily branch plan.depth t → Type*}
  [∀ slots, Fintype (Sample slots)]
  (F : OriginalDecoderMark.Family branch (FixedRows.rows plan) plan.depth t Sample)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))
  (slots projected : Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (slots s j) (projected s j))
  (upper lower : Nodes branch plan.depth) (lowerLevel : Nat)
  (A : ManyGoodRows.RowMap (Block (FixedRows.rows plan) upper) plan.order)
  (a : Block (FixedRows.rows plan) lower) (cut : OwnInputReference.Cut upper lower)
  (threshold : ℝ)
  (visible : HierarchicalProjectedRawPrediction.Visible projected (FixedRows.rows plan)
    upper lower A (FixedRows.repeats plan) cut)

def familyMeetingProbability : ℝ :=
  ((HierarchicalProjectedMeeting.leftLaw slots projected projection upper lowerLevel
    (HierarchicalProjectedRawPrediction.visibleBackground slots projected projection
      (FixedRows.rows plan) upper lower A (FixedRows.repeats plan) cut visible)
    (F.original slots) (F.arrays slots) (F.lowerEvent slots) (InitialParameters.useful δ)
    σ plan.density A
    (HierarchicalProjectedRawPrediction.known projected (FixedRows.rows plan)
      upper lower A (FixedRows.repeats plan) cut visible)).product
    (RightDecoder.law projected (FixedRows.rows plan) upper lower (LinearMap.ker A) a
      (FixedRows.repeats plan) cut σ
      (OwnInputReference.readInput projected (FixedRows.rows plan) upper lower
        (LinearMap.ker A) a
        (OwnInputRawAssembly.scalarEval projected upper lower (FixedRows.repeats plan) cut)
        visible) threshold)).probability
    (fun answer => decide ((ProjectedNodeEmbedding.intoOriginal projection upper).dualMap
      answer.1 = answer.2))

theorem familyMeetingProbability_congr
    (target other : Slots branch plan.depth → Fin t → MixedSupport.Slot)
    (otherLower : Nodes branch plan.depth)
    (projection' : ∀ s j, MixedSupport.Projection (target s j) (other s j))
    (a' : Block (FixedRows.rows plan) otherLower)
    (cut' : OwnInputReference.Cut upper otherLower)
    (visible' : HierarchicalProjectedRawPrediction.Visible other (FixedRows.rows plan)
      upper otherLower A (FixedRows.repeats plan) cut')
    (hs : slots = target) (hp : projected = other) (hl : lower = otherLower)
    (hprojection : HEq projection projection') (ha : HEq a a')
    (hcut : HEq cut cut') (hvisible : HEq visible visible') :
    familyMeetingProbability plan F σ slots projected projection upper lower lowerLevel
        A a cut threshold visible =
      familyMeetingProbability plan F σ target other projection' upper otherLower lowerLevel
        A a' cut' threshold visible' := by
  cases hs
  cases hp
  cases hl
  have hprojection' : projection = projection' := eq_of_heq hprojection
  cases hprojection'
  have ha' : a = a' := eq_of_heq ha
  cases ha'
  have hcut' : cut = cut' := eq_of_heq hcut
  cases hcut'
  have hvisible' : visible = visible' := eq_of_heq hvisible
  cases hvisible'
  rfl

end
end PerfectCompleteness.ProjectedMeetingTransport

end

end OAI
