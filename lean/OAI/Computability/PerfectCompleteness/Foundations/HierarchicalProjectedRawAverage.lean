import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalProjectedRawMeeting
import OAI.Computability.PerfectCompleteness.Foundations.TupleIndexEmitterLemmas

namespace OAI

section

namespace PerfectCompleteness.HierarchicalProjectedRawAverage

noncomputable section

open scoped BigOperators Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

private theorem event_mass_le_expectation {X : Type*} [Fintype X]
    (μ : FiniteDistribution X) (event : X → Bool) (value : X → ℝ) (factor : ℝ)
    (hnonneg : ∀ x, 0 ≤ value x)
    (hbound : ∀ x, event x = true → factor ≤ value x) :
    factor * μ.probability event ≤ μ.expectation value := by
  unfold FiniteDistribution.probability FiniteDistribution.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : event x = true
  · rw [ite_eq_left hx]
    calc
      factor * μ.weight x = μ.weight x * factor := mul_comm _ _
      _ ≤ μ.weight x * value x :=
        mul_le_mul_of_nonneg_left (hbound x hx) (μ.nonnegative x)
  · rw [ite_eq_right hx, mul_zero]
    exact mul_nonneg (μ.nonnegative x) (hnonneg x)

variable {δ : ℚ} (plan : FixedRows.Plan δ) {branch : Nat → Nat} {t : Nat}
  (slots projected : RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (slots s j) (projected s j))
  (upper lower : Nodes branch plan.depth) (lowerLevel : Nat)
  {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (originalArrays : Ω → Arrays slots (FixedRows.rows plan))
  (lowerEvent : Ω → Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))
  (A : ManyGoodRows.RowMap (Block (FixedRows.rows plan) upper) plan.order)
  (a : Block (FixedRows.rows plan) lower) (cut : OwnInputReference.Cut upper lower)

abbrev Raw := HierarchicalProjectedRawPrediction.Raw projected (FixedRows.rows plan) upper lower A
  (FixedRows.repeats plan) cut

abbrev Visible := HierarchicalProjectedRawPrediction.Visible projected (FixedRows.rows plan) upper lower A
  (FixedRows.repeats plan) cut

def law (externalLaw : FiniteDistribution
    (OwnInputReference.Exterior projected (FixedRows.rows plan) upper lower)) :
    FiniteDistribution (Raw plan projected upper lower A cut) :=
  OwnInputReference.rawLaw projected (FixedRows.rows plan) upper lower (LinearMap.ker A)
    (FixedRows.repeats plan) cut externalLaw

abbrev J := HierarchicalProjectedRawPrediction.rawJ slots projected projection (FixedRows.rows plan) upper lower lowerLevel
  original originalArrays lowerEvent (InitialParameters.useful δ) σ plan.density A
  (FixedRows.repeats plan) cut

abbrev prediction := HierarchicalProjectedRawPrediction.rawPrediction slots projected projection (FixedRows.rows plan) upper lower lowerLevel
  original originalArrays lowerEvent (InitialParameters.useful δ) σ plan.density A
  (FixedRows.repeats plan) cut a

def goodRecord (externalLaw : FiniteDistribution
    (OwnInputReference.Exterior projected (FixedRows.rows plan) upper lower))
    (v : Visible plan projected upper lower A cut) : Bool :=
  PositiveFiberMass.goodRecord (law plan projected upper lower A cut externalLaw)
    (fun sample : Raw plan projected upper lower A cut => sample.2)
    (J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut)
    (prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut)
    (rhoPred (InitialParameters.useful δ) plan.density) v

def goodEvent (externalLaw : FiniteDistribution
    (OwnInputReference.Exterior projected (FixedRows.rows plan) upper lower))
    (sample : Raw plan projected upper lower A cut) : Bool :=
  J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut sample &&
    goodRecord plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut
      externalLaw sample.2

def factor : ℝ :=
  (1 / (2 : ℝ) ^ plan.order) *
    (tau (InitialParameters.useful δ) plan.density plan.order
      (FixedRows.rows plan (Nodes.height upper)) ^ 2 /
        (2 * (2 : ℝ) ^ FixedRows.rows plan (Nodes.height upper)))

theorem factor_nonneg : 0 ≤ factor plan upper := by
  unfold factor
  positivity

abbrev meetingProbability :=
  HierarchicalProjectedRawMeeting.meetingProbability plan slots projected projection upper lower lowerLevel
    original originalArrays lowerEvent σ A a cut

def expectedMeeting (externalLaw : FiniteDistribution
    (OwnInputReference.Exterior projected (FixedRows.rows plan) upper lower)) : ℝ :=
  (law plan projected upper lower A cut externalLaw).expectation
    (fun sample => meetingProbability plan slots projected projection upper lower lowerLevel
      original originalArrays lowerEvent σ A a cut sample.2)

theorem meeting_lower_of_goodRecord (hδ : 0 < δ)
    (externalLaw : FiniteDistribution
      (OwnInputReference.Exterior projected (FixedRows.rows plan) upper lower))
    (v : Visible plan projected upper lower A cut)
    (hgood : goodRecord plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ
      A a cut externalLaw v = true) :
    factor plan upper ≤
      meetingProbability plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut v := by
  have hpositive := (PositiveFiberMass.goodRecord_iff
    (law plan projected upper lower A cut externalLaw)
    (fun sample : Raw plan projected upper lower A cut => sample.2)
    (J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut)
    (prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut)
    (rhoPred (InitialParameters.useful δ) plan.density) v).mp hgood
  let originalGiven : Raw plan projected upper lower A cut → Bool := fun sample =>
    J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut sample &&
      @decide (sample.2 = v) (Classical.propDecidable _)
  have hgiven : originalGiven =
      HierarchicalProjectedRawPrediction.given slots projected projection (FixedRows.rows plan) upper lower lowerLevel
        original originalArrays lowerEvent (InitialParameters.useful δ) σ plan.density A
        (FixedRows.repeats plan) cut v := by
    funext sample
    unfold originalGiven HierarchicalProjectedRawPrediction.given
    apply congrArg (fun flag : Bool =>
      J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut sample && flag)
    exact (@decide_eq_decide _ _ _ _).mpr Iff.rfl
  have positive : 0 < (law plan projected upper lower A cut externalLaw).probability
      (HierarchicalProjectedRawPrediction.given slots projected projection (FixedRows.rows plan) upper lower lowerLevel
        original originalArrays lowerEvent (InitialParameters.useful δ) σ plan.density A
        (FixedRows.repeats plan) cut v) := by
    rw [← hgiven]
    exact hpositive.1
  have conditional : rhoPred (InitialParameters.useful δ) plan.density ≤
      ((law plan projected upper lower A cut externalLaw).condition
        (HierarchicalProjectedRawPrediction.given slots projected projection (FixedRows.rows plan) upper lower lowerLevel
          original originalArrays lowerEvent (InitialParameters.useful δ) σ plan.density A
          (FixedRows.repeats plan) cut v) positive).probability
        (prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut) := by
    have hprediction := hpositive.2
    have hmatch : (fun sample : Raw plan projected upper lower A cut =>
        originalGiven sample &&
          prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut sample) =
        (fun sample =>
          (J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut sample &&
            prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut sample) &&
          @decide (sample.2 = v) (Classical.propDecidable _)) := by
      funext sample
      dsimp only [originalGiven]
      cases J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut sample <;>
        cases prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut sample <;>
        cases @decide (sample.2 = v) (Classical.propDecidable _) <;> rfl
    change rhoPred (InitialParameters.useful δ) plan.density ≤
      (law plan projected upper lower A cut externalLaw).probability
        (fun sample =>
          (J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut sample &&
            prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut sample) &&
          @decide (sample.2 = v) (Classical.propDecidable _)) /
      (law plan projected upper lower A cut externalLaw).probability originalGiven at hprediction
    rw [← hmatch, hgiven] at hprediction
    exact hprediction.trans_eq
      (FiniteDistribution.probability_condition (law plan projected upper lower A cut externalLaw)
        (HierarchicalProjectedRawPrediction.given slots projected projection (FixedRows.rows plan) upper lower lowerLevel
          original originalArrays lowerEvent (InitialParameters.useful δ) σ plan.density A
          (FixedRows.repeats plan) cut v)
        (prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut)
        positive).symm
  exact HierarchicalProjectedRawMeeting.meeting_probability_lower plan slots projected projection upper lower lowerLevel
    original originalArrays lowerEvent σ A a cut v hδ externalLaw positive conditional

theorem expectedMeeting_ge_good_mass (hδ : 0 < δ)
    (externalLaw : FiniteDistribution
      (OwnInputReference.Exterior projected (FixedRows.rows plan) upper lower)) :
    factor plan upper *
      (law plan projected upper lower A cut externalLaw).probability
        (goodEvent plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut externalLaw) ≤
      expectedMeeting plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut externalLaw := by
  apply event_mass_le_expectation
  · intro sample
    exact HierarchicalProjectedRawMeeting.meetingProbability_nonneg plan slots projected projection upper lower lowerLevel
      original originalArrays lowerEvent σ A a cut sample.2
  · intro sample hs
    exact meeting_lower_of_goodRecord plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ
      A a cut hδ externalLaw sample.2 (Bool.and_eq_true_iff.mp hs).2

theorem J_and_prediction :
    (fun sample => J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut sample &&
      prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut sample) =
      prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut := by
  funext sample
  unfold J prediction HierarchicalProjectedRawPrediction.rawJ HierarchicalProjectedRawPrediction.rawPrediction
    HierarchicalPrediction.prediction
  exact Bool.and_self_left _ _

theorem prediction_difference_le_good_mass (hδ : 0 < δ)
    (externalLaw : FiniteDistribution
      (OwnInputReference.Exterior projected (FixedRows.rows plan) upper lower)) :
    (law plan projected upper lower A cut externalLaw).probability
        (prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut) -
      rhoPred (InitialParameters.useful δ) plan.density *
        (law plan projected upper lower A cut externalLaw).probability
          (J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut) ≤
      (law plan projected upper lower A cut externalLaw).probability
        (goodEvent plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut externalLaw) := by
  have h := PositiveFiberMass.difference_le_good_mass
    (law plan projected upper lower A cut externalLaw)
    (fun sample : Raw plan projected upper lower A cut => sample.2)
    (J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut)
    (prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut)
    (rhoPred (InitialParameters.useful δ) plan.density)
    (rhoPred_pos (InitialParameters.useful_pos hδ) plan.density_pos).le
  rw [J_and_prediction] at h
  exact h

theorem expectedMeeting_ge_prediction_difference (hδ : 0 < δ)
    (externalLaw : FiniteDistribution
      (OwnInputReference.Exterior projected (FixedRows.rows plan) upper lower)) :
    factor plan upper *
      ((law plan projected upper lower A cut externalLaw).probability
          (prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut) -
        rhoPred (InitialParameters.useful δ) plan.density *
          (law plan projected upper lower A cut externalLaw).probability
            (J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut)) ≤
      expectedMeeting plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut externalLaw :=
  (mul_le_mul_of_nonneg_left
    (prediction_difference_le_good_mass plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ
      A a cut hδ externalLaw) (factor_nonneg plan upper)).trans
    (expectedMeeting_ge_good_mass plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ
      A a cut hδ externalLaw)

end
end PerfectCompleteness.HierarchicalProjectedRawAverage

end

end OAI
