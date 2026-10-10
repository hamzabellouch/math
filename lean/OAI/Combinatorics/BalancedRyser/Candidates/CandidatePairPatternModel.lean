import OAI.Combinatorics.BalancedRyser.Probability.RootPatternModel

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace Balanced.CandidateExposure

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance pairModelMeasurableSpace : MeasurableSpace F := ⊤

abbrev EligiblePair (g : Direction F) :=
  ↥(eligibleTuples g) × ↥(eligibleTuples g)

def pairSuccessEvent (g : Direction F) (a : EligiblePair g) : Set (MergedPairs F) :=
  {M | (∃ c, (∀ i, OnLine (tuplePoint M a.1.val i) (g, c)) ∧
      (∀ i, OnLine (tuplePoint M a.2.val i) (g, c))) ∧
    Function.Injective (tuplePoint M a.1.val) ∧
    Function.Injective (tuplePoint M a.2.val)}

abbrev pairPatternModel (g : Direction F) : PatternModel.{u} where
  Color := Direction F
  Value := fun _ => Bool → F
  law := fun _ => (PMF.uniformOfFintype (Bool → F)).toMeasure
  Label := EligiblePair g
  support := fun a => generatorSet a.1.val ∪ generatorSet a.2.val
  event := pairSuccessEvent g
  eventMeasurable := fun _ => (Set.toFinite _).measurableSet
  dependsOn := by
    intro a M N h
    have h₁ := TupleAlignment.tuplePoint_eq_of_eq_on_generators a.1.val
      (fun d hd => h d (Finset.mem_union_left _ hd))
    have h₂ := TupleAlignment.tuplePoint_eq_of_eq_on_generators a.2.val
      (fun d hd => h d (Finset.mem_union_right _ hd))
    simp only [pairSuccessEvent, Set.mem_ofPred_eq, h₁, h₂]

theorem pairPatternModel_support_card_le (g : Direction F) (a : EligiblePair g) :
    ((pairPatternModel g).support a).card ≤ 8 := by
  have h₁ : (generatorSet a.1.val).card = 4 := by
    have hi := (Finset.mem_filter.mp a.1.property).2.1
    exact (Finset.card_image_of_injective _ hi).trans (by simp)
  have h₂ : (generatorSet a.2.val).card = 4 := by
    have hi := (Finset.mem_filter.mp a.2.property).2.1
    exact (Finset.card_image_of_injective _ hi).trans (by simp)
  calc
    _ ≤ (generatorSet a.1.val).card + (generatorSet a.2.val).card :=
      Finset.card_union_le _ _
    _ = 8 := by rw [h₁, h₂]

theorem pairPatternModel_count (g : Direction F) (M : MergedPairs F) :
    (pairPatternModel g).count M =
      ((Finset.univ.filter fun a : EligiblePair g => M ∈ pairSuccessEvent g a).card : ℝ) := by
  simp only [PatternModel.count, PatternModel.indicator, pairPatternModel,
    Set.indicator_apply, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem pairSuccessEvent_swap (g : Direction F) (a : EligiblePair g) :
    pairSuccessEvent g a.swap = pairSuccessEvent g a := by
  ext M
  constructor <;> rintro ⟨⟨c, h₁, h₂⟩, hi₁, hi₂⟩ <;>
    exact ⟨⟨c, h₂, h₁⟩, hi₂, hi₁⟩

theorem pairPatternModel_overlapCount (g : Direction F)
    (K₀ K : Finset (Direction F)) (M : MergedPairs F) :
    (pairPatternModel g).overlapCount K₀ K M =
      ((Finset.univ.filter fun a : EligiblePair g =>
        ¬ Disjoint ((generatorSet a.1.val ∪ generatorSet a.2.val) \ K₀) K ∧
          M ∈ pairSuccessEvent g a).card : ℝ) := by
  simp only [PatternModel.overlapCount, PatternModel.indicator, pairPatternModel,
    Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Set.indicator_apply]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

theorem pairPatternModel_measure (g : Direction F) :
    (pairPatternModel g).measure = (offsetLaw F).toMeasure :=
  TupleAlignment.rootPatternModel_measure g

theorem pairPatternModel_fixedExpectation_exposed (g : Direction F)
    (K : Finset (Direction F)) (x : MergedPairs F) (f : MergedPairs F → ℝ) :
    (pairPatternModel g).fixedExpectation K x f =
      ∫ M, f M ∂(exposedLaw K x).toMeasure :=
  TupleAlignment.rootPatternModel_fixedExpectation_exposed g K x f

theorem mem_pairSuccessEvent_iff (g : Direction F) (a : EligiblePair g)
    (M : MergedPairs F) :
    M ∈ pairSuccessEvent g a ↔
      M ∈ successfulInDirection a.1.val g ∧
      (∀ i, OnLine (tuplePoint M a.2.val i)
        (g, lineEval g (tuplePoint M a.1.val 0))) ∧
      Function.Injective (tuplePoint M a.2.val) := by
  constructor
  · rintro ⟨⟨c, h₁, h₂⟩, hi₁, hi₂⟩
    refine ⟨⟨⟨c, h₁⟩, hi₁⟩, ?_, hi₂⟩
    have hc : lineEval g (tuplePoint M a.1.val 0) = c := h₁ 0
    simpa only [hc] using h₂
  · rintro ⟨⟨⟨c, h₁⟩, hi₁⟩, h₂, hi₂⟩
    refine ⟨⟨c, h₁, ?_⟩, hi₁, hi₂⟩
    have hc : lineEval g (tuplePoint M a.1.val 0) = c := h₁ 0
    simpa only [hc] using h₂

end Balanced.CandidateExposure

end

end OAI
