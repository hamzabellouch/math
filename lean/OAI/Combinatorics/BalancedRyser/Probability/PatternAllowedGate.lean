import OAI.Combinatorics.BalancedRyser.Probability.PatternConditionalMean

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced.PatternModel

universe u
noncomputable section
attribute [local instance] Classical.propDecidable

def gateInitialEvent (P : PatternModel.{u}) (K₀ : Finset P.Color)
    (S : Set P.Sample) (hS : MeasurableSet S)
    (hdepends : ∀ x y, (∀ c ∈ K₀, x c = y c) → (x ∈ S ↔ y ∈ S)) :
    PatternModel.{u} where
  Color := P.Color
  colorFintype := P.colorFintype
  colorDecidableEq := P.colorDecidableEq
  Value := P.Value
  valueMeasurable := P.valueMeasurable
  law := P.law
  lawProbability := P.lawProbability
  Label := P.Label
  labelFintype := P.labelFintype
  support a := K₀ ∪ P.support a
  event a := S ∩ P.event a
  eventMeasurable a := hS.inter (P.eventMeasurable a)
  dependsOn a x y hxy := and_congr
    (hdepends x y (fun c hc => hxy c (Finset.mem_union_left _ hc)))
    (P.dependsOn a x y (fun c hc => hxy c (Finset.mem_union_right _ hc)))

variable (P : PatternModel.{u}) (K₀ : Finset P.Color)
    (S : Set P.Sample) (hS : MeasurableSet S)
    (hdepends : ∀ x y, (∀ c ∈ K₀, x c = y c) → (x ∈ S ↔ y ∈ S))

@[simp] theorem gateInitialEvent_measure :
    (P.gateInitialEvent K₀ S hS hdepends).measure = P.measure := rfl

@[simp] theorem gateInitialEvent_fixCoordinates (K : Finset P.Color) (x ω : P.Sample) :
    (P.gateInitialEvent K₀ S hS hdepends).fixCoordinates K x ω =
      P.fixCoordinates K x ω := rfl

@[simp] theorem gateInitialEvent_indicator (a : P.Label) (ω : P.Sample) :
    (P.gateInitialEvent K₀ S hS hdepends).indicator a ω =
      if ω ∈ S then P.indicator a ω else 0 := by
  by_cases h : ω ∈ S <;>
    simp [indicator, gateInitialEvent, Set.indicator_apply, h]

@[simp] theorem gateInitialEvent_count (ω : P.Sample) :
    (P.gateInitialEvent K₀ S hS hdepends).count ω =
      if ω ∈ S then P.count ω else 0 := by
  change (∑ label : P.Label, (P.gateInitialEvent K₀ S hS hdepends).indicator label ω) =
    if ω ∈ S then (∑ label : P.Label, P.indicator label ω) else 0
  simp_rw [P.gateInitialEvent_indicator K₀ S hS hdepends]
  by_cases hmem : ω ∈ S <;> simp [hmem]

@[simp] theorem gateInitialEvent_freshSupport (a : P.Label) :
    (P.gateInitialEvent K₀ S hS hdepends).support a \ K₀ = P.support a \ K₀ := by
  change (K₀ ∪ P.support a) \ K₀ = P.support a \ K₀
  ext c
  simp only [Finset.mem_sdiff, Finset.mem_union]
  tauto

@[simp] theorem gateInitialEvent_overlapCount (K : Finset P.Color) (ω : P.Sample) :
    (P.gateInitialEvent K₀ S hS hdepends).overlapCount K₀ K ω =
      if ω ∈ S then P.overlapCount K₀ K ω else 0 := by
  change (∑ a : P.Label, if Disjoint ((K₀ ∪ P.support a) \ K₀) K then 0 else
      (S ∩ P.event a).indicator (fun _ => (1 : ℝ)) ω) =
    if ω ∈ S then (∑ a : P.Label, if Disjoint (P.support a \ K₀) K then 0 else
      P.indicator a ω) else 0
  have hs (a : P.Label) : (K₀ ∪ P.support a) \ K₀ = P.support a \ K₀ := by
    ext c
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  simp_rw [hs]
  by_cases h : ω ∈ S <;> simp [Set.indicator_apply, indicator, h]

theorem gateInitialEvent_support_card_le (r : ℕ)
    (hr : ∀ a, (P.support a).card ≤ r) (a : P.Label) :
    ((P.gateInitialEvent K₀ S hS hdepends).support a).card ≤ K₀.card + r :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add_left (hr a) _)

include hdepends in

theorem mem_allowed_fix_union_iff (K : Finset P.Color) (x ω : P.Sample) :
    P.fixCoordinates (K₀ ∪ K) x ω ∈ S ↔ x ∈ S := by
  apply hdepends
  intro c hc
  simp [fixCoordinates, Finset.mem_union_left K hc]

@[simp] theorem gateInitialEvent_fixed_count (K : Finset P.Color) (x : P.Sample) :
    (P.gateInitialEvent K₀ S hS hdepends).fixedExpectation (K₀ ∪ K) x
      (P.gateInitialEvent K₀ S hS hdepends).count =
      if x ∈ S then P.fixedExpectation (K₀ ∪ K) x P.count else 0 := by
  change (∫ ω : P.Sample,
    (P.gateInitialEvent K₀ S hS hdepends).count (P.fixCoordinates (K₀ ∪ K) x ω)
      ∂P.measure) = _
  by_cases hx : x ∈ S
  · rw [ite_eq_left hx]
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [P.gateInitialEvent_count,
      ite_eq_left ((P.mem_allowed_fix_union_iff K₀ S hdepends K x ω).mpr hx)]
  · rw [ite_eq_right hx]
    have hz : (fun ω : P.Sample =>
        (P.gateInitialEvent K₀ S hS hdepends).count (P.fixCoordinates (K₀ ∪ K) x ω)) =
        fun _ => 0 := by
      funext ω
      rw [P.gateInitialEvent_count, ite_eq_right]
      exact fun hω => hx ((P.mem_allowed_fix_union_iff K₀ S hdepends K x ω).mp hω)
    rw [hz, integral_zero]

@[simp] theorem gateInitialEvent_fixed_overlap (K : Finset P.Color) (x : P.Sample) :
    (P.gateInitialEvent K₀ S hS hdepends).fixedExpectation (K₀ ∪ K) x
      ((P.gateInitialEvent K₀ S hS hdepends).overlapCount K₀ K) =
      if x ∈ S then P.fixedExpectation (K₀ ∪ K) x (P.overlapCount K₀ K) else 0 := by
  change (∫ ω : P.Sample,
    (P.gateInitialEvent K₀ S hS hdepends).overlapCount K₀ K
      (P.fixCoordinates (K₀ ∪ K) x ω) ∂P.measure) = _
  by_cases hx : x ∈ S
  · rw [ite_eq_left hx]
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [P.gateInitialEvent_overlapCount,
      ite_eq_left ((P.mem_allowed_fix_union_iff K₀ S hdepends K x ω).mpr hx)]
  · rw [ite_eq_right hx]
    have hz : (fun ω : P.Sample =>
        (P.gateInitialEvent K₀ S hS hdepends).overlapCount K₀ K
          (P.fixCoordinates (K₀ ∪ K) x ω)) = fun _ => 0 := by
      funext ω
      rw [P.gateInitialEvent_overlapCount, ite_eq_right]
      exact fun hω => hx ((P.mem_allowed_fix_union_iff K₀ S hdepends K x ω).mp hω)
    rw [hz, integral_zero]

theorem gateInitialEvent_total_bound (K : Finset P.Color) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ S, P.fixedExpectation (K₀ ∪ K) x P.count ≤ C) :
    ∀ x, (P.gateInitialEvent K₀ S hS hdepends).fixedExpectation (K₀ ∪ K) x
      (P.gateInitialEvent K₀ S hS hdepends).count ≤ C := by
  intro x
  refine (P.gateInitialEvent_fixed_count K₀ S hS hdepends K x).trans_le ?_
  split_ifs with hx
  · exact hbound x hx
  · exact hC

theorem gateInitialEvent_overlap_bound (K : Finset P.Color) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ S, P.fixedExpectation (K₀ ∪ K) x (P.overlapCount K₀ K) ≤ C) :
    ∀ x, (P.gateInitialEvent K₀ S hS hdepends).fixedExpectation (K₀ ∪ K) x
      ((P.gateInitialEvent K₀ S hS hdepends).overlapCount K₀ K) ≤ C := by
  intro x
  refine (P.gateInitialEvent_fixed_overlap K₀ S hS hdepends K x).trans_le ?_
  split_ifs with hx
  · exact hbound x hx
  · exact hC

end
end Balanced.PatternModel

end OAI
