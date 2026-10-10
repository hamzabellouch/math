import OAI.Combinatorics.EditApproximation.Binary.BinaryBellmanKernel
import OAI.Combinatorics.EditApproximation.Geometry.RepresentativeBands
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The finite representative-band construction on stored binary fractions:
connection and child sums, the exact wide minimum, velocity, and every
literal band predicate. The Cartesian product materializes the wide-action enumeration. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

private theorem nat_distance_value (a b : ℕ) : (Nat.dist a b : ℚ) = |(a : ℚ) - b| := by
  rcases le_total a b with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]

private theorem rationalConnectionBudget_nat {n : ℕ} (start finish : ℕ)
    (states : List (TargetInterval n)) :
    rationalConnectionBudget start states finish = (connectionBudget start states finish : ℚ) := by
  induction states generalizing start with
  | nil => simp only [rationalConnectionBudget, connectionBudget, nat_distance_value]
  | cons state rest ih =>
    simp only [rationalConnectionBudget, connectionBudget, Nat.cast_add, ih, nat_distance_value]



@[simp] theorem endpointDistanceWithWork_value {n : ℕ} (q r : TargetInterval n) :
    (endpointDistanceWithWork q r).1.value = (targetEndpointDistance q r : ℚ) := by
  simp only [endpointDistanceWithWork, canonicalAddWithWork_value, distanceWithWork_value,
    nat_value, targetEndpointDistance, Nat.cast_add, nat_distance_value]



@[simp] theorem endpointConnectionWithWork_value {n M : ℕ} (r : TargetInterval n)
    (states : Fin M → TargetInterval n) :
    (endpointConnectionWithWork r states).1.value = (endpointActionConnection r states : ℚ) := by
  simp only [endpointConnectionWithWork, connectionWithWork_value, nat_value,
    rationalConnectionBudget_nat, endpointActionConnection]

def endpointScoreWithWork {n M : ℕ} (r : TargetInterval n)
    (child : Fin M → TargetInterval n → BinaryFraction) (states : Fin M → TargetInterval n) :
    BinaryFraction × ℕ :=
  let connection := endpointConnectionWithWork r states
  let children := sumListWithWork (List.ofFn fun i => child i (states i))
  let result := canonicalAddWithWork connection.1 children.1
  (result.1, connection.2 + children.2 + result.2 + 2)

@[simp] theorem endpointScoreWithWork_value {n M : ℕ} (r : TargetInterval n)
    (child : Fin M → TargetInterval n → BinaryFraction) (states : Fin M → TargetInterval n) :
    (endpointScoreWithWork r child states).1.value =
      rationalEndpointActionValue r states (fun i s => (child i s).value) := by
  simp only [endpointScoreWithWork, canonicalAddWithWork_value, endpointConnectionWithWork_value,
    sumListWithWork_value, List.map_ofFn, List.sum_ofFn, rationalEndpointActionValue, Function.comp_def]

def wideMinimumWithWork {n M : ℕ} (r : TargetInterval n)
    (child : Fin M → TargetInterval n → BinaryFraction)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ []) : BinaryFraction × ℕ :=
  let fallback := endpointScoreWithWork r child (actions.head hne)
  let scores := arithmeticMapWithWork (endpointScoreWithWork r child) actions
  let result := minimumWithWork fallback.1 scores.1
  (result.1, fallback.2 + scores.2 + result.2 + 2)

@[simp] theorem wideMinimumWithWork_value {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (child : Fin M → TargetInterval ny → BinaryFraction)
    (hne : wideActionList M parent r b P ≠ []) :
    (wideMinimumWithWork r child (wideActionList M parent r b P) hne).1.value =
      rationalWideActionMinimum parent r b P hne (fun i s => (child i s).value) := by
  simp only [wideMinimumWithWork, minimumWithWork_value, arithmeticMapWithWork_value,
    List.map_map, Function.comp_def, endpointScoreWithWork_value, rationalWideActionMinimum]



@[simp] theorem stateGapWithWork_value {n : ℕ} (sourceLength : ℕ) (r : TargetInterval n) :
    (stateGapWithWork sourceLength r).1.value = (r.hi : ℚ) - r.lo - sourceLength := by
  simp only [stateGapWithWork, subWithWork_value, nat_value]

/-- Every filter callback is the literal binary band predicate. -/
def bandFromActionsWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b : ℕ) (tau theta velocity : BinaryFraction)
    (child : Fin M → TargetInterval ny → BinaryFraction)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ []) :
    List (Fin M → TargetInterval ny) × ℕ :=
  let margin := subWithWork one tau
  let guard := leWithWork velocity.absolute margin.1
  if guard.1 then
    let filtered := filterWithWork
      (bandPredicateWithWork parent r b tau theta velocity actions hne child) actions
    (filtered.1, margin.2 + guard.2 + filtered.2 + 2)
  else ([], margin.2 + guard.2 + 1)

@[simp] theorem bandFromActionsWithWork_value {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b : ℕ) (tau theta velocity : BinaryFraction)
    (child : Fin M → TargetInterval ny → BinaryFraction)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ []) :
    (bandFromActionsWithWork parent r b tau theta velocity child actions hne).1 =
      if |velocity.value| ≤ 1 - tau.value then
        actions.filter (fun states => decide (bandActionPredicate parent r b tau.value theta.value
          velocity.value actions hne (fun i s => (child i s).value) states)) else [] := by
  have hguard : (leWithWork velocity.absolute (subWithWork one tau).1).1 = true ↔
      |velocity.value| ≤ 1 - tau.value := by
    simp only [leWithWork_value, absolute_value, subWithWork_value, one, nat_value, Nat.cast_one]
  unfold bandFromActionsWithWork
  dsimp only
  by_cases h : |velocity.value| ≤ 1 - tau.value
  · rw [ite_eq_left (hguard.mpr h), ite_eq_left h, filterWithWork_value]
    apply List.filter_congr
    intro states _
    apply Bool.eq_iff_iff.mpr
    exact (bandPredicateWithWork_value parent r b tau theta velocity actions hne child states).trans
      decide_eq_true_iff.symm
  · rw [ite_eq_right (fun hg => h (hguard.mp hg)), ite_eq_right h]

/-- The actions have been materialized once and are reused for the wide
minimum and all prefix queries. -/
def representativeFromActionsWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (sourceLength b : ℕ) (tau theta : BinaryFraction)
    (child : Fin M → TargetInterval ny → BinaryFraction)
    (actions : List (Fin M → TargetInterval ny)) : List (Fin M → TargetInterval ny) × ℕ :=
  if hne : actions = [] then ([], 1) else
    let Z := wideMinimumWithWork r child actions hne
    let positive := ltWithWork zero Z.1
    if positive.1 then
      let gap := stateGapWithWork sourceLength r
      let velocity := divWithWork gap.1 Z.1
      let result := bandFromActionsWithWork parent r b tau theta velocity.1 child actions hne
      (result.1, Z.2 + positive.2 + gap.2 + velocity.2 + result.2 + 3)
    else ([], Z.2 + positive.2 + 2)

/-- Full stored-data representative construction, including the Cartesian
product and all subsequent numerical work. -/
def representativeBandWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (sourceLength b P : ℕ) (tau theta : BinaryFraction)
    (child : Fin M → TargetInterval ny → BinaryFraction) : List (Fin M → TargetInterval ny) × ℕ :=
  let wide := materializedWideActionsWithWork M parent r b P
  let result := representativeFromActionsWithWork parent r sourceLength b tau theta child (wide.1.map Vector.get)
  (result.1, wide.2 + result.2 + wide.1.length + 1)

theorem representativeFromActionsWithWork_value {α : Type*} (source target : List α)
    {M : ℕ} (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P : ℕ) (tau theta : BinaryFraction) (child : Fin M → TargetInterval target.length → BinaryFraction) :
    (representativeFromActionsWithWork parent r (parent.hi - parent.lo) b tau theta child
      (wideActionList M parent r b P)).1 =
      representativeBandActions source target parent r b P tau.value theta.value
        (fun i s => (child i s).value) := by
  have hgap : (stateGapWithWork (parent.hi - parent.lo) r).1.value =
      rationalStateGap (substring source parent.lo parent.hi) target r := by
    rw [stateGapWithWork_value, rationalStateGap, substring_length source parent.lo parent.hi parent.valid]
  by_cases hne : wideActionList M parent r b P = []
  · simp only [representativeFromActionsWithWork, representativeBandActions, dite_eq_left hne]
  · have hz := wideMinimumWithWork_value parent r b P child hne
    have hzero : zero.value = 0 := by
      rw [← representation_value, zero_representation, UnreducedRational.value_zero]
    have hpositive : (ltWithWork zero (wideMinimumWithWork r child
        (wideActionList M parent r b P) hne).1).1 = true ↔
        0 < rationalWideActionMinimum parent r b P hne (fun i s => (child i s).value) := by
      rw [ltWithWork_value, hz, hzero]
    simp only [representativeFromActionsWithWork, representativeBandActions, dite_eq_right hne]
    by_cases hp : 0 < rationalWideActionMinimum parent r b P hne (fun i s => (child i s).value)
    · rw [ite_eq_left (hpositive.mpr hp), ite_eq_left hp]
      dsimp only
      rw [bandFromActionsWithWork_value]
      simp only [divWithWork_value, hgap, hz, computedBandActions, dite_eq_right hne]
    · rw [ite_eq_right (fun h => hp (hpositive.mp h)), ite_eq_right hp]

theorem representativeBandWithWork_value {α : Type*} (source target : List α)
    {M : ℕ} (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P : ℕ) (tau theta : BinaryFraction) (child : Fin M → TargetInterval target.length → BinaryFraction) :
    (representativeBandWithWork parent r (parent.hi - parent.lo) b P tau theta child).1 =
      representativeBandActions source target parent r b P tau.value theta.value
        (fun i s => (child i s).value) := by
  simp only [representativeBandWithWork, materializedWideActionsWithWork_value]
  exact representativeFromActionsWithWork_value source target parent r b P tau theta child

end BinaryFraction
end EditApproximation

end OAI
