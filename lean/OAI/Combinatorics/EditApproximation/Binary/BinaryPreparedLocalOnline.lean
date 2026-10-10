import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedOnline
import OAI.Combinatorics.EditApproximation.Binary.BinaryRefinementLists

namespace OAI

/-! One rounded center is queried at each retained dyadic scale. Both
eligibility and the complete online optimizer are charged. -/

namespace EditApproximation
namespace BinaryFraction

def preparedLocalOnlineScaleWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H e : ℕ) (hP : 0 < P)
    (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (query : TargetInterval target.length) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let b := 2 ^ e
  let spacing := seedGridSpacingWithWork b P
  let center := roundStateWithWork (bitWordValue spacing.1) (seedGridSpacingWithWork_pos b P hP) query
  let eligible := centerEligibilityWithWork b F a (parentInitial center.1)
  if eligible.1 then
    let selected := preparedOnlineWithWork source target parent P F exponent H b (Nat.two_pow_pos e) hP
      tau eta kappa child initial table t center.1 (integer b center.1)
    (selected.1, spacing.2 + center.2 + eligible.2 + selected.2 + e + 4)
  else (none, spacing.2 + center.2 + eligible.2 + e + 3)

theorem preparedLocalOnlineScaleWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H e : ℕ) (hP : 0 < P)
    (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (query : TargetInterval target.length) :
    ((preparedLocalOnlineScaleWithWork source target parent P F exponent H e hP tau a eta kappa parentInitial
      child initial table t integer query).1.map BinaryBellmanAction.decode) =
      (let b := 2 ^ e
       let r := roundInterval (seedGridSpacing b P) query
       if (b : ℚ) / (4 * a.value) ≤ (parentInitial r).value ∧
           (parentInitial r).value ≤ 8 * F * b then
         keyedOnlineCandidate source target parent P F exponent H b tau.value eta.value kappa.value
           (fun i q => (child i q).value) (fun i q => (initial i q).value)
           (fun i s q => (table s (i, q)).value) t r (integer b r)
       else none) := by
  unfold preparedLocalOnlineScaleWithWork
  simp only [roundStateWithWork_value, seedGridSpacingWithWork_value _ _ hP]
  by_cases h : (centerEligibilityWithWork (2 ^ e) F a
      (parentInitial (roundInterval (seedGridSpacing (2 ^ e) P) query))).1 = true
  · have hp := (centerEligibilityWithWork_value _ _ _ _).mp h
    rw [ite_eq_left h, ite_eq_left hp]
    exact preparedOnlineWithWork_value source target parent P F exponent H (2 ^ e) (Nat.two_pow_pos e) hP
        tau eta kappa child initial table t (roundInterval (seedGridSpacing (2 ^ e) P) query)
        (integer (2 ^ e) (roundInterval (seedGridSpacing (2 ^ e) P) query))
  · have hp : ¬ (((2 ^ e : ℕ) : ℚ) / (4 * a.value) ≤
        (parentInitial (roundInterval (seedGridSpacing (2 ^ e) P) query)).value ∧
        (parentInitial (roundInterval (seedGridSpacing (2 ^ e) P) query)).value ≤ 8 * F * (2 ^ e : ℕ)) :=
      fun hx => h ((centerEligibilityWithWork_value _ _ _ _).mpr hx)
    rw [ite_eq_right h, ite_eq_right hp]
    rfl

def preparedLocalOnlineActionsWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H : ℕ) (hP : 0 < P)
    (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (query : TargetInterval target.length) :
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let scales := queryExponentsWithWork N F a (parentInitial query)
  let selected := filterMapWithWork
    (fun e => preparedLocalOnlineScaleWithWork source target parent P F exponent H e hP tau a eta kappa
      parentInitial child initial table t integer query) scales.1
  (selected.1, scales.2 + selected.2 + 1)

theorem preparedLocalOnlineActionsWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H : ℕ) (hP : 0 < P)
    (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (query : TargetInterval target.length) :
    ((preparedLocalOnlineActionsWithWork source target parent N P F exponent H hP tau a eta kappa parentInitial
      child initial table t integer query).1.map BinaryBellmanAction.decode) =
      localOnlineCandidates source target parent N P F exponent H tau.value a.value eta.value kappa.value
        (fun r => (parentInitial r).value) (fun i r => (child i r).value)
        (fun i r => (initial i r).value) (fun i s r => (table s (i, r)).value) t integer query := by
  unfold preparedLocalOnlineActionsWithWork
  simp only [filterMapWithWork_value, List.map_filterMap]
  trans (queryExponentsWithWork N F a (parentInitial query)).1.filterMap (fun e =>
    let b := 2 ^ e
    let r := roundInterval (seedGridSpacing b P) query
    if (b : ℚ) / (4 * a.value) ≤ (parentInitial r).value ∧ (parentInitial r).value ≤ 8 * F * b then
      keyedOnlineCandidate source target parent P F exponent H b tau.value eta.value kappa.value
        (fun i q => (child i q).value) (fun i q => (initial i q).value)
        (fun i s q => (table s (i, q)).value) t r (integer b r)
    else none)
  · apply List.filterMap_congr
    intro e _
    exact preparedLocalOnlineScaleWithWork_value source target parent P F exponent H e hP tau a eta kappa
      parentInitial child initial table t integer query
  · trans ((queryExponentsWithWork N F a (parentInitial query)).1.map (fun e => 2 ^ e)).filterMap
      (fun b =>
        let r := roundInterval (seedGridSpacing b P) query
        if (b : ℚ) / (4 * a.value) ≤ (parentInitial r).value ∧ (parentInitial r).value ≤ 8 * F * b then
          keyedOnlineCandidate source target parent P F exponent H b tau.value eta.value kappa.value
            (fun i q => (child i q).value) (fun i q => (initial i q).value)
            (fun i s q => (table s (i, q)).value) t r (integer b r)
        else none)
    · rw [List.filterMap_map]
      rfl
    · rw [queryExponentsWithWork_value]
      rfl

end BinaryFraction
end EditApproximation

end OAI
