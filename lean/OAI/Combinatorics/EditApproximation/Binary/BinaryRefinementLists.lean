import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalGroupActions
import OAI.Combinatorics.EditApproximation.Binary.BinaryWideGridWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Literal local scale and representative lists. Each bounded endpoint
grid is constructed before the center eligibility tests are performed. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem queryExponentsWithWork_value (N F : ℕ) (a w : BinaryFraction) :
    ((queryExponentsWithWork N F a w).1.map (fun e => 2 ^ e)) =
      dyadicQueryWindow N w.value a.value F := by
  have hscale : (List.range (max 1 N.bits.length)).map (fun e => 2 ^ e) = dyadicScales N := by
    simpa only [dyadicScalesWithWork, arithmeticMapWithWork_value, powerTwoWord_value] using
      dyadicScalesWithWork_value N
  have hguard (e : ℕ) : (refinementScaleGuardWithWork F (2 ^ e) a w).1 =
      decide (w.value / (16 * F) ≤ (2 ^ e : ℕ) ∧ ((2 ^ e : ℕ) : ℚ) ≤ 8 * a.value * w.value) :=
    Bool.eq_iff_iff.mpr (by simp only [refinementScaleGuardWithWork_value, decide_eq_true_eq])
  simp only [queryExponentsWithWork, filterWithWork_value, hguard]
  unfold dyadicQueryWindow
  rw [← hscale, List.filter_map]
  rfl

def localRepresentativesWithWork {n : ℕ} (N P F : ℕ) (a : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction) (query : TargetInterval n) :
    List (ℕ × TargetInterval n) × ℕ :=
  let scales := queryExponentsWithWork N F a (initial query)
  let radius := naturalCeilingWithWork (initial query)
  let result := arithmeticFlatMapWithWork (fun e =>
    let b := 2 ^ e
    let spacing := seedGridSpacingWithWork b P
    let points := gridStateBoxWithWork n (bitWordValue spacing.1) (bitWordValue radius.1) query.lo query.hi
    let selected := filterWithWork (fun r => centerEligibilityWithWork b F a (initial r)) points.1
    let labeled := arithmeticMapWithWork (fun r => ((b, r), 1)) selected.1
    (labeled.1, spacing.2 + points.2 + selected.2 + labeled.2 + e + 5)) scales.1
  (result.1, scales.2 + radius.2 + result.2 + 3)

@[simp] theorem localRepresentativesWithWork_value {n : ℕ} (N P F : ℕ) (hP : 0 < P)
    (a : BinaryFraction) (initial : TargetInterval n → BinaryFraction) (query : TargetInterval n) :
    (localRepresentativesWithWork N P F a initial query).1 =
      localRefinementRepresentatives N P F a.value (fun r => (initial r).value) query := by
  have hcenter (b : ℕ) (r : TargetInterval n) : (centerEligibilityWithWork b F a (initial r)).1 =
      decide ((b : ℚ) / (4 * a.value) ≤ (initial r).value ∧ (initial r).value ≤ 8 * F * b) :=
    Bool.eq_iff_iff.mpr (by simp only [centerEligibilityWithWork_value, decide_eq_true_eq])
  have hgrid (e : ℕ) : (gridStateBoxWithWork n (seedGridSpacing (2 ^ e) P)
      ⌈(initial query).value⌉₊ query.lo query.hi).1 =
      localTargetStates n (seedGridSpacing (2 ^ e) P) ⌈(initial query).value⌉₊ query := by
    rw [gridStateBoxWithWork_value _ _ _ _ _ (by unfold seedGridSpacing; omega)]
    rfl
  unfold localRepresentativesWithWork
  simp only [arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value, filterWithWork_value,
    hcenter, naturalCeilingWithWork_value, seedGridSpacingWithWork_value _ _ hP, hgrid]
  change (queryExponentsWithWork N F a (initial query)).1.flatMap
    (fun e => (((localTargetStates n (seedGridSpacing (2 ^ e) P) ⌈(initial query).value⌉₊ query).filter
      (fun r => decide (((2 ^ e : ℕ) : ℚ) / (4 * a.value) ≤ (initial r).value ∧
        (initial r).value ≤ 8 * F * (2 ^ e : ℕ)))).map (fun r => (2 ^ e, r)))) = _
  trans ((queryExponentsWithWork N F a (initial query)).1.map (fun e => 2 ^ e)).flatMap
    (fun b => ((localTargetStates n (seedGridSpacing b P) ⌈(initial query).value⌉₊ query).filter
      (fun r => decide ((b : ℚ) / (4 * a.value) ≤ (initial r).value ∧
        (initial r).value ≤ 8 * F * b))).map (fun r => (b, r)))
  · rw [List.flatMap_map]
  · rw [queryExponentsWithWork_value]
    rfl

end BinaryFraction
end EditApproximation

end OAI
