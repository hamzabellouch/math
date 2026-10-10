import OAI.Combinatorics.EditApproximation.Geometry.AlignedStates
import OAI.Combinatorics.EditApproximation.Geometry.SharedActions
import OAI.Combinatorics.EditApproximation.Geometry.WideActions

namespace OAI

/-!
# Actual rounded comparison actions

An optimal balanced alignment at the rounded representative is rounded
on the same integer grid. This produces a shared-endpoint wide action
and the manuscript's multiplicative cost growth, with all empty children
retained as labeled coordinates.
-/

namespace EditApproximation

open Finset EditDistortion

theorem rounded_comparison_action {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (parent : TargetInterval source.length)
    (q : TargetInterval target.length) (b P : ℕ) (hP : 66 ≤ P)
    (hb : b ≤ stateEditCost (substring source parent.lo parent.hi) target q)
    (hcost : stateEditCost (substring source parent.lo parent.hi) target q < 2 * b) :
    let r := roundInterval (seedGridSpacing b P) q
    ∃ states : Fin M → TargetInterval target.length,
      states ∈ wideActionList M parent r b P ∧ endpointActionConnection r states = 0 ∧
      (∀ i j : Fin M, j.val = i.val + 1 → (states i).hi = (states j).lo) ∧
      (∀ i : Fin M,
        Nat.dist (r.lo + ((sourceChild parent i).lo - parent.lo)) (states i).lo ≤ 6 * b ∧
        Nat.dist (r.lo + ((sourceChild parent i).hi - parent.lo)) (states i).hi ≤ 6 * b) ∧
      (∑ i, (stateEditCost
        (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (states i) : ℝ)) ≤
          (1 + 4 * (M : ℝ) / P) * stateEditCost (substring source parent.lo parent.hi) target q := by
  dsimp only
  let g := seedGridSpacing b P
  let r := roundInterval g q
  let piece := fun i : Fin M =>
    substring source (sourceChild parent i).lo (sourceChild parent i).hi
  let c : ℝ := stateEditCost (substring source parent.lo parent.hi) target q
  let cr : ℝ := stateEditCost (substring source parent.lo parent.hi) target r
  have hPr : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hProne : (1 : ℝ) ≤ P := by exact_mod_cast (by omega : 1 ≤ P)
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hbc : (b : ℝ) ≤ c := by dsimp only [c]; exact_mod_cast hb
  have hcb : c < 2 * b := by dsimp only [c]; exact_mod_cast hcost
  have hqgrid : (targetEndpointDistance q r : ℝ) * P ≤ 2 * b := by
    exact_mod_cast rounded_seedGrid_error b P (by omega) q
  have hcr : cr ≤ c + targetEndpointDistance q r := by
    have h := stateEditCost_distance_abs (substring source parent.lo parent.hi) target q r
    have hR : |c - cr| ≤ (targetEndpointDistance q r : ℝ) := by
      dsimp only [c, cr]
      exact_mod_cast h
    linarith [(abs_le.mp hR).1]
  have hcrP : cr * P ≤ c * P + 2 * b := by
    have hmul := mul_le_mul_of_nonneg_right hcr hPr.le
    nlinarith
  have hqerror : (targetEndpointDistance q r : ℝ) ≤ 2 * b := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (targetEndpointDistance q r))
      (sub_nonneg.mpr hProne)]
  obtain ⟨aligned, hsplit, hstart, hend, hshared, hanchors⟩ :=
    optimal_balanced_child_states source target hM parent r
  let states := fun i => roundInterval g (aligned i)
  have herror (i : Fin M) : (targetEndpointDistance (aligned i) (states i) : ℝ) * P ≤ 2 * b := by
    exact_mod_cast rounded_seedGrid_error b P (by omega) (aligned i)
  have hanchorBound (i : Fin M) (anchor endpoint rounded : ℕ)
      (hanchor : Nat.dist anchor endpoint ≤ stateEditCost (substring source parent.lo parent.hi) target r)
      (hround : Nat.dist endpoint rounded ≤ targetEndpointDistance (aligned i) (states i)) :
      Nat.dist anchor rounded ≤ 6 * b := by
    have htriangle := Nat.dist.triangle_inequality anchor endpoint rounded
    have hbound : (Nat.dist anchor rounded : ℝ) ≤ cr +
        targetEndpointDistance (aligned i) (states i) := by
      dsimp only [cr]
      exact_mod_cast (by omega : Nat.dist anchor rounded ≤
        stateEditCost (substring source parent.lo parent.hi) target r +
          targetEndpointDistance (aligned i) (states i))
    have he := herror i
    have herr : (targetEndpointDistance (aligned i) (states i) : ℝ) ≤ 2 * b := by
      nlinarith [mul_nonneg (Nat.cast_nonneg (targetEndpointDistance (aligned i) (states i)))
        (sub_nonneg.mpr hProne)]
    have hfinal : (Nat.dist anchor rounded : ℝ) ≤ 6 * b := by linarith
    exact_mod_cast hfinal
  have hanchorsRounded (i : Fin M) :
      Nat.dist (r.lo + ((sourceChild parent i).lo - parent.lo)) (states i).lo ≤ 6 * b ∧
      Nat.dist (r.lo + ((sourceChild parent i).hi - parent.lo)) (states i).hi ≤ 6 * b := by
    constructor
    · exact hanchorBound i _ _ _ (hanchors i).1 (Nat.le_add_right _ _)
    · exact hanchorBound i _ _ _ (hanchors i).2 (Nat.le_add_left _ _)
  have hcostPoint (i : Fin M) :
      (stateEditCost (piece i) target (states i) : ℝ) * P ≤
        (stateEditCost (piece i) target (aligned i) : ℝ) * P + 2 * b := by
    have h := stateEditCost_distance_abs (piece i) target (aligned i) (states i)
    have hR : |(stateEditCost (piece i) target (aligned i) : ℝ) -
        stateEditCost (piece i) target (states i)| ≤ targetEndpointDistance (aligned i) (states i) := by
      exact_mod_cast h
    have hstep : (stateEditCost (piece i) target (states i) : ℝ) ≤
        stateEditCost (piece i) target (aligned i) + targetEndpointDistance (aligned i) (states i) := by
      linarith [(abs_le.mp hR).1]
    have hmul := mul_le_mul_of_nonneg_right hstep hPr.le
    nlinarith [herror i]
  have hsum := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin M))) => hcostPoint i)
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← sum_mul] at hsum
  have hsplitR : (∑ i, (stateEditCost (piece i) target (aligned i) : ℝ)) = cr := by
    dsimp only [piece, cr]
    exact_mod_cast hsplit
  rw [hsplitR] at hsum
  have hsumFinal : (∑ i, (stateEditCost (piece i) target (states i) : ℝ)) ≤
      (1 + 4 * (M : ℝ) / P) * c := by
    have hMb := mul_le_mul_of_nonneg_left hbc (Nat.cast_nonneg M)
    have hbM : (b : ℝ) ≤ M * (b : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hMr) (Nat.cast_nonneg b)]
    have hscaled : (∑ i, (stateEditCost (piece i) target (states i) : ℝ)) * P ≤
        (P + 4 * (M : ℝ)) * c := by nlinarith
    have hformula : ((P : ℝ) + 4 * M) * c / P = (1 + 4 * (M : ℝ) / P) * c := by
      field_simp
    rw [← hformula]
    exact (le_div_iff₀ hPr).2 hscaled
  refine ⟨states, ?_, ?_, ?_, hanchorsRounded, hsumFinal⟩
  · apply wideActionList_complete parent r states (fun i => roundInterval_on_grid g (aligned i))
    · intro i; exact (hanchorsRounded i).1.trans (by omega)
    · intro i; exact (hanchorsRounded i).2.trans (by omega)
  · exact round_shared_action hM r aligned hstart hend hshared (roundInterval_on_grid g q)
  · intro i j hij
    exact roundInterval_shared (aligned i) (aligned j) (hshared i j hij)

end EditApproximation

end OAI
