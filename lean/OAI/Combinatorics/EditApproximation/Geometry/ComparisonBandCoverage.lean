import OAI.Combinatorics.EditApproximation.Geometry.RepresentativeBands
import OAI.Combinatorics.EditApproximation.Geometry.Curvature

namespace OAI

/-!
# Comparison action coverage by the computed predictor

Masses, gaps, prefix costs and curvature are those of the actual labeled
comparison action. The finite wide-action minimum supplies Z. No scalar
prefix prediction contract is assumed.
-/

namespace EditApproximation

open Finset

noncomputable def comparisonActionMass {ny M : ℕ}
    (comparison : Fin M → TargetInterval ny) (child : Fin M → TargetInterval ny → ℝ) : ℝ :=
  ∑ i, child i (comparison i)

noncomputable def comparisonActionCurvature {α : Type*} (source target : List α)
    {M : ℕ} (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (comparison : Fin M → TargetInterval target.length)
    (child : Fin M → TargetInterval target.length → ℝ) : ℝ :=
  (∑ i, (stateLengthGap
    (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i)) ^ 2 /
      child i (comparison i)) -
    (stateLengthGap (substring source parent.lo parent.hi) target r) ^ 2 /
      comparisonActionMass comparison child

theorem comparisonPrefixShift_origin {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (comparison : Fin M → TargetInterval ny)
    (hzero : endpointActionConnection r comparison = 0) :
    comparisonPrefixShift parent r comparison 0 = (r.lo : ℝ) - parent.lo := by
  have h := (zero_connection_prefix_suffix r comparison 0 hzero).1
  simp only [List.take_zero, realConnectionBudget] at h
  have heq : (connectionPrefixBoundary (List.ofFn comparison) r.hi 0 : ℝ) = r.lo :=
    (sub_eq_zero.mp (abs_eq_zero.mp h)).symm
  simp only [comparisonPrefixShift, balancedCut_zero, heq]

/-- The actual comparison prefix prediction error is at most
`sqrt(W*K) + 2*(W-Z)`. All mass, gap and finite-minimum inequalities are
derived from the genuine child table lower invariant. -/
theorem comparisonPrefixPrediction_error {α : Type*} (source target : List α)
    {M b P : ℕ} (hM : 0 < M) (parent : TargetInterval source.length)
    (r : TargetInterval target.length) (comparison : Fin M → TargetInterval target.length)
    (hcomparison : comparison ∈ wideActionList M parent r b P)
    (hnonempty : wideActionList M parent r b P ≠ [])
    (child : Fin M → TargetInterval target.length → ℝ)
    (a : ℝ) (ha : 1 ≤ a)
    (hchild : ∀ i s, max ((stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s : ℝ) / a)
        |stateLengthGap (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s| ≤
          child i s)
    (hzero : endpointActionConnection r comparison = 0)
    (hZpos : 0 < wideActionMinimum parent r b P hnonempty child)
    (j : ℕ) (hj : j ≤ M) :
    |comparisonPrefixShift parent r comparison j - ((r.lo : ℝ) - parent.lo) -
      (stateLengthGap (substring source parent.lo parent.hi) target r /
        wideActionMinimum parent r b P hnonempty child) *
        widePrefixMinimum parent r (wideActionList M parent r b P) hnonempty child j
          (comparisonPrefixShift parent r comparison j)| ≤
      Real.sqrt (comparisonActionMass comparison child *
        comparisonActionCurvature source target parent r comparison child) +
        2 * (comparisonActionMass comparison child - wideActionMinimum parent r b P hnonempty child) := by
  let mass := fun i : Fin M => child i (comparison i)
  let gap := fun i : Fin M => stateLengthGap
    (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i)
  let W := comparisonActionMass comparison child
  let Z := wideActionMinimum parent r b P hnonempty child
  let parentGap := stateLengthGap (substring source parent.lo parent.hi) target r
  let K := comparisonActionCurvature source target parent r comparison child
  let prefixMass := comparisonPrefixValue comparison child j
  let point := comparisonPrefixShift parent r comparison j
  let origin := (r.lo : ℝ) - parent.lo
  let predictor := widePrefixMinimum parent r (wideActionList M parent r b P) hnonempty child j point
  have hgap (i : Fin M) : |gap i| ≤ mass i := (le_max_right _ _).trans (hchild i (comparison i))
  have hmass (i : Fin M) : 0 ≤ mass i := (abs_nonneg _).trans (hgap i)
  have hzeroMass (i : Fin M) (hi : mass i = 0) : gap i = 0 := by
    have h := hgap i
    rw [hi] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  have hsum : (∑ i, gap i) = parentGap := zero_connection_gap_sum source target hM parent r comparison hzero
  have hZW : Z ≤ W := by
    have h := wideActionMinimum_le_member parent r hnonempty child comparison hcomparison
    simpa only [Z, W, comparisonActionMass, endpointActionValue, hzero, Nat.cast_zero, zero_add] using h
  have hZ : 0 < Z := hZpos
  have hW : 0 < W := hZ.trans_le hZW
  have hG : 0 ≤ W - Z := sub_nonneg.mpr hZW
  have hparentGap : |parentGap| ≤ Z :=
    (le_max_right _ _).trans (wideActionMinimum_lower source target hM parent r b P hnonempty a ha child hchild)
  have hvelocity : |parentGap / Z| ≤ 1 := by
    rw [abs_div, abs_of_pos hZpos]
    exact (div_le_one hZpos).2 hparentGap
  have hprediction : |parentGap / W - parentGap / Z| * W ≤ W - Z := by
    have hid : (parentGap / W - parentGap / Z) * W = -(parentGap / Z) * (W - Z) := by
      field_simp [hW.ne', hZ.ne']
      ring
    calc
      _ = |(parentGap / W - parentGap / Z) * W| := by rw [abs_mul, abs_of_pos hW]
      _ = |parentGap / Z| * (W - Z) := by rw [hid, abs_mul, abs_neg, abs_of_nonneg hG]
      _ ≤ 1 * (W - Z) := mul_le_mul_of_nonneg_right hvelocity hG
      _ = _ := one_mul _
  have hprefix : 0 ≤ prefixMass := sum_nonneg (fun i _ => by
    dsimp only [mass] at hmass
    by_cases hi : i.val < j
    · simpa only [comparisonPrefixValue, hi, ite_eq_left] using hmass i
    · simp only [hi, ↓reduceIte, le_refl])
  have hprefixTotal : prefixMass ≤ W := by
    apply sum_le_sum
    intro i hi
    by_cases hij : i.val < j
    · simp only [hij, ↓reduceIte, le_refl]
    · simpa only [hij, ↓reduceIte] using hmass i
  have hcost := comparisonPrefixMinimum_actual_bounds parent r comparison hcomparison hnonempty child j hj hzero
  have hcurvature := curvature_l1_le_sqrt univ mass gap
    (fun i _ => hmass i) (fun i _ hi => hzeroMass i hi) hW
  rw [hsum] at hcurvature
  change (∑ i, |gap i - (parentGap / W) * mass i|) ≤ Real.sqrt (W * K) at hcurvature
  have hprefixGap := comparisonPrefixShift_gap_sum source target hM parent r comparison j hj hzero
  rw [comparisonPrefixShift_origin parent r comparison hzero] at hprefixGap
  have hdecomposition : point - origin - (parentGap / W) * prefixMass =
      ∑ i, if i.val < j then gap i - (parentGap / W) * mass i else 0 := by
    rw [hprefixGap]
    simp only [prefixMass, comparisonPrefixValue]
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    by_cases hij : i.val < j <;> simp only [hij, ↓reduceIte, mul_zero, sub_zero, mass, gap]
  have hdeviation : |point - origin - (parentGap / W) * prefixMass| ≤ Real.sqrt (W * K) := by
    rw [hdecomposition]
    apply (abs_sum_le_sum_abs _ _).trans
    apply (sum_le_sum (fun i _ => ?_)).trans hcurvature
    by_cases hij : i.val < j
    · simp only [hij, ↓reduceIte, le_refl]
    · simp only [hij, ↓reduceIte, abs_zero]
      exact abs_nonneg _
  exact comparison_prefix_prediction_error hprefix hprefixTotal hprediction hvelocity
    hcost.1 hcost.2 hdeviation

/-- The derived analytic estimate places the actual comparison action in
the literal rational finite filter once its explicit numerical budget holds. -/
theorem comparison_computedBandActions_mem {α : Type*} (source target : List α)
    {M b P : ℕ} (hM : 0 < M) (parent : TargetInterval source.length)
    (r : TargetInterval target.length) (comparison : Fin M → TargetInterval target.length)
    (hcomparison : comparison ∈ wideActionList M parent r b P)
    (hnonempty : wideActionList M parent r b P ≠ [])
    (tau theta : ℚ) (child : Fin M → TargetInterval target.length → ℚ)
    (a : ℝ) (ha : 1 ≤ a)
    (hchild : ∀ i s, max ((stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s : ℝ) / a)
        |stateLengthGap (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s| ≤
          (child i s : ℝ))
    (hzero : endpointActionConnection r comparison = 0)
    (hanchors : ∀ i, Nat.dist (r.lo + ((sourceChild parent i).lo - parent.lo)) (comparison i).lo ≤ 6 * b ∧
      Nat.dist (r.lo + ((sourceChild parent i).hi - parent.lo)) (comparison i).hi ≤ 6 * b)
    (hZpos : 0 < rationalWideActionMinimum parent r b P hnonempty child)
    (hvelocity : |rationalStateGap (substring source parent.lo parent.hi) target r /
      rationalWideActionMinimum parent r b P hnonempty child| ≤ 1 - tau)
    (hnumerical : Real.sqrt (comparisonActionMass comparison (fun i s => (child i s : ℝ)) *
        comparisonActionCurvature source target parent r comparison (fun i s => (child i s : ℝ))) +
        2 * (comparisonActionMass comparison (fun i s => (child i s : ℝ)) -
          wideActionMinimum parent r b P hnonempty (fun i s => (child i s : ℝ))) ≤
        (tau : ℝ) * theta * b / M) :
    comparison ∈ computedBandActions parent r b P tau theta
      (rationalStateGap (substring source parent.lo parent.hi) target r /
        rationalWideActionMinimum parent r b P hnonempty child) child := by
  apply computedBandActions_complete parent r b P tau theta _ child comparison hnonempty hcomparison hvelocity
  refine ⟨hzero, hanchors, ?_⟩
  intro j hj
  have hZreal : 0 < wideActionMinimum parent r b P hnonempty (fun i s => (child i s : ℝ)) := by
    rw [← rationalWideActionMinimum_cast]
    exact_mod_cast hZpos
  have herror := comparisonPrefixPrediction_error source target hM parent r comparison hcomparison hnonempty
    (fun i s => (child i s : ℝ)) a ha hchild hzero hZreal j.val (Nat.le_of_lt j.isLt)
  have hbound := herror.trans hnumerical
  have hpoint : ((bandCutShift parent comparison j : ℚ) : ℝ) =
      comparisonPrefixShift parent r comparison j.val := by
    rw [comparisonPrefixShift_at_child]
    simp only [bandCutShift, Rat.cast_sub, Rat.cast_natCast]
  apply (Rat.cast_le (K := ℝ)).mp
  simp only [Rat.cast_abs, Rat.cast_sub, Rat.cast_natCast, Rat.cast_div, Rat.cast_mul,
    rationalStateGap_cast, rationalWideActionMinimum_cast, rationalWidePrefixMinimum_cast]
  rw [hpoint]
  exact hbound

/-- The representative wrapper computes precisely the velocity used in
the preceding finite-filter membership result. -/
theorem comparison_representativeBandActions_mem {α : Type*} (source target : List α)
    {M b P : ℕ} (hM : 0 < M) (parent : TargetInterval source.length)
    (r : TargetInterval target.length) (comparison : Fin M → TargetInterval target.length)
    (hcomparison : comparison ∈ wideActionList M parent r b P)
    (hnonempty : wideActionList M parent r b P ≠ [])
    (tau theta : ℚ) (child : Fin M → TargetInterval target.length → ℚ)
    (a : ℝ) (ha : 1 ≤ a)
    (hchild : ∀ i s, max ((stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s : ℝ) / a)
        |stateLengthGap (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s| ≤
          (child i s : ℝ))
    (hzero : endpointActionConnection r comparison = 0)
    (hanchors : ∀ i, Nat.dist (r.lo + ((sourceChild parent i).lo - parent.lo)) (comparison i).lo ≤ 6 * b ∧
      Nat.dist (r.lo + ((sourceChild parent i).hi - parent.lo)) (comparison i).hi ≤ 6 * b)
    (hZpos : 0 < rationalWideActionMinimum parent r b P hnonempty child)
    (hvelocity : |rationalStateGap (substring source parent.lo parent.hi) target r /
      rationalWideActionMinimum parent r b P hnonempty child| ≤ 1 - tau)
    (hnumerical : Real.sqrt (comparisonActionMass comparison (fun i s => (child i s : ℝ)) *
        comparisonActionCurvature source target parent r comparison (fun i s => (child i s : ℝ))) +
        2 * (comparisonActionMass comparison (fun i s => (child i s : ℝ)) -
          wideActionMinimum parent r b P hnonempty (fun i s => (child i s : ℝ))) ≤
        (tau : ℝ) * theta * b / M) :
    comparison ∈ representativeBandActions source target parent r b P tau theta child := by
  simp only [representativeBandActions, dite_eq_right hnonempty, ite_eq_left hZpos]
  exact comparison_computedBandActions_mem source target hM parent r comparison hcomparison hnonempty
    tau theta child a ha hchild hzero hanchors hZpos hvelocity hnumerical

end EditApproximation

end OAI
