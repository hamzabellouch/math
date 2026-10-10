import OAI.Combinatorics.EditApproximation.Geometry.ComparisonBandCoverage
import OAI.Combinatorics.EditApproximation.Geometry.BandParameters

namespace OAI

/-! The comparison band uses the computed numerical parameters, with its error budget proved. -/

namespace EditApproximation

open Finset

theorem comparisonActionCurvature_nonneg {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (parent : TargetInterval source.length)
    (r : TargetInterval target.length) (comparison : Fin M → TargetInterval target.length)
    (child : Fin M → TargetInterval target.length → ℝ)
    (hgap : ∀ i, |stateLengthGap
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i)| ≤
        child i (comparison i))
    (hzero : endpointActionConnection r comparison = 0)
    (hW : 0 < comparisonActionMass comparison child) :
    0 ≤ comparisonActionCurvature source target parent r comparison child := by
  let mass := fun i => child i (comparison i)
  let gap := fun i => stateLengthGap
    (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i)
  have hmass (i : Fin M) : 0 ≤ mass i := (abs_nonneg _).trans (hgap i)
  have hzeroMass (i : Fin M) (hi : mass i = 0) : gap i = 0 := by
    have h := hgap i
    change |gap i| ≤ mass i at h
    rw [hi] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  have hsum := zero_connection_gap_sum source target hM parent r comparison hzero
  have h := curvature_nonneg univ mass gap (fun i _ => hmass i) (fun i _ => hzeroMass i) hW
  dsimp only [mass, gap] at h
  rw [hsum] at h
  exact h

theorem computed_comparison_band_mem {α : Type*} (source target : List α)
    (N : ℕ) (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
    {M b P : ℕ} (hM : 0 < M) (hMeq : M = (integerParameters N).M)
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (comparison : Fin M → TargetInterval target.length)
    (hcomparison : comparison ∈ wideActionList M parent r b P)
    (hnonempty : wideActionList M parent r b P ≠ [])
    (child : Fin M → TargetInterval target.length → ℚ) (a : ℝ) (ha : 1 ≤ a)
    (hchild : ∀ i s, max ((stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s : ℝ) / a)
        |stateLengthGap (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s| ≤
          (child i s : ℝ))
    (hupper : ∀ i, (child i (comparison i) : ℝ) ≤ 2 * inputSmallLog N * stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i))
    (hcostSum : (∑ i, (stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i) : ℝ)) ≤ 4 * b)
    (hpositive : 0 < stateEditCost (substring source parent.lo parent.hi) target r)
    (hzero : endpointActionConnection r comparison = 0)
    (hanchors : ∀ i, Nat.dist (r.lo + ((sourceChild parent i).lo - parent.lo)) (comparison i).lo ≤ 6 * b ∧
      Nat.dist (r.lo + ((sourceChild parent i).hi - parent.lo)) (comparison i).hi ≤ 6 * b)
    (hvelocity : |rationalStateGap (substring source parent.lo parent.hi) target r /
      rationalWideActionMinimum parent r b P hnonempty child| ≤
        1 - (rationalParameters (inputSmallLog N)).tau)
    (hKsmall : comparisonActionCurvature source target parent r comparison (fun i s => (child i s : ℝ)) ≤
      b / heightQuarterRoot N)
    (hGsmall : comparisonActionMass comparison (fun i s => (child i s : ℝ)) -
      wideActionMinimum parent r b P hnonempty (fun i s => (child i s : ℝ)) ≤ b / heightQuarterRoot N) :
    comparison ∈ representativeBandActions source target parent r b P
      (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).theta child := by
  let childR := fun i s => (child i s : ℝ)
  let W := comparisonActionMass comparison childR
  let Z := wideActionMinimum parent r b P hnonempty childR
  let K := comparisonActionCurvature source target parent r comparison childR
  have hgap (i : Fin M) : |stateLengthGap
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i)| ≤
        childR i (comparison i) := (le_max_right _ _).trans (hchild i (comparison i))
  have hZlower : (stateEditCost (substring source parent.lo parent.hi) target r : ℝ) / a ≤ Z :=
    (le_max_left _ _).trans (wideActionMinimum_lower source target hM parent r b P hnonempty a ha childR hchild)
  have hcpos : (0 : ℝ) < stateEditCost (substring source parent.lo parent.hi) target r := by exact_mod_cast hpositive
  have hZpos : 0 < Z := (div_pos hcpos (by linarith only [ha] : 0 < a)).trans_le hZlower
  have hZposQ : 0 < rationalWideActionMinimum parent r b P hnonempty child := by
    have h := hZpos
    change 0 < wideActionMinimum parent r b P hnonempty childR at h
    rw [← rationalWideActionMinimum_cast] at h
    exact_mod_cast h
  have hZW : Z ≤ W := by
    have h := wideActionMinimum_le_member parent r hnonempty childR comparison hcomparison
    simpa only [Z, W, comparisonActionMass, endpointActionValue, hzero, Nat.cast_zero, zero_add] using h
  have hWpos : 0 < W := hZpos.trans_le hZW
  have hK : 0 ≤ K := comparisonActionCurvature_nonneg source target hM parent r comparison childR hgap hzero hWpos
  have hG : 0 ≤ W - Z := sub_nonneg.mpr hZW
  have hWupper : W ≤ 8 * inputSmallLog N * b := by
    calc
      W = ∑ i, childR i (comparison i) := rfl
      _ ≤ ∑ i, 2 * (inputSmallLog N : ℝ) * stateEditCost
          (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i) :=
        sum_le_sum fun i _ => hupper i
      _ = 2 * (inputSmallLog N : ℝ) * ∑ i, (stateEditCost
          (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i) : ℝ) := by rw [mul_sum]
      _ ≤ 2 * (inputSmallLog N : ℝ) * (4 * b) :=
        mul_le_mul_of_nonneg_left hcostSum (by positivity)
      _ = 8 * inputSmallLog N * b := by ring
  have hnumerical := computed_nonbad_band_numerical_bound N hN hell (Nat.cast_nonneg b)
    hK hG hWpos.le hKsmall hGsmall hWupper
  rw [← hMeq] at hnumerical
  apply comparison_representativeBandActions_mem source target hM parent r comparison hcomparison hnonempty
    (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).theta child
    a ha hchild hzero hanchors hZposQ hvelocity
  simpa only [mul_comm, W, Z, K, childR] using hnumerical

end EditApproximation

end OAI
