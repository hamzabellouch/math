import OAI.Combinatorics.EditApproximation.Geometry.BandGuards
import Mathlib.Data.Int.Log
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Actual dyadic child envelopes

The maximum scans the actual finite band. The dyadic ceiling uses the
computable integer upper logarithm of a positive rational, including values
below one.
-/

namespace EditApproximation

open Finset



theorem rationalMaximum_le (fallback upper : ℚ) (values : List ℚ)
    (hfallback : fallback ≤ upper) (hvalues : ∀ value ∈ values, value ≤ upper) :
    rationalMaximum fallback values ≤ upper := by
  induction values with
  | nil => exact hfallback
  | cons value rest ih =>
    exact max_le (hvalues value (by simp)) (ih (fun value hv => hvalues value (by simp [hv])))

theorem le_rationalMaximum_member (fallback : ℚ) (values : List ℚ) (value : ℚ)
    (hvalue : value ∈ values) : value ≤ rationalMaximum fallback values := by
  induction values with
  | nil => simp only [List.not_mem_nil] at hvalue
  | cons head rest ih =>
    rcases List.mem_cons.mp hvalue with rfl | hrest
    · exact le_max_left _ _
    · exact (ih hrest).trans (le_max_right _ _)



theorem rationalDyadicCeiling_bounds (value : ℚ) (hvalue : 0 < value) :
    value ≤ rationalDyadicCeiling value ∧ rationalDyadicCeiling value < 2 * value := by
  constructor
  · exact Int.self_le_zpow_clog (by decide : 1 < 2) value
  · have h := mul_lt_mul_of_pos_right
      (Int.zpow_pred_clog_lt_self (by decide : 1 < 2) hvalue) (by norm_num : (0 : ℚ) < 2)
    change (2 : ℚ) ^ (Int.clog 2 value - 1) * 2 < value * 2 at h
    have hexponent : Int.clog 2 value - 1 + 1 = Int.clog 2 value := by omega
    rw [← zpow_add_one₀ (by norm_num : (2 : ℚ) ≠ 0), hexponent] at h
    simpa only [rationalDyadicCeiling, mul_comm] using h

/-- Zero is a harmless duplicated fallback under the initial table lower
invariant. The positive b/M floor ensures that the ceiling input is positive. -/


theorem bandChildEnvelope_lower {ny M : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (i : Fin M) :
    (b : ℚ) / M ≤ bandChildEnvelope b band initial i ∧
      ∀ action ∈ band, initial i (action i) ≤ bandChildEnvelope b band initial i := by
  have hceil := Int.self_le_zpow_clog (R := ℚ) (by decide : 1 < 2)
    (max ((b : ℚ) / M) (rationalMaximum 0 (band.map fun action => initial i (action i))))
  refine ⟨(le_max_left _ _).trans hceil, ?_⟩
  intro action ha
  exact (le_rationalMaximum_member 0 _ _ (List.mem_map.mpr ⟨action, ha, rfl⟩)).trans
    ((le_max_right _ _).trans hceil)

/-- Every finite envelope is bounded using the actual computed-band
endpoint diameter and the initial table's spatial inequality. -/
theorem bandChildEnvelope_upper {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (hb : 0 < b) (hM : 0 < M)
    (tau theta velocity : ℚ) (htau : 0 < tau) (htheta : 0 ≤ theta)
    (child initial : Fin M → TargetInterval ny → ℚ)
    (comparison : Fin M → TargetInterval ny)
    (hcomparison : comparison ∈ computedBandActions parent r b P tau theta velocity child)
    (L0 : ℚ) (hL0 : 0 ≤ L0)
    (hinitial : ∀ i, 0 ≤ initial i (comparison i))
    (hspatial : ∀ i s t, initial i s ≤ initial i t + L0 * targetEndpointDistance s t)
    (i : Fin M) :
    bandChildEnvelope b (computedBandActions parent r b P tau theta velocity child) initial i ≤
      2 * ((b : ℚ) / M) + 2 * initial i (comparison i) + 8 * L0 * theta * b / M := by
  let band := computedBandActions parent r b P tau theta velocity child
  let delta : ℚ := 4 * theta * b / M
  let upper := initial i (comparison i) + L0 * delta
  have hdelta : 0 ≤ delta := by dsimp only [delta]; positivity
  have hupper : 0 ≤ upper := add_nonneg (hinitial i) (mul_nonneg hL0 hdelta)
  have hmembers : ∀ value ∈ band.map (fun action => initial i (action i)), value ≤ upper := by
    intro value hvalue
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hvalue
    have hdistReal := computedBand_child_endpoint_diameter parent r b P tau theta velocity htau htheta
      child action comparison ha hcomparison i
    have hdist : (targetEndpointDistance (action i) (comparison i) : ℚ) ≤ delta := by exact_mod_cast hdistReal
    exact (hspatial i (action i) (comparison i)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hdist hL0))
  have hmaximum := rationalMaximum_le 0 upper _ hupper hmembers
  have hfloor : (0 : ℚ) < (b : ℚ) / M := div_pos (by exact_mod_cast hb) (by exact_mod_cast hM)
  have hpositive := hfloor.trans_le (le_max_left ((b : ℚ) / M)
    (rationalMaximum 0 (band.map fun action => initial i (action i))))
  have hceil := (rationalDyadicCeiling_bounds _ hpositive).2.le
  have hmaxUpper : max ((b : ℚ) / M)
      (rationalMaximum 0 (band.map fun action => initial i (action i))) ≤ (b : ℚ) / M + upper := by
    apply max_le
    · exact le_add_of_nonneg_right hupper
    · exact hmaximum.trans (le_add_of_nonneg_left hfloor.le)
  apply hceil.trans
  have hmul := mul_le_mul_of_nonneg_left hmaxUpper (by norm_num : (0 : ℚ) ≤ 2)
  dsimp only [upper, delta] at hmul
  convert hmul using 1
  ring

/-- The actual sum guard follows from the concrete envelopes, the initial
cone bounds at the comparison child states, and their actual edit costs. -/
theorem bandChildEnvelope_sum_guard {α : Type*} (source target : List α)
    {M : ℕ} (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P : ℕ) (hb : 0 < b) (hM : 0 < M)
    (tau theta velocity : ℚ) (htau : 0 < tau) (htheta : 0 ≤ theta)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (comparison : Fin M → TargetInterval target.length)
    (hcomparison : comparison ∈ computedBandActions parent r b P tau theta velocity child)
    (L0 F : ℚ) (hL0 : 0 ≤ L0) (hF : 1 ≤ F) (hsmall : L0 * theta ≤ 1)
    (hinitial : ∀ i, 0 ≤ initial i (comparison i))
    (hspatial : ∀ i s t, initial i s ≤ initial i t + L0 * targetEndpointDistance s t)
    (hinitialUpper : ∀ i, initial i (comparison i) ≤ 2 * F * (stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i) : ℚ))
    (hcomparisonCost : (∑ i : Fin M, (stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i) : ℚ)) ≤ 4 * b) :
    (∑ i : Fin M, bandChildEnvelope b
      (computedBandActions parent r b P tau theta velocity child) initial i) ≤ 64 * F * b := by
  have hMr : (0 : ℚ) < M := by exact_mod_cast hM
  have hpoint := fun i => bandChildEnvelope_upper parent r b P hb hM tau theta velocity htau htheta
    child initial comparison hcomparison L0 hL0 hinitial hspatial i
  have hsum := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin M))) => hpoint i)
  have hequal : (∑ i : Fin M, (2 * ((b : ℚ) / M) + 2 * initial i (comparison i) +
      8 * L0 * theta * b / M)) = 2 * b + 2 * (∑ i : Fin M, initial i (comparison i)) +
        8 * L0 * theta * b := by
    rw [sum_add_distrib, sum_add_distrib, sum_const, sum_const,
      card_univ, Fintype.card_fin, ← mul_sum]
    simp only [nsmul_eq_mul]
    field_simp [hMr.ne']
  rw [hequal] at hsum
  have hinitSum := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin M))) => hinitialUpper i)
  rw [← mul_sum] at hinitSum
  have hFpos : 0 ≤ 2 * F := by linarith
  have hcost := mul_le_mul_of_nonneg_left hcomparisonCost hFpos
  have hsmallb := mul_le_mul_of_nonneg_right hsmall (show (0 : ℚ) ≤ b by positivity)
  have hFb := mul_le_mul_of_nonneg_right hF (show (0 : ℚ) ≤ b by positivity)
  nlinarith only [hsum, hinitSum, hcost, hsmallb, hFb]

end EditApproximation

end OAI
