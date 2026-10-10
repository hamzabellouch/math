import OAI.NumberTheory.JointDickman.Amplification.RampCutoff

namespace OAI

/-! # Averaging the sharp local law to a ramp cutoff -/

namespace JointDickman

open MeasureTheory Finset

open Classical in
theorem intervalIntegrable_strict_cutoff (x a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => if t < x then (1 : ℝ) else 0) volume a b := by
  have h := (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b)
  have heq : (Set.Iio x).indicator (fun _ : ℝ => (1 : ℝ)) =
      (fun t => if t < x then (1 : ℝ) else 0) := by
    funext t
    rfl
  rw [← heq]
  exact intervalIntegrable_iff.mpr (h.def'.indicator measurableSet_Iio)

open Classical in
theorem highExclusiveCell_intervalIntegrable {C E A : Type*} [Fintype E] [DecidableEq A]
    (v : E → ℝ) (cell : C → E → Option A) (location : E → ℝ)
    (c : C) (a : A) (lo hi : ℝ) :
    IntervalIntegrable
      (fun t => highExclusiveCell v cell (fun e => location e ≤ t) c a) volume lo hi := by
  simp only [highExclusiveCell_eq_sum, not_le]
  have hs : IntervalIntegrable (∑ e : E, fun t =>
      if t < location e ∧ cell c e = some a then v e else 0) volume lo hi := by
    apply IntervalIntegrable.sum
    intro e _
    by_cases he : cell c e = some a
    · simpa only [he, and_true, mul_ite, mul_one, mul_zero] using
        (intervalIntegrable_strict_cutoff (location e) lo hi).const_mul (v e)
    · simp only [he, and_false, ↓reduceIte]
      exact intervalIntegrable_const
  convert hs using 1
  funext t
  exact (Finset.sum_apply t Finset.univ
    (fun e : E => fun s : ℝ => if s < location e ∧ cell c e = some a then v e else 0)).symm

open Classical in
/-- The linear ramp is exactly an average of sharp high cutoffs. -/
theorem rampCellMass_eq_average {C E A : Type*} [Fintype E] [DecidableEq A]
    (v : E → ℝ) (cell : C → E → Option A) (location : E → ℝ)
    (c : C) (a : A) {lo hi : ℝ} (hlohi : lo < hi) :
    optionCellMass (fun e => v e * averagingRamp lo hi (location e)) (cell c) a =
      (∫ t in lo..hi, highExclusiveCell v cell (fun e => location e ≤ t) c a) / (hi - lo) := by
  simp only [highExclusiveCell_eq_sum, not_le]
  rw [intervalIntegral.integral_finsetSum]
  · unfold optionCellMass
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : cell c e = some a
    · simp only [he, and_true, ↓reduceIte]
      rw [averagingRamp_integral hlohi]
      have heq : (fun t => if t < location e then v e else 0) =
          (fun t => v e * (if t < location e then 1 else 0)) := by funext t; split_ifs <;> simp
      rw [heq, intervalIntegral.integral_const_mul]
      ring
    · simp [he]
  · intro e _
    by_cases he : cell c e = some a
    · simpa only [he, and_true, mul_ite, mul_one, mul_zero] using
        (intervalIntegrable_strict_cutoff (location e) lo hi).const_mul (v e)
    · simp only [he, and_false, ↓reduceIte]
      exact intervalIntegrable_const

open Classical in
/-- Averaging a pointwise local error keeps the same error constant. -/
theorem rampCellMass_local_error {C E A : Type*} [Fintype E] [DecidableEq A]
    (v : E → ℝ) (cell : C → E → Option A) (location : E → ℝ)
    (c : C) (a : A) {lo hi ε : ℝ} (hlohi : lo < hi) (profile : ℝ → ℝ)
    (hprofile : IntervalIntegrable profile volume lo hi)
    (herror : ∀ t ∈ Set.Icc lo hi,
      |highExclusiveCell v cell (fun e => location e ≤ t) c a - profile t| ≤ ε) :
    |optionCellMass (fun e => v e * averagingRamp lo hi (location e)) (cell c) a -
      (∫ t in lo..hi, profile t) / (hi - lo)| ≤ ε := by
  rw [rampCellMass_eq_average v cell location c a hlohi, ← sub_div,
    ← intervalIntegral.integral_sub
      (highExclusiveCell_intervalIntegrable v cell location c a lo hi) hprofile]
  rw [abs_div, abs_of_pos (sub_pos.mpr hlohi)]
  apply (div_le_iff₀ (sub_pos.mpr hlohi)).mpr
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := lo) (b := hi) (f := fun t =>
      highExclusiveCell v cell (fun e => location e ≤ t) c a - profile t)
    (C := ε) (fun t ht => by
      rw [Real.norm_eq_abs]
      exact herror t (Set.uIcc_of_le hlohi.le ▸ Set.uIoc_subset_uIcc ht))
  simpa only [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hlohi)] using h

end JointDickman

end OAI
