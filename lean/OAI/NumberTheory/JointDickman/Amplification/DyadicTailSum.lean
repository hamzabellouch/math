import OAI.NumberTheory.JointDickman.Amplification.ChernoffParameters
import OAI.NumberTheory.JointDickman.Arithmetic.RegularityTailPrimeSums

namespace OAI

/-! # Summing the lower-tail Chernoff bounds over dyadic endpoints -/

namespace JointDickman

open Finset

theorem geometric_sum_under_cap (S : Finset ℕ) {r w : ℝ}
    (hr : 1 < r) (hw : 0 ≤ w) (hcap : ∀ i ∈ S, w * r ^ i ≤ 1) :
    (∑ i ∈ S, w * r ^ i) ≤ r / (r - 1) := by
  classical
  by_cases hS : S.Nonempty
  · let m := S.max' hS
    have hm : m ∈ S := S.max'_mem hS
    have hsub : S ⊆ range (m + 1) := by
      intro i hi
      exact mem_range.mpr (Nat.lt_succ_of_le (S.le_max' i hi))
    have hsum : (∑ i ∈ range (m + 1), w * r ^ i) * (r - 1) = w * (r ^ (m + 1) - 1) := by
      rw [← mul_sum, mul_assoc, geom_sum_mul]
    have hlast := hcap m hm
    calc
      _ ≤ ∑ i ∈ range (m + 1), w * r ^ i := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ r / (r - 1) := by
        apply (le_div_iff₀ (sub_pos.mpr hr)).mpr
        rw [hsum, pow_succ]
        have h := mul_le_mul_of_nonneg_right hlast (by linarith : 0 ≤ r)
        nlinarith
  · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    simp only [he, sum_empty]
    positivity

theorem dyadic_power_sum_bound (S : Finset ℕ) {B Y a : ℝ}
    (hB : 0 < B) (hY : 0 ≤ Y) (ha : 0 < a)
    (hcap : ∀ i ∈ S, (2 : ℝ) ^ i * Y ≤ B) :
    (∑ i ∈ S, (((2 : ℝ) ^ i * Y) / B) ^ a) ≤
      (2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1) := by
  have heq (i : ℕ) : (((2 : ℝ) ^ i * Y) / B) ^ a =
      (Y / B) ^ a * ((2 : ℝ) ^ a) ^ i := by
    rw [mul_div_assoc, Real.mul_rpow (by positivity) (div_nonneg hY hB.le),
      ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  simp_rw [heq]
  apply geometric_sum_under_cap S (Real.one_lt_rpow (by norm_num) ha) (Real.rpow_nonneg (div_nonneg hY hB.le) _)
  intro i hi
  rw [← heq]
  have hle : ((2 : ℝ) ^ i * Y) / B ≤ 1 := (div_le_one hB).mpr (hcap i hi)
  have h := Real.rpow_le_rpow (by positivity : 0 ≤ ((2 : ℝ) ^ i * Y) / B) hle ha.le
  simpa only [Real.one_rpow] using h

noncomputable def tailSaving : ℝ := (1 / 2 : ℝ) * (1 - Real.exp (-(1 / 10 : ℝ))) - (2 / 5 : ℝ) * (1 / 10)

theorem tailSaving_pos : 0 < tailSaving := tail_tilt_margin

theorem tail_chernoff_factor_bound {B Y M K C : ℝ}
    (hB : 0 < B) (hY : 0 < Y) (hM : Real.log (B / Y) - K ≤ M) :
    Real.exp ((1 / 10 : ℝ) * ((2 / 5 : ℝ) * Real.log (B / Y) - C) +
      ((Real.exp (-(1 / 10 : ℝ)) - 1) / 2) * M) ≤
    Real.exp (K * ((1 - Real.exp (-(1 / 10 : ℝ))) / 2)) *
      Real.exp (-(1 / 10 : ℝ) * C) * (Y / B) ^ tailSaving := by
  have hexp : Real.exp (-(1 / 10 : ℝ)) ≤ 1 := by
    calc
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by norm_num)
      _ = 1 := Real.exp_zero
  have hm := mul_le_mul_of_nonpos_left hM (show (Real.exp (-(1 / 10 : ℝ)) - 1) / 2 ≤ 0 by linarith)
  have hlog : Real.log (Y / B) = -Real.log (B / Y) := by
    rw [Real.log_div hY.ne' hB.ne', Real.log_div hB.ne' hY.ne']
    ring
  rw [Real.rpow_def_of_pos (div_pos hY hB), ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [hlog]
  unfold tailSaving
  nlinarith

/-- The dyadic union bound is uniform in the number of endpoints and in C. -/
theorem dyadic_tail_chernoff_sum (S : Finset ℕ) {B Y K C : ℝ}
    (hB : 0 < B) (hY : 0 < Y) (M : ℕ → ℝ)
    (hM : ∀ i ∈ S, Real.log (B / ((2 : ℝ) ^ i * Y)) - K ≤ M i)
    (hcap : ∀ i ∈ S, (2 : ℝ) ^ i * Y ≤ B) :
    (∑ i ∈ S, Real.exp ((1 / 10 : ℝ) * ((2 / 5 : ℝ) * Real.log (B / ((2 : ℝ) ^ i * Y)) - C) +
      ((Real.exp (-(1 / 10 : ℝ)) - 1) / 2) * M i)) ≤
      (Real.exp (K * ((1 - Real.exp (-(1 / 10 : ℝ))) / 2)) *
        ((2 : ℝ) ^ tailSaving / ((2 : ℝ) ^ tailSaving - 1))) * Real.exp (-(1 / 10 : ℝ) * C) := by
  calc
    _ ≤ ∑ i ∈ S, Real.exp (K * ((1 - Real.exp (-(1 / 10 : ℝ))) / 2)) *
        Real.exp (-(1 / 10 : ℝ) * C) * (((2 : ℝ) ^ i * Y) / B) ^ tailSaving :=
      sum_le_sum (fun i hi => tail_chernoff_factor_bound hB (by positivity) (hM i hi))
    _ = (Real.exp (K * ((1 - Real.exp (-(1 / 10 : ℝ))) / 2)) * Real.exp (-(1 / 10 : ℝ) * C)) *
        ∑ i ∈ S, (((2 : ℝ) ^ i * Y) / B) ^ tailSaving := by rw [mul_sum]
    _ ≤ _ := by
      have h : (Real.exp (K * ((1 - Real.exp (-(1 / 10 : ℝ))) / 2)) * Real.exp (-(1 / 10 : ℝ) * C)) *
          (∑ i ∈ S, (((2 : ℝ) ^ i * Y) / B) ^ tailSaving) ≤
          (Real.exp (K * ((1 - Real.exp (-(1 / 10 : ℝ))) / 2)) * Real.exp (-(1 / 10 : ℝ) * C)) *
          ((2 : ℝ) ^ tailSaving / ((2 : ℝ) ^ tailSaving - 1)) :=
        mul_le_mul_of_nonneg_left (dyadic_power_sum_bound S hB hY.le tailSaving_pos hcap) (by positivity)
      convert h using 1; ring

end JointDickman

end OAI
