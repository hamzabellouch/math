import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparseContourScale
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Elementary abscissa and height choices for the sparse-prime contour.
The estimates are uniform in the positive cutoff, including arbitrarily
large cutoffs. -/

namespace TwoPointCorrelations

open Filter
open scoped Topology

lemma mrt_sparse_right_abscissa {x : ℝ} (hx : 8 ≤ x) :
    1 < 1 + 1 / Real.log x ∧ 1 + 1 / Real.log x ≤ 2 ∧
      x ^ (1 + 1 / Real.log x) = Real.exp 1 * x := by
  have hx0 : 0 < x := by linarith
  have hlog : 1 ≤ Real.log x := by
    apply (Real.le_log_iff_exp_le hx0).mpr
    linarith [Real.exp_one_lt_d9]
  have hl0 : 0 < Real.log x := by linarith
  refine ⟨by have hp := one_div_pos.mpr hl0; linarith, ?_, ?_⟩
  · have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hlog
    norm_num at hh
    rw [one_div]
    linarith
  · rw [Real.rpow_def_of_pos hx0]
    have he : Real.log x * (1 + 1 / Real.log x) = 1 + Real.log x := by
      field_simp
      ring
    rw [he, Real.exp_add, Real.exp_log hx0]

lemma mrt_sparse_left_power {L Y : ℝ} (hL : 0 < L) (hY : 2 ≤ Y) :
    (4 * Y) ^ (1 - L ^ (-(3 / 4 : ℝ))) ≤
      4 * Y * Real.exp (-Real.log Y / L ^ (3 / 4 : ℝ)) := by
  have hY0 : 0 < Y := by linarith
  have hx0 : 0 < 4 * Y := by positivity
  have hlogs : Real.log Y ≤ Real.log (4 * Y) :=
    Real.log_le_log hY0 (by linarith)
  rw [Real.rpow_def_of_pos hx0]
  have he : Real.log (4 * Y) * (1 - L ^ (-(3 / 4 : ℝ))) =
      Real.log (4 * Y) - L ^ (-(3 / 4 : ℝ)) * Real.log (4 * Y) := by ring
  rw [he, Real.exp_sub, Real.exp_log hx0]
  rw [div_eq_mul_inv, ← Real.exp_neg]
  apply mul_le_mul_of_nonneg_left _ hx0.le
  apply Real.exp_le_exp.mpr
  rw [Real.rpow_neg hL.le]
  have hp := mul_le_mul_of_nonneg_left hlogs
    (inv_nonneg.mpr (Real.rpow_nonneg hL.le (3 / 4 : ℝ)))
  simp only [div_eq_mul_inv] at hp ⊢
  nlinarith only [hp]

lemma mrt_sparse_height_choices (T₀ : ℝ) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ L ^ (-(3 / 4 : ℝ)) ≤ 1 / 2 ∧
      T₀ ≤ Real.exp (2 * L) ∧ 2 * Real.exp L ≤ Real.exp (2 * L) / 2 ∧
      (5 * Real.exp (2 * L)) * (Real.exp (2 * L)) ^ (-(3 / 2 : ℝ)) ≤ 1 ∧
      (5 * Real.exp (2 * L)) * L ^ 2 / (Real.exp (2 * L)) ^ 3 ≤ 1 := by
  have hd := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 3 / 4 by norm_num)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have he := (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop
    (by norm_num : (0 : ℝ) < 2))).eventually (eventually_ge_atTop T₀)
  have hp := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    2 4 (by norm_num)).const_mul 5
  simp only [mul_zero] at hp
  filter_upwards [hd, he, hp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (Real.log 5)] with L hd he hp hL hL5
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hE : 5 ≤ Real.exp L := (Real.log_le_iff_le_exp (by norm_num)).mp hL5
  have hprod : Real.exp (2 * L) = Real.exp L * Real.exp L := by
    rw [show 2 * L = L + L by ring, Real.exp_add]
  refine ⟨hL, hd.le, he, ?_, ?_, ?_⟩
  · rw [hprod]
    nlinarith [Real.exp_pos L]
  · rw [← Real.exp_mul, show 2 * L * (-(3 / 2 : ℝ)) = -3 * L by ring]
    rw [show 5 * Real.exp (2 * L) * Real.exp (-3 * L) =
      5 * Real.exp (-L) by rw [mul_assoc, ← Real.exp_add]; congr 2; ring]
    rw [Real.exp_neg]
    exact (div_le_one (Real.exp_pos L)).mpr hE
  · have hid : 5 * Real.exp (2 * L) * L ^ 2 / Real.exp (2 * L) ^ 3 =
        5 * (L ^ (2 : ℝ) * Real.exp (-4 * L)) := by
      rw [Real.rpow_two, ← Real.exp_nat_mul, div_eq_mul_inv, ← Real.exp_neg]
      norm_num only [Nat.cast_ofNat]
      rw [show 5 * Real.exp (2 * L) * L ^ 2 * Real.exp (-(3 * (2 * L))) =
        5 * L ^ 2 * (Real.exp (2 * L) * Real.exp (-(3 * (2 * L)))) by ring,
        ← Real.exp_add]
      rw [show 2 * L + -(3 * (2 * L)) = -4 * L by ring]
      ring
    rw [hid]
    exact hp.le

lemma mrt_sparse_frequency_height {L u : ℝ} (hL : 0 ≤ L)
    (hu : |u| ≤ 2 * Real.exp L) : 1 + u ^ 2 ≤ 5 * Real.exp (2 * L) := by
  have hE : 1 ≤ Real.exp (2 * L) := Real.one_le_exp_iff.mpr (by linarith)
  have hh : u ^ 2 ≤ 4 * Real.exp (2 * L) := by
    have hs := sq_le_sq₀ (abs_nonneg u) (by positivity : 0 ≤ 2 * Real.exp L)
    have hp := hs.mpr hu
    rw [sq_abs, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num,
      ← Real.exp_nat_mul] at hp
    simpa only [Nat.cast_ofNat] using hp
  linarith

end TwoPointCorrelations

end OAI
