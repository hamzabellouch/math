import OAI.NumberTheory.JointDickman.Analysis.MellinShortComparison
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

/-! # Exact logarithmic reparametrization of a short interval -/
namespace JointDickman
open Finset PublishedInputs

noncomputable def logarithmicWindowAverage (f : ArithmeticFunction ℂ) (δ v : ℝ) : ℂ :=
  (∑ n ∈ Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + δ)⌋₊,
    f n / (n : ℂ)) / (δ : ℂ)

theorem logarithmic_window_width {x H : ℝ} (hx : 0 < x) (hH : 0 < H) :
    0 < Real.log ((x + H) / x) ∧
      H / (x + H) ≤ Real.log ((x + H) / x) ∧
      Real.log ((x + H) / x) ≤ H / x := by
  have hsum : 0 < x + H := by positivity
  have hr : 0 < (x + H) / x := div_pos hsum hx
  have hr1 : 1 < (x + H) / x := (lt_div_iff₀ hx).mpr (by linarith)
  refine ⟨Real.log_pos hr1, ?_, ?_⟩
  · calc
      H / (x + H) = 1 - ((x + H) / x)⁻¹ := by field_simp [hx.ne', hsum.ne']; ring
      _ ≤ _ := Real.one_sub_inv_le_log_of_pos hr
  · calc
      _ ≤ (x + H) / x - 1 := Real.log_le_sub_one_of_pos hr
      _ = H / x := by field_simp [hx.ne']; ring

/-- The logarithmic interval has exactly the original arithmetic endpoints. -/
theorem logarithmicWindowAverage_endpoints (f : ArithmeticFunction ℂ)
    {x H : ℝ} (hx : 0 < x) (hH : 0 < H) :
    logarithmicWindowAverage f (Real.log ((x + H) / x)) (Real.log x) =
      (∑ n ∈ Ioc ⌊x⌋₊ ⌊x + H⌋₊, f n / (n : ℂ)) /
        (Real.log ((x + H) / x) : ℂ) := by
  have hsum : 0 < x + H := by positivity
  have he : Real.log x + Real.log ((x + H) / x) = Real.log (x + H) := by
    rw [Real.log_div hsum.ne' hx.ne']
    ring
  simp only [logarithmicWindowAverage, he, Real.exp_log hx, Real.exp_log hsum]

/-- Before normalization, the reciprocal short average is the exact
logarithmic-window sum, with no endpoint error. -/
theorem reciprocalShortAverage_eq_logarithmic (f : ArithmeticFunction ℂ)
    {x H : ℝ} (hx : 0 < x) (hH : 0 < H) :
    reciprocalShortAverage f H x =
      ((x * Real.log ((x + H) / x) / H : ℝ) : ℂ) *
        logarithmicWindowAverage f (Real.log ((x + H) / x)) (Real.log x) := by
  rw [logarithmicWindowAverage_endpoints f hx hH]
  have hδ := (logarithmic_window_width hx hH).1
  unfold reciprocalShortAverage
  push_cast
  field_simp [show (Real.log ((x + H) / x) : ℂ) ≠ 0 by exact_mod_cast hδ.ne',
    show (H : ℂ) ≠ 0 by exact_mod_cast hH.ne']

/-- A hard short average is bounded by its normalized logarithmic window
plus the uniform endpoint-scale error. -/
theorem norm_shortAverage_le_logarithmic (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {x H : ℝ} (hx : 0 < x) (hH : 0 < H) :
    ‖complexShortAverage f H x‖ ≤
      ‖logarithmicWindowAverage f (Real.log ((x + H) / x)) (Real.log x)‖ +
        (H + 1) / x := by
  have hδ := logarithmic_window_width hx hH
  have hfactor0 : 0 ≤ x * Real.log ((x + H) / x) / H :=
    div_nonneg (mul_nonneg hx.le hδ.1.le) hH.le
  have hfactor1 : x * Real.log ((x + H) / x) / H ≤ 1 := by
    apply (div_le_one hH).mpr
    have ht := mul_le_mul_of_nonneg_left hδ.2.2 hx.le
    simpa only [mul_div_cancel₀ _ hx.ne'] using ht
  have hrecip : ‖reciprocalShortAverage f H x‖ ≤
      ‖logarithmicWindowAverage f (Real.log ((x + H) / x)) (Real.log x)‖ := by
    rw [reciprocalShortAverage_eq_logarithmic f hx hH, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfactor0]
    exact mul_le_of_le_one_left (norm_nonneg _) hfactor1
  calc
    _ = ‖(complexShortAverage f H x - reciprocalShortAverage f H x) +
        reciprocalShortAverage f H x‖ := by rw [sub_add_cancel]
    _ ≤ ‖complexShortAverage f H x - reciprocalShortAverage f H x‖ +
        ‖reciprocalShortAverage f H x‖ := norm_add_le _ _
    _ ≤ (H + 1) / x +
        ‖logarithmicWindowAverage f (Real.log ((x + H) / x)) (Real.log x)‖ :=
      add_le_add (short_average_reciprocal_error f hf hx hH) hrecip
    _ = _ := add_comm _ _

theorem shortAverage_sq_le_logarithmic (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {x H : ℝ} (hx : 0 < x) (hH : 0 < H) :
    ‖complexShortAverage f H x‖ ^ 2 ≤
      2 * ‖logarithmicWindowAverage f (Real.log ((x + H) / x)) (Real.log x)‖ ^ 2 +
        2 * ((H + 1) / x) ^ 2 := by
  have hb := norm_shortAverage_le_logarithmic f hf hx hH
  have hn := norm_nonneg (complexShortAverage f H x)
  have hl := norm_nonneg
    (logarithmicWindowAverage f (Real.log ((x + H) / x)) (Real.log x))
  have he : 0 ≤ (H + 1) / x := by positivity
  nlinarith [sq_nonneg (‖logarithmicWindowAverage f (Real.log ((x + H) / x))
    (Real.log x)‖ - (H + 1) / x)]

end JointDickman

end OAI
