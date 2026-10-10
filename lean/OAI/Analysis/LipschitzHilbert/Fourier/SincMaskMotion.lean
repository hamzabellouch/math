import OAI.Analysis.LipschitzHilbert.Estimates.SlopeBoxMask
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! Global motion of the actual sinc-product mask.  The integral formula
handles the origin without a quotient singularity. -/

noncomputable section
open scoped Interval

namespace LipschitzHilbert

theorem sinc_eq_integral_cos (x : ℝ) :
    Real.sinc x = ∫ t in (0:ℝ)..1, Real.cos (t*x) := by
  by_cases hx : x = 0
  · simp [hx]
  rw [intervalIntegral.integral_comp_mul_right _ hx, integral_cos]
  simp [Real.sinc_of_ne_zero hx, div_eq_mul_inv, mul_comm]

/-- A global bound, including either endpoint equal to zero. -/
theorem abs_sinc_sub_sinc_le (x y : ℝ) :
    |Real.sinc x-Real.sinc y| ≤ |x-y| := by
  have hi (v : ℝ) : IntervalIntegrable (fun t : ℝ => Real.cos (t*v))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [sinc_eq_integral_cos x, sinc_eq_integral_cos y,
    ← intervalIntegral.integral_sub (hi x) (hi y)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := |x-y|)
    (f := fun t : ℝ => Real.cos (t*x)-Real.cos (t*y)) ?_
  · simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hb
  · intro t ht
    simp only [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at ht
    calc
      ‖Real.cos (t*x)-Real.cos (t*y)‖ ≤ |t*x-t*y| :=
        Real.abs_cos_sub_cos_le _ _
      _ = |t| * |x-y| := by rw [← mul_sub, abs_mul]
      _ ≤ 1 * |x-y| := mul_le_mul_of_nonneg_right
        (by rw [abs_of_pos ht.1]; exact ht.2) (abs_nonneg _)
      _ = _ := one_mul _

theorem abs_sinc_product_sub_le (x₁ y₁ x₀ y₀ : ℝ) :
    |Real.sinc x₁*Real.sinc y₁-Real.sinc x₀*Real.sinc y₀| ≤
      |x₁-x₀|+|y₁-y₀| := by
  calc
    _ = |(Real.sinc x₁-Real.sinc x₀)*Real.sinc y₁+
        Real.sinc x₀*(Real.sinc y₁-Real.sinc y₀)| := by congr 1; ring
    _ ≤ |(Real.sinc x₁-Real.sinc x₀)*Real.sinc y₁|+
        |Real.sinc x₀*(Real.sinc y₁-Real.sinc y₀)| := abs_add_le _ _
    _ = |Real.sinc x₁-Real.sinc x₀| * |Real.sinc y₁|+
        |Real.sinc x₀| * |Real.sinc y₁-Real.sinc y₀| := by rw [abs_mul, abs_mul]
    _ ≤ |x₁-x₀| * 1+1 * |y₁-y₀| := add_le_add
      (mul_le_mul (abs_sinc_sub_sinc_le _ _) (Real.abs_sinc_le_one _)
        (abs_nonneg _) (abs_nonneg _))
      (mul_le_mul (Real.abs_sinc_le_one _) (abs_sinc_sub_sinc_le _ _)
        (abs_nonneg _) zero_le_one)
    _ = _ := by ring

theorem sincProductMask_motion (n : ℕ) (x₁ y₁ x₀ y₀ : ℝ) :
    |sincProductMask n x₁ y₁-sincProductMask n x₀ y₀| ≤
      (2*(n:ℝ))*(|x₁-x₀|+|y₁-y₀|) := by
  have hprod (x y : ℝ) : |Real.sinc x*Real.sinc y| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (Real.abs_sinc_le_one x)
      (Real.abs_sinc_le_one y) (abs_nonneg _) zero_le_one
  have hm : max |Real.sinc x₁*Real.sinc y₁| |Real.sinc x₀*Real.sinc y₀| ≤ 1 :=
    max_le (hprod _ _) (hprod _ _)
  have hp : max |Real.sinc x₁*Real.sinc y₁| |Real.sinc x₀*Real.sinc y₀| ^
      (2*n-1) ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀
      (le_trans (abs_nonneg _) (le_max_left _ _)) hm (2*n-1)
  calc
    _ ≤ |Real.sinc x₁*Real.sinc y₁-Real.sinc x₀*Real.sinc y₀| * (2*n:ℕ)*
        max |Real.sinc x₁*Real.sinc y₁| |Real.sinc x₀*Real.sinc y₀|^(2*n-1) :=
      abs_pow_sub_pow_le _ _ (2*n)
    _ ≤ (|x₁-x₀|+|y₁-y₀|)*(2*n:ℕ)*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right (abs_sinc_product_sub_le _ _ _ _)
        (Nat.cast_nonneg _)) hp (by positivity) (by positivity)
    _ = _ := by push_cast; ring

theorem topSincMask_motion (L A x₁ y₁ x₀ y₀ : ℝ) (hL : 0 < L) :
    |topSincMask L A x₁ y₁-topSincMask L A x₀ y₀| ≤
      (2*(⌈L⌉₊:ℝ)/L^A)*(|x₁-x₀|+|y₁-y₀|) := by
  have h := sincProductMask_motion ⌈L⌉₊ (x₁/L^A) (y₁/L^A) (x₀/L^A) (y₀/L^A)
  rw [← sub_div, ← sub_div, abs_div, abs_div,
    abs_of_pos (Real.rpow_pos_of_pos hL A)] at h
  change |sincProductMask _ _ _-sincProductMask _ _ _| ≤ _
  convert h using 1
  ring

theorem topSincMask_motion_power (L A x₁ y₁ x₀ y₀ : ℝ) (hL : 1 ≤ L) :
    |topSincMask L A x₁ y₁-topSincMask L A x₀ y₀| ≤
      (4*L^(1-A))*(|x₁-x₀|+|y₁-y₀|) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hc : (⌈L⌉₊:ℝ) ≤ 2*L := by
    have hh := Nat.ceil_lt_add_one hL0.le
    linarith
  apply (topSincMask_motion L A x₁ y₁ x₀ y₀ hL0).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc
    2*(⌈L⌉₊:ℝ)/L^A ≤ 2*(2*L)/L^A :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = 4*L^(1-A) := by rw [Real.rpow_sub hL0, Real.rpow_one]; ring

namespace SlopeBox

/-- Motion in the two actual normalized coordinates of the top. -/
theorem mask_motion (T : SlopeBox) (L A : ℝ) (hL : 0 < L) (z₁ z₀ : ℝ × ℝ) :
    |T.mask L A z₁-T.mask L A z₀| ≤ (2*(⌈L⌉₊:ℝ)/L^A)*
      (|(z₁.1-z₀.1)/T.length|+
        |((z₁.2-z₀.2)-T.slope*(z₁.1-z₀.1))/T.width|) := by
  have hx : T.horizontal z₁-T.horizontal z₀ = (z₁.1-z₀.1)/T.length := by
    unfold horizontal
    ring
  have hy : T.transverse z₁-T.transverse z₀ =
      ((z₁.2-z₀.2)-T.slope*(z₁.1-z₀.1))/T.width := by
    unfold transverse
    ring
  simpa only [mask, hx, hy] using topSincMask_motion L A
    (T.horizontal z₁) (T.transverse z₁) (T.horizontal z₀) (T.transverse z₀) hL

theorem mask_line_motion (T : SlopeBox) (L A : ℝ) (hL : 0 < L)
    (s a : ℝ) (z : ℝ × ℝ) :
    |T.mask L A (lineShift s a z)-T.mask L A z| ≤
      (2*(⌈L⌉₊:ℝ)/L^A)*(1/T.length+|s-T.slope|/T.width)*|a| := by
  have h := T.mask_motion L A hL (lineShift s a z) z
  have hx : (lineShift s a z).1-z.1 = a := by simp [lineShift]
  have hy : (lineShift s a z).2-z.2-T.slope*((lineShift s a z).1-z.1) =
      (s-T.slope)*a := by simp [lineShift]; ring
  rw [hy, hx, abs_div, abs_div, abs_mul, abs_of_pos T.length_pos,
    abs_of_pos T.width_pos] at h
  convert h using 1
  ring

end SlopeBox
end LipschitzHilbert

end

end OAI
