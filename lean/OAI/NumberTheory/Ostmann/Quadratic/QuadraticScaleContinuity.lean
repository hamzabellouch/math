import OAI.NumberTheory.Ostmann.Quadratic.QuadraticPhaseContinuity
import OAI.NumberTheory.Ostmann.Characters.SchwartzWeightVariation

namespace OAI

/-! # Scale continuity on a common finite quadratic cutoff -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem inv_sub_abs_le_of_one_le (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |x⁻¹ - y⁻¹| ≤ |x - y| := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have he : x⁻¹ - y⁻¹ = (y - x) / (x * y) := by field_simp
  rw [he, abs_div, abs_of_pos (mul_pos hx0 hy0), abs_sub_comm]
  exact div_le_self (abs_nonneg _) (one_le_mul_of_one_le_of_one_le hx hy)

theorem sqrt_sub_abs_le_of_one_le (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ |x - y| := by
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hsx : 1 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by simpa using hx)
  have hsy : 1 ≤ Real.sqrt y := Real.le_sqrt_of_sq_le (by simpa using hy)
  have he : (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) = x - y := by
    nlinarith only [Real.sq_sqrt hx0, Real.sq_sqrt hy0]
  have hn := congrArg abs he
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt x + Real.sqrt y)] at hn
  calc
    _ ≤ |Real.sqrt x - Real.sqrt y| * (Real.sqrt x + Real.sqrt y) :=
      le_mul_of_one_le_right (abs_nonneg _) (by linarith)
    _ = _ := hn

theorem inv_sqrt_sub_abs_le_of_one_le (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |(Real.sqrt x)⁻¹ - (Real.sqrt y)⁻¹| ≤ |x - y| := by
  have hsx : 1 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by simpa using hx)
  have hsy : 1 ≤ Real.sqrt y := Real.le_sqrt_of_sq_le (by simpa using hy)
  exact (inv_sub_abs_le_of_one_le _ _ hsx hsy).trans (sqrt_sub_abs_le_of_one_le x y hx hy)

theorem quadratic_normalizer_factor (q s : ℕ) (R v : ℝ) (hR : 0 ≤ R) :
    (Real.sqrt (R * q / ((s : ℝ) * v)))⁻¹ =
      Real.sqrt ((s : ℝ) * v / q) * (Real.sqrt R)⁻¹ := by
  have he : R * q / ((s : ℝ) * v) = R * ((q : ℝ) / ((s : ℝ) * v)) := by ring
  rw [he, Real.sqrt_mul hR, mul_inv, ← Real.sqrt_inv ((q : ℝ) / ((s : ℝ) * v)),
    inv_div, mul_comm]

theorem quadraticDensityTerm_scale_sub_bound {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (B : ℝ) (hg : ∀ x, ‖g x‖ ≤ B)
    (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R R' v : ℝ) (s w W : ℕ)
    (hR : 1 ≤ R) (hR' : 1 ≤ R') (hv : 0 ≤ v) (hw : w ≤ W) :
    ‖quadraticDensityTerm g a θ Φ R v s w - quadraticDensityTerm g a θ Φ R' v s w‖ ≤
      B * SchwartzMap.seminorm ℝ 0 1 Φ * ((s : ℝ) * v / q) * W ^ 2 * |R - R'| := by
  have hB : 0 ≤ B := (norm_nonneg (g 0)).trans (hg 0)
  have ha : 0 ≤ (s : ℝ) * v / q := by positivity
  have hd : |(s : ℝ) * v * (w : ℝ) ^ 2 / (R * q) -
      (s : ℝ) * v * (w : ℝ) ^ 2 / (R' * q)| ≤
      ((s : ℝ) * v / q) * W ^ 2 * |R - R'| := by
    have he : (s : ℝ) * v * (w : ℝ) ^ 2 / (R * q) -
        (s : ℝ) * v * (w : ℝ) ^ 2 / (R' * q) =
        (((s : ℝ) * v / q) * w ^ 2) * (R⁻¹ - R'⁻¹) := by ring
    rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((s : ℝ) * v / q) * w ^ 2)]
    have hw' : (w : ℝ) ^ 2 ≤ (W : ℝ) ^ 2 := by gcongr
    exact mul_le_mul (mul_le_mul_of_nonneg_left hw' ha)
      (inv_sub_abs_le_of_one_le R R' hR hR') (abs_nonneg _) (by positivity)
  have he : quadraticDensityTerm g a θ Φ R v s w - quadraticDensityTerm g a θ Φ R' v s w =
      (g (a * (w : ZMod q) ^ 2 * (s : ZMod q)) * realAdditivePhase (θ * v * (w : ℝ) ^ 2 / q) ^ s) *
        (Φ ((s : ℝ) * v * (w : ℝ) ^ 2 / (R * q)) - Φ ((s : ℝ) * v * (w : ℝ) ^ 2 / (R' * q))) := by
    simp only [quadraticDensityTerm]
    ring
  rw [he, norm_mul, norm_mul, norm_pow, norm_realAdditivePhase, one_pow, mul_one]
  have hs := (schwartz_norm_sub_le Φ _ _).trans (mul_le_mul_of_nonneg_left hd (by positivity))
  have hh := mul_le_mul (hg (a * (w : ZMod q) ^ 2 * (s : ZMod q))) hs (norm_nonneg _) hB
  exact hh.trans_eq (by ring)

end Ostmann

end OAI
