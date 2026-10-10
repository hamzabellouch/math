import OAI.Geometry.EinsteinFour.JacobiApproximation
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OAI

/-! Uniform relative errors at the initial endpoint. These estimates let the
Jacobi approximation be used on intervals reaching zero, where the inverse
of the exact Jacobi matrix itself is unbounded. -/

namespace PositiveEinsteinFour.Jacobi

open Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Dividing the position error by time leaves an error of order one mesh
step, uniformly over every positive mesh index. -/
theorem relative_position_error {x X : E} {i : ℕ} {h C K : ℝ}
    (hi : 0 < i) (hh : 0 < h)
    (herr : ‖x - X‖ ≤ C * i * h ^ 2 * Real.exp (K * i * h)) :
    ‖((1 : ℝ) / (i * h)) • x - ((1 : ℝ) / (i * h)) • X‖ ≤
      C * h * Real.exp (K * i * h) := by
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have ht : (0 : ℝ) < i * h := mul_pos hi' hh
  calc
    _ = (1 / (i * h)) * ‖x - X‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr ht)]
    _ ≤ (1 / (i * h)) * (C * i * h ^ 2 * Real.exp (K * i * h)) :=
      mul_le_mul_of_nonneg_left herr (one_div_nonneg.mpr ht.le)
    _ = _ := by field_simp

/-- The relative approximation is close to its initial derivative even at
the first mesh point; no lower cutoff for time is needed. -/
theorem relative_position_near_initial {x X e : E} {i : ℕ} {h C K L : ℝ}
    (hi : 0 < i) (hh : 0 < h)
    (herr : ‖x - X‖ ≤ C * i * h ^ 2 * Real.exp (K * i * h))
    (hexact : ‖((1 : ℝ) / (i * h)) • X - e‖ ≤ L * (i * h)) :
    ‖((1 : ℝ) / (i * h)) • x - e‖ ≤
      C * h * Real.exp (K * i * h) + L * (i * h) := by
  exact (norm_sub_le_norm_sub_add_norm_sub _ (((1 : ℝ) / (i * h)) • X) e).trans
    (add_le_add (relative_position_error hi hh herr) hexact)

/-- The exact solution divided by time approaches its initial derivative
with a quantitative bound, directly from the differential equation. -/
theorem exact_relative_position_near_initial {X V : ℝ → E} {e : E} {t L : ℝ}
    (ht : 0 < t) (hL : 0 ≤ L) (hX0 : X 0 = 0) (hV0 : V 0 = e)
    (hX : ∀ s ∈ Set.Icc 0 t, HasDerivAt X (V s) s)
    (hV : ∀ s ∈ Set.Icc 0 t, ‖V s - e‖ ≤ L * s) :
    ‖((1 : ℝ) / t) • X t - e‖ ≤ L * t := by
  have hr : ‖X t - t • e‖ ≤ L * t ^ 2 := by
    have h := first_order_remainder ht.le hL
      (a := 0) (h := t) (f := X) (d := V)
      (by simpa only [zero_add] using hX)
      (by simpa only [zero_add, sub_zero, hV0] using hV)
    simpa only [zero_add, hX0, hV0, sub_zero] using h
  have hid : ((1 : ℝ) / t) • X t - e = ((1 : ℝ) / t) • (X t - t • e) := by
    rw [smul_sub, smul_smul, one_div_mul_cancel ht.ne', one_smul]
  calc
    _ = (1 / t) * ‖X t - t • e‖ := by
      rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr ht)]
    _ ≤ (1 / t) * (L * t ^ 2) := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by field_simp

/-- The operator-norm neighborhood used to keep the symmetric Schur pivots
positive. This lower bound also records the size of the positive margin. -/
theorem quadratic_lower_of_norm_error
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : F →L[ℝ] F) (c : ℝ) (x : F) :
    (c - ‖A - c • ContinuousLinearMap.id ℝ F‖) * ‖x‖ ^ 2 ≤ inner ℝ (A x) x := by
  let B := A - c • ContinuousLinearMap.id ℝ F
  have herr : |inner ℝ (B x) x| ≤ ‖B‖ * ‖x‖ ^ 2 := by
    calc
      _ ≤ ‖B x‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖B‖ * ‖x‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (B.le_opNorm x) (norm_nonneg x)
      _ = _ := by ring
  have hid : inner ℝ (A x) x = c * ‖x‖ ^ 2 + inner ℝ (B x) x := by
    change inner ℝ (A x) x = c * ‖x‖ ^ 2 + inner ℝ (A x - c • x) x
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  change (c - ‖B‖) * ‖x‖ ^ 2 ≤ inner ℝ (A x) x
  linarith [neg_abs_le (inner ℝ (B x) x)]

/-- Strict positivity follows without taking an inverse of a limiting
matrix. Symmetry can then be supplied separately by the Schur recurrence. -/
theorem quadratic_pos_of_norm_error
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {A : F →L[ℝ] F} {c : ℝ}
    (hA : ‖A - c • ContinuousLinearMap.id ℝ F‖ < c) {x : F} (hx : x ≠ 0) :
    0 < inner ℝ (A x) x := by
  exact lt_of_lt_of_le (mul_pos (sub_pos.mpr hA) (sq_pos_of_pos (norm_pos_iff.mpr hx)))
    (quadratic_lower_of_norm_error A c x)

end

end PositiveEinsteinFour.Jacobi

end OAI
