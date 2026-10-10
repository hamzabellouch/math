import OAI.NumberTheory.TwoPoint.Bounds.PrimeRowMomentScale

namespace OAI

/-! Polynomially many rare-site row costs are absorbed by the
stretched-exponential forbidden-site probability. -/

namespace TwoPointCorrelations

open Filter

lemma eventually_rare_row_exponent (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop,
      (2 * C + 25) * Real.log L + 2 * L ^ (9 / 10 : ℝ) ≤
        (1 / 2 : ℝ) * L ^ (199 / 200 : ℝ) := by
  have hlog := (isLittleO_log_rpow_atTop (show 0 < (199 / 200 : ℝ) by norm_num)).bound
    (show 0 < 1 / (8 * (2 * C + 26)) by positivity)
  have hpower := (tendsto_rpow_atTop (y := (19 / 200 : ℝ)) (by norm_num)).eventually
    (eventually_ge_atTop (8 : ℝ))
  filter_upwards [hlog, hpower, eventually_ge_atTop (1 : ℝ)] with L hl hp hL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hln : 0 ≤ Real.log L := Real.log_nonneg hL
  have hR : 0 ≤ L ^ (199 / 200 : ℝ) := Real.rpow_nonneg hLp.le _
  rw [Real.norm_eq_abs, abs_of_nonneg hln, Real.norm_eq_abs, abs_of_nonneg hR] at hl
  have hc : (2 * C + 25) * Real.log L ≤ (1 / 8 : ℝ) * L ^ (199 / 200 : ℝ) := by
    calc
      _ ≤ (2 * C + 26) * Real.log L := by nlinarith
      _ ≤ (2 * C + 26) * ((1 / (8 * (2 * C + 26))) * L ^ (199 / 200 : ℝ)) :=
        mul_le_mul_of_nonneg_left hl (by positivity)
      _ = _ := by field_simp
  have hh := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hLp.le (9 / 10 : ℝ))
  have he : L ^ (9 / 10 : ℝ) * L ^ (19 / 200 : ℝ) = L ^ (199 / 200 : ℝ) := by
    rw [← Real.rpow_add hLp]
    norm_num
  rw [he] at hh
  nlinarith

theorem eventually_rare_row_decay (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ A x : ℝ, 0 ≤ A → 0 ≤ x →
      A ≤ Real.exp (C * Real.log L) →
      x ^ 2 ≤ L ^ (25 : ℕ) * Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) →
      A * x ≤ Real.exp (-L ^ (9 / 10 : ℝ)) := by
  filter_upwards [eventually_rare_row_exponent C hC, eventually_ge_atTop (1 : ℝ)]
      with L hscale hL
  intro A x hA hx hAbound hxbound
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hA2 := pow_le_pow_left₀ hA hAbound 2
  have hh := mul_le_mul hA2 hxbound (sq_nonneg x)
    (sq_nonneg (Real.exp (C * Real.log L)))
  have hL25 : Real.exp ((25 : ℕ) * Real.log L) = L ^ (25 : ℕ) := by
    rw [Real.exp_nat_mul, Real.exp_log hLp]
  have he : (Real.exp (C * Real.log L)) ^ 2 *
      (L ^ (25 : ℕ) * Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ))) =
        Real.exp ((2 * C + 25) * Real.log L -
          (1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) := by
    rw [← Real.exp_nat_mul, ← hL25, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [he] at hh
  have hexp := Real.exp_le_exp.mpr
    (show (2 * C + 25) * Real.log L - (1 / 2 : ℝ) * L ^ (199 / 200 : ℝ) ≤
      -(2 * L ^ (9 / 10 : ℝ)) by linarith)
  have hsq : (A * x) ^ 2 ≤ (Real.exp (-L ^ (9 / 10 : ℝ))) ^ 2 := by
    calc
      _ = A ^ 2 * x ^ 2 := mul_pow _ _ _
      _ ≤ Real.exp ((2 * C + 25) * Real.log L -
          (1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) := hh
      _ ≤ Real.exp (-(2 * L ^ (9 / 10 : ℝ))) := hexp
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hAx : 0 ≤ A * x := mul_nonneg hA hx
  have hpos := Real.exp_pos (-L ^ (9 / 10 : ℝ))
  nlinarith

end TwoPointCorrelations

end OAI
