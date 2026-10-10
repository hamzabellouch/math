import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingWeightAddition

namespace OAI

/-! # One physical derivative costs one high-frequency Sobolev order uniformly in radius -/

namespace DefocusingNLS

private theorem derivative_density_bound (a k L x : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hk : 8 < k) (hL : 1 ≤ L) (hx : 0 ≤ x) :
    ((L ^ (-2 : ℝ) + x ^ 2) ^ (6 - a) + x ^ (2 * k)) * x ^ 2 ≤
      (2 ^ (6 - a) + 1) ^ 2 *
        ((L ^ (-2 : ℝ) + x ^ 2) ^ (6 - a) + x ^ (2 * (k + 1))) := by
  by_cases hz : x = 0
  · subst x
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, mul_zero]
    positivity
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
  have hp (s : ℝ) : x ^ (2 * s) * x ^ 2 = x ^ (2 * (s + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hxp]
    congr 1
    ring
  let A := (L ^ (-2 : ℝ) + x ^ 2) ^ (6 - a)
  let H := x ^ (2 * (k + 1))
  let C : ℝ := 2 ^ (6 - a) + 1
  have hA : 0 ≤ A := Real.rpow_nonneg (by positivity) _
  have hH : 0 ≤ H := Real.rpow_nonneg hx _
  have hC : 1 ≤ C := le_add_of_nonneg_left (by positivity)
  have hlow : A * x ^ 2 ≤ C * (A + H) - H := by
    by_cases hx1 : x ≤ 1
    · have hx2 : x ^ 2 ≤ 1 := by nlinarith
      have hl := mul_le_mul_of_nonneg_left hx2 hA
      have he : 0 ≤ (C - 1) * (A + H) := mul_nonneg (by linarith) (add_nonneg hA hH)
      nlinarith
    · have hx1' : 1 ≤ x := le_of_lt (lt_of_not_ge hx1)
      have hLpow : L ^ (-2 : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hL (by norm_num)
      have hbase : L ^ (-2 : ℝ) + x ^ 2 ≤ 2 * x ^ 2 := by nlinarith
      have hAp : A ≤ 2 ^ (6 - a) * x ^ (2 * (6 - a)) := by
        calc
          A ≤ (2 * x ^ 2) ^ (6 - a) := Real.rpow_le_rpow (by positivity) hbase (by linarith)
          _ = _ := by
            rw [Real.mul_rpow (by norm_num) (sq_nonneg x),
              ← Real.rpow_natCast, ← Real.rpow_mul hx]
            norm_num
      have he : x ^ (2 * (6 - a)) * x ^ 2 ≤ H := by
        rw [hp]
        exact Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
      have hb : A * x ^ 2 ≤ 2 ^ (6 - a) * H := by
        calc
          _ ≤ (2 ^ (6 - a) * x ^ (2 * (6 - a))) * x ^ 2 :=
            mul_le_mul_of_nonneg_right hAp (sq_nonneg x)
          _ = 2 ^ (6 - a) * (x ^ (2 * (6 - a)) * x ^ 2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)
      have hh : 0 ≤ C * A := mul_nonneg (by linarith) hA
      dsimp [C] at *
      nlinarith
  have hCsq : C ≤ C ^ 2 := by nlinarith
  calc
    _ = A * x ^ 2 + H := by rw [add_mul, hp]
    _ ≤ C * (A + H) := by linarith
    _ ≤ C ^ 2 * (A + H) := mul_le_mul_of_nonneg_right hCsq (add_nonneg hA hH)
    _ = _ := rfl

theorem expandingSobolevWeight_derivative_le (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hk : 8 < k) (hL : 1 ≤ L) (n : frequencyLattice) :
    expandingSobolevWeight a k L n * (‖n‖ / L) ≤
      (2 ^ (6 - a) + 1) * expandingSobolevWeight a (k + 1) L n := by
  have hLp : 0 < L := by linarith
  have hb := mul_le_mul_of_nonneg_left
    (derivative_density_bound a k L (‖n‖ / L) ha ha1 hk hL (by positivity))
    (show 0 ≤ (2 * Real.pi * L) ^ (12 : ℕ) by positivity)
  have hw (j : ℝ) : expandingSobolevWeight a j L n ^ 2 =
      (2 * Real.pi * L) ^ (12 : ℕ) *
        ((L ^ (-2 : ℝ) + (‖n‖ / L) ^ 2) ^ (6 - a) + (‖n‖ / L) ^ (2 * j)) := by
    rw [expandingSobolevWeight_sq a j L hL, expandingSobolevWeightSq_original a j L hL]
  have hs : (expandingSobolevWeight a k L n * (‖n‖ / L)) ^ 2 ≤
      ((2 ^ (6 - a) + 1) * expandingSobolevWeight a (k + 1) L n) ^ 2 := by
    rw [mul_pow, mul_pow, hw k, hw (k + 1)]
    nlinarith only [hb]
  exact (sq_le_sq₀ (mul_nonneg (expandingSobolevWeight_pos a k L hL n).le (by positivity)) (by
    exact mul_nonneg (by positivity) (expandingSobolevWeight_pos a (k + 1) L hL n).le)).mp hs

end DefocusingNLS

end OAI
