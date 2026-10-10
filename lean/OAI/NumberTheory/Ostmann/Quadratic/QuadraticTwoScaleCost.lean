import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace OAI

/-! # The two actual shortened matrix ranges in the quadratic comparison -/

namespace Ostmann

private theorem sqrt_add_subadditive {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hxy := Real.sq_sqrt (add_nonneg hx hy)
  have hxs := Real.sq_sqrt hx
  have hys := Real.sq_sqrt hy
  have hn := Real.sqrt_nonneg (x + y)
  nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y,
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

theorem quadratic_two_scale_sqrt_cost {Y N u v : ℝ}
    (hY : 0 ≤ Y) (hN : 0 ≤ N) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    Real.sqrt (Y + N / u) * Real.sqrt (Y + N / v) ≤
      Y + 2 * Real.sqrt (Y * N) + N / Real.sqrt (u * v) := by
  have hu₀ : 0 < u := zero_lt_one.trans_le hu
  have hv₀ : 0 < v := zero_lt_one.trans_le hv
  have hsu : Real.sqrt (N / u) ≤ Real.sqrt N := Real.sqrt_le_sqrt
    ((div_le_self hN hu).trans_eq rfl)
  have hsv : Real.sqrt (N / v) ≤ Real.sqrt N := Real.sqrt_le_sqrt
    ((div_le_self hN hv).trans_eq rfl)
  have hprod : Real.sqrt (N / u) * Real.sqrt (N / v) = N / Real.sqrt (u * v) := by
    rw [Real.sqrt_div hN, Real.sqrt_div hN, div_mul_div_comm,
      ← pow_two, Real.sq_sqrt hN, ← Real.sqrt_mul hu₀.le]
  calc
    _ ≤ (Real.sqrt Y + Real.sqrt (N / u)) * (Real.sqrt Y + Real.sqrt (N / v)) :=
      mul_le_mul (sqrt_add_subadditive hY (div_nonneg hN hu₀.le))
        (sqrt_add_subadditive hY (div_nonneg hN hv₀.le))
        (Real.sqrt_nonneg _) (by positivity)
    _ = Y + Real.sqrt Y * Real.sqrt (N / u) + Real.sqrt Y * Real.sqrt (N / v) +
        N / Real.sqrt (u * v) := by
      rw [← hprod]
      nlinarith only [Real.sq_sqrt hY]
    _ ≤ Y + Real.sqrt Y * Real.sqrt N + Real.sqrt Y * Real.sqrt N +
        N / Real.sqrt (u * v) := by
      gcongr
    _ = _ := by rw [Real.sqrt_mul hY]; ring

end Ostmann

end OAI
