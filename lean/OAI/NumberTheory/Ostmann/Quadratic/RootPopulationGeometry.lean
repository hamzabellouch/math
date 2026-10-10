import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

namespace OAI

/-! # Diameter control for roots belonging to one signed quadratic kernel -/

namespace Ostmann

theorem square_sub_le_abs_square_difference (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a - b) ^ 2 ≤ |a ^ 2 - b ^ 2| := by
  by_cases hab : b ≤ a
  · have hs : 0 ≤ a ^ 2 - b ^ 2 := by nlinarith
    rw [abs_of_nonneg hs]
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hab)]
  · have hab' : a ≤ b := le_of_not_ge hab
    have hs : a ^ 2 - b ^ 2 ≤ 0 := by nlinarith
    rw [abs_of_nonpos hs]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hab')]

/-- Both signs of the squarefree kernel are allowed. Nonnegative root
parameters in an endpoint interval of diameter X have this diameter. -/
theorem kernel_root_diameter (u m h x y a b X : ℝ)
    (hu : u ≠ 0) (hm : 0 ≤ m) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : u * a ^ 2 = m * x - h) (hy : u * b ^ 2 = m * y - h)
    (hxy : |x - y| ≤ X) :
    |a - b| ≤ Real.sqrt (m * X / |u|) := by
  have hu0 : 0 < |u| := abs_pos.mpr hu
  have hdiff : u * (a ^ 2 - b ^ 2) = m * (x - y) := by nlinarith
  have habs := congrArg abs hdiff
  simp only [abs_mul, abs_of_nonneg hm] at habs
  have hp := square_sub_le_abs_square_difference a b ha hb
  have hsq : (a - b) ^ 2 ≤ m * X / |u| := by
    apply (le_div_iff₀ hu0).mpr
    have hmul := mul_le_mul_of_nonneg_left hp hu0.le
    have hsize := mul_le_mul_of_nonneg_left hxy hm
    nlinarith
  have hnonneg : 0 ≤ m * X / |u| := (sq_nonneg (a - b)).trans hsq
  have hroot := Real.sq_sqrt hnonneg
  have hroot0 := Real.sqrt_nonneg (m * X / |u|)
  nlinarith [sq_abs (a - b), abs_nonneg (a - b)]

end Ostmann

end OAI
