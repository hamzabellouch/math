import OAI.Geometry.EinsteinFour.Algebra

namespace OAI

/-!
# Spectral bounds for a Weyl block

Only the three real eigenvalues and their trace and norm identities are used.
The minimum eigenvalue is `-x`, and the Hilbert--Schmidt norm is `sqrt 6 * v`.
-/

namespace PositiveEinsteinFour

/-- The least eigenvalue of a real trace-free three-dimensional block controls
its normalized norm, including the zero block. This is the bound `v ≤ x ≤ 2v`
from Section 2 of the manuscript. -/
theorem weyl_eigenvalue_norm_bounds
    (v x s t : ℝ) (hv : 0 ≤ v)
    (htrace : -x + s + t = 0)
    (hnorm : x ^ 2 + s ^ 2 + t ^ 2 = 6 * v ^ 2)
    (hs : -x ≤ s) (ht : -x ≤ t) :
    v ≤ x ∧ x ≤ 2 * v := by
  have ht_eq : t = x - s := by linarith
  subst t
  have hx : 0 ≤ x := by linarith
  have hpositive_product : 0 ≤ (s + x) * (x - s + x) :=
    mul_nonneg (by linarith) (by linarith)
  constructor
  · nlinarith
  · nlinarith [sq_nonneg (s - (x - s))]

/-- Sectional positivity expressed by the two minimum eigenvalues implies the
strict sum bound for the normalized Weyl norms. -/
theorem weyl_norm_sum_lt_two
    (v b x y : ℝ) (hvx : v ≤ x) (hby : b ≤ y) (hpositive : x + y < 2) :
    v + b < 2 := by
  linarith

end PositiveEinsteinFour

end OAI
