import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Small positive semidefinite forms and Schur completion

The closed determinant criterion includes vanishing diagonal entries. The
Schur estimate below consequently includes the singular axial endpoint of the
quadratic comparison in Section 6 of the manuscript.
-/

namespace PositiveEinsteinFour

/-- The determinant test for a symmetric two-by-two real quadratic form,
including zero diagonal entries. -/
theorem quadratic_form_nonneg_of_det
    (r h s : ℝ) (hr : 0 ≤ r) (hh : 0 ≤ h) (hdet : s ^ 2 ≤ r * h)
    (x y : ℝ) :
    0 ≤ r * x ^ 2 + 2 * s * x * y + h * y ^ 2 := by
  by_cases hrzero : r = 0
  · have hs : s = 0 := by nlinarith [sq_nonneg s]
    subst r
    subst s
    simpa using mul_nonneg hh (sq_nonneg y)
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hrzero)
    have hdet_y : 0 ≤ (r * h - s ^ 2) * y ^ 2 :=
      mul_nonneg (sub_nonneg.mpr hdet) (sq_nonneg y)
    have hidentity :
        r * (r * x ^ 2 + 2 * s * x * y + h * y ^ 2) =
          (r * x + s * y) ^ 2 + (r * h - s ^ 2) * y ^ 2 := by ring
    have hproduct : 0 ≤ r * (r * x ^ 2 + 2 * s * x * y + h * y ^ 2) := by
      rw [hidentity]
      exact add_nonneg (sq_nonneg _) hdet_y
    exact nonneg_of_mul_nonneg_right hproduct hrpos

/-- Conversely, nonnegativity of the binary form implies the closed diagonal
and determinant conditions. The singular diagonal case is tested directly. -/
theorem quadratic_form_det_of_nonneg
    (r h s : ℝ)
    (hform : ∀ x y, 0 ≤ r * x ^ 2 + 2 * s * x * y + h * y ^ 2) :
    0 ≤ r ∧ 0 ≤ h ∧ s ^ 2 ≤ r * h := by
  have hr : 0 ≤ r := by simpa using hform 1 0
  have hh : 0 ≤ h := by simpa using hform 0 1
  refine ⟨hr, hh, ?_⟩
  by_cases hrzero : r = 0
  · subst r
    have htest := hform (h + 1) (-s)
    have hhs : 0 ≤ h * s ^ 2 := mul_nonneg hh (sq_nonneg s)
    have hs : s = 0 := by nlinarith [sq_nonneg s]
    simp [hs]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hrzero)
    have htest := hform (-s) r
    have hproduct : 0 ≤ r * (r * h - s ^ 2) := by nlinarith
    have hdet := nonneg_of_mul_nonneg_right hproduct hrpos
    linarith

/-- Division-free Schur completion. The scalar first corner may vanish;
nonnegativity of the lower form and the Schur bound handle that endpoint. -/
theorem schur_complement_nonneg
    (a b c f d e : ℝ) (ha : 0 ≤ a)
    (hbase : ∀ y z, 0 ≤ b * y ^ 2 + 2 * c * y * z + f * z ^ 2)
    (hschur : ∀ y z,
      (d * y + e * z) ^ 2 ≤ a * (b * y ^ 2 + 2 * c * y * z + f * z ^ 2))
    (x y z : ℝ) :
    0 ≤ a * x ^ 2 + 2 * x * (d * y + e * z) +
      b * y ^ 2 + 2 * c * y * z + f * z ^ 2 := by
  have h := quadratic_form_nonneg_of_det a
    (b * y ^ 2 + 2 * c * y * z + f * z ^ 2) (d * y + e * z)
    ha (hbase y z) (hschur y z) x 1
  nlinarith

/-- At a zero scalar corner, the Schur bound forces both mixed coefficients to
vanish. This isolates the endpoint without a division by the corner. -/
theorem schur_zero_corner
    (b c f d e : ℝ)
    (hschur : ∀ y z,
      (d * y + e * z) ^ 2 ≤ (0 : ℝ) * (b * y ^ 2 + 2 * c * y * z + f * z ^ 2)) :
    d = 0 ∧ e = 0 := by
  have hd := hschur 1 0
  have he := hschur 0 1
  constructor <;> nlinarith [sq_nonneg d, sq_nonneg e]

end PositiveEinsteinFour

end OAI
