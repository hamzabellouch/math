import OAI.MathematicalPhysics.DefocusingNLS.Certificates.PolynomialDisk
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RootDiskArithmetic

namespace OAI

/-!+# Interpreting integer disk bounds over the complex numbers

Integer upper and lower coefficient bounds imply
the norm inequality required by the disk root theorem.
-/

namespace DefocusingNLS.SeparatorArithmetic

theorem norm_toComplex_le_upper (z : GaussianInt) :
    ‖(z : ℂ)‖ ≤ (coefficientUpper z : ℝ) := by
  simpa only [coefficientUpper, Int.cast_add, Int.cast_abs,
    GaussianInt.intCast_re, GaussianInt.intCast_im] using
    Complex.norm_le_abs_re_add_abs_im (z : ℂ)

theorem lower_le_norm_toComplex (z : GaussianInt) :
    (coefficientLower z : ℝ) ≤ ‖(z : ℂ)‖ := by
  simp only [coefficientLower, Int.cast_max, Int.cast_abs,
    GaussianInt.intCast_re, GaussianInt.intCast_im]
  exact max_le (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)

theorem root_of_integer_coefficient_bound (a b : GaussianInt)
    (c : Fin 14 → GaussianInt) (r : ℕ) (hb : b ≠ 0)
    (hbound : coefficientUpper a +
      ∑ i, coefficientUpper (c i) * (r : ℤ) ^ ((i : ℕ) + 2) ≤
        coefficientLower b * r) :
    ∃ z : ℂ, ‖z‖ ≤ r ∧
      (a : ℂ) + (b : ℂ) * z + ∑ i, (c i : ℂ) * z ^ ((i : ℕ) + 2) = 0 := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  apply degree_fifteen_root_in_disk (a : ℂ) (b : ℂ)
    (fun i => (c i : ℂ)) r hr (GaussianInt.toComplex_eq_zero.not.mpr hb)
  have hreal : (coefficientUpper a : ℝ) +
      ∑ i, (coefficientUpper (c i) : ℝ) * (r : ℝ) ^ ((i : ℕ) + 2) ≤
        (coefficientLower b : ℝ) * r := by exact_mod_cast hbound
  calc
    ‖(a : ℂ)‖ + ∑ i, ‖(c i : ℂ)‖ * (r : ℝ) ^ ((i : ℕ) + 2) ≤
        (coefficientUpper a : ℝ) +
          ∑ i, (coefficientUpper (c i) : ℝ) * (r : ℝ) ^ ((i : ℕ) + 2) := by
      apply add_le_add (norm_toComplex_le_upper a)
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (norm_toComplex_le_upper (c i))
        (pow_nonneg hr _)
    _ ≤ (coefficientLower b : ℝ) * r := hreal
    _ ≤ ‖(b : ℂ)‖ * r := mul_le_mul_of_nonneg_right (lower_le_norm_toComplex b) hr

end DefocusingNLS.SeparatorArithmetic

end OAI
