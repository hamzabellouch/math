import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace OAI

/-!
# The finite inverse for the higher-dimensional stationary expansion

The polynomials are those of `osc:L-operators` and `osc:B-operators` in
Section 6 of the manuscript. Their variable represents the sphere Laplacian.
The finite inverse identity is algebraic and independent of a sphere
stationary-phase expansion.
-/

namespace Falconer
open Polynomial
open scoped BigOperators

noncomputable def sphereStationaryConstant (n : ℕ) : ℂ :=
  ((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) *
    Complex.exp (-(Real.pi : ℂ) * n / 4 * Complex.I)

theorem sphereStationaryConstant_ne_zero (n : ℕ) :
    sphereStationaryConstant n ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast (Real.rpow_pos_of_pos (by positivity : 0 < 2 * Real.pi)
      ((n : ℝ) / 2)).ne'
  · exact Complex.exp_ne_zero _

/-- The direct stationary coefficient, as a polynomial in the sphere Laplacian.
Here `n` is the sphere dimension, so the ambient dimension is `n+1`. -/
noncomputable def sphereDirectPolynomial (n j : ℕ) : Polynomial ℂ :=
  C (sphereStationaryConstant n / ((2 * Complex.I)^j * (j.factorial : ℂ))) *
    ∏ q ∈ Finset.range j,
      (X + C ((q : ℂ) * (q+1) - (n : ℂ) * ((n : ℂ)-2) / 4))

@[simp] theorem sphereDirectPolynomial_zero (n : ℕ) :
    sphereDirectPolynomial n 0 = C (sphereStationaryConstant n) := by
  simp [sphereDirectPolynomial]

theorem sphereDirectPolynomial_degree (n j : ℕ) :
    (sphereDirectPolynomial n j).natDegree ≤ j := by
  apply (natDegree_C_mul_le _ _).trans
  apply (natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _q ∈ Finset.range j, 1 := Finset.sum_le_sum (fun q _ =>
      (natDegree_X_add_C _).le)
    _ = j := by simp

private theorem constant_polynomial_product (a b : ℂ) (P Q : Polynomial ℂ) :
    C a * (C b * (P*Q)) = C (a*b) * Q * P := by
  rw [C_mul]
  ring

private theorem polynomial_product_reorder (A B D : Polynomial ℂ) :
    A*B*D = B*(A*D) := by ring

/-- The coefficient recurrence obtained by substituting the outgoing series
in the Helmholtz equation, with the manuscript's Laplacian sign convention. -/
theorem sphereDirectPolynomial_succ (n j : ℕ) :
    C (2 * Complex.I * (j+1)) * sphereDirectPolynomial n (j+1) =
      (X + C ((j : ℂ)*(j+1) - (n : ℂ)*((n : ℂ)-2)/4)) *
        sphereDirectPolynomial n j := by
  have hz : 2 * Complex.I ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hj' : (j+1 : ℂ) ≠ 0 := by
    exact_mod_cast (show j+1 ≠ 0 by omega)
  have hc : (2 * Complex.I * (j+1)) *
      (sphereStationaryConstant n / ((2 * Complex.I)^(j+1) * ((j+1).factorial : ℂ))) =
        sphereStationaryConstant n / ((2 * Complex.I)^j * (j.factorial : ℂ)) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp [hz, hj, hj']
  simp only [sphereDirectPolynomial, Finset.prod_range_succ]
  calc
    _ = C ((2 * Complex.I * (j+1)) *
        (sphereStationaryConstant n / ((2 * Complex.I)^(j+1) * ((j+1).factorial : ℂ)))) *
        (X + C ((j : ℂ)*(j+1) - (n : ℂ)*((n : ℂ)-2)/4)) *
        ∏ q ∈ Finset.range j,
          (X + C ((q : ℂ)*(q+1) - (n : ℂ)*((n : ℂ)-2)/4)) := by
      exact constant_polynomial_product _ _ _ _
    _ = _ := by
      rw [hc]
      exact polynomial_product_reorder _ _ _


/-- The finite inverse coefficients from `osc:B-operators`. -/
noncomputable def sphereInversePolynomial (n : ℕ) : ℕ → Polynomial ℂ
  | 0 => C ((sphereStationaryConstant n)⁻¹)
  | j+1 => C (-(sphereStationaryConstant n)⁻¹) *
      ∑ h ∈ Finset.range (j+1),
        sphereDirectPolynomial n (h+1) * sphereInversePolynomial n (j-h)
termination_by j => j
decreasing_by omega

@[simp] theorem sphereInversePolynomial_zero (n : ℕ) :
    sphereInversePolynomial n 0 = C ((sphereStationaryConstant n)⁻¹) := by
  rw [sphereInversePolynomial]

theorem sphereInversePolynomial_degree (n j : ℕ) :
    (sphereInversePolynomial n j).natDegree ≤ j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [sphereInversePolynomial]
      apply (natDegree_C_mul_le _ _).trans
      apply natDegree_sum_le_of_forall_le
      intro h hh
      have hh' : h ≤ j := by have := Finset.mem_range.mp hh; omega
      have hb := ih (j-h) (by omega)
      have hd := sphereDirectPolynomial_degree n (h+1)
      exact natDegree_mul_le.trans (by omega)

theorem sphereInversePolynomial_cancellation (n j : ℕ) :
    (∑ h ∈ Finset.range (j+1),
      sphereDirectPolynomial n h * sphereInversePolynomial n (j-h)) =
        if j = 0 then 1 else 0 := by
  cases j with
  | zero =>
    simp only [Nat.zero_add, Finset.sum_range_one, Nat.sub_self,
      sphereDirectPolynomial_zero, sphereInversePolynomial_zero, ↓reduceIte]
    rw [← C_mul, mul_inv_cancel₀ (sphereStationaryConstant_ne_zero n), C_1]
  | succ j =>
    rw [Finset.sum_range_succ']
    simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero, sphereDirectPolynomial_zero,
      sphereInversePolynomial, Nat.succ_ne_zero, ↓reduceIte]
    rw [← mul_assoc, ← C_mul]
    simp [sphereStationaryConstant_ne_zero]

theorem sphereInversePolynomial_cancellation_reverse (n j : ℕ) :
    (∑ h ∈ Finset.range (j+1),
      sphereDirectPolynomial n (j-h) * sphereInversePolynomial n h) =
        if j = 0 then 1 else 0 := by
  rw [← sphereInversePolynomial_cancellation n j,
    ← Finset.sum_range_reflect (fun h =>
      sphereDirectPolynomial n h * sphereInversePolynomial n (j-h)) (j+1)]
  apply Finset.sum_congr rfl
  intro h hh
  have hh' : h ≤ j := by have := Finset.mem_range.mp hh; omega
  simp [Nat.sub_sub_self hh']

/-- Exact cancellation in the triangular truncation used for the inverse
stationary expansion, before estimating any analytic remainder. -/
theorem sphereInversePolynomial_triangle (n J : ℕ) (t : ℂ) :
    (∑ j ∈ Finset.range (J+1), ∑ h ∈ Finset.range (J+1-j),
      C (t^(j+h)) * sphereDirectPolynomial n h * sphereInversePolynomial n j) = 1 := by
  rw [← Finset.sum_range_diag_flip]
  have he : ∀ k ∈ Finset.range (J+1),
      (∑ j ∈ Finset.range (k+1),
        C (t^(j+(k-j))) * sphereDirectPolynomial n (k-j) *
          sphereInversePolynomial n j) = C (t^k) * (if k = 0 then 1 else 0) := by
    intro k _
    rw [← sphereInversePolynomial_cancellation_reverse n k, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ k := by have := Finset.mem_range.mp hj; omega
    rw [Nat.add_sub_of_le hj', mul_assoc]
  rw [Finset.sum_congr rfl he]
  simp

/-- Applying the triangular identity to a Laplacian jet evaluated at a point.
The relevant linear map is `p ↦ (p(Δ)b)(e)`. -/
theorem sphereInversePolynomial_triangle_linear (n J : ℕ) (t : ℂ)
    (F : Polynomial ℂ →ₗ[ℂ] ℂ) :
    (∑ j ∈ Finset.range (J+1), t^j *
      ∑ h ∈ Finset.range (J+1-j),
        t^h * F (sphereDirectPolynomial n h * sphereInversePolynomial n j)) = F 1 := by
  have he := congrArg F (sphereInversePolynomial_triangle n J t)
  simp only [map_sum] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [mul_assoc (C _), ← Polynomial.smul_eq_C_mul, map_smul]
  simp only [smul_eq_mul, pow_add]
  ring

/-- The exact error identity for inversion. Each `I j` is a normalized
stationary integral of `B_j b`, expanded through order `J-j`. -/
theorem sphereInversePolynomial_error_identity (n J : ℕ) (t z : ℂ)
    (F : Polynomial ℂ →ₗ[ℂ] ℂ) (I : ℕ → ℂ) :
    (∑ j ∈ Finset.range (J+1), t^j * I j) - z * F 1 =
      ∑ j ∈ Finset.range (J+1), t^j *
        (I j - z * ∑ h ∈ Finset.range (J+1-j),
          t^h * F (sphereDirectPolynomial n h * sphereInversePolynomial n j)) := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← sphereInversePolynomial_triangle_linear n J t F, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- No uniformity or analyticity is hidden in finite inversion: it costs
exactly the sum of the weighted direct remainder bounds. -/
theorem sphereInversePolynomial_remainder (n J : ℕ) (t z : ℂ)
    (F : Polynomial ℂ →ₗ[ℂ] ℂ) (I : ℕ → ℂ) (E : ℕ → ℝ)
    (hE : ∀ j ∈ Finset.range (J+1),
      ‖I j - z * ∑ h ∈ Finset.range (J+1-j),
        t^h * F (sphereDirectPolynomial n h * sphereInversePolynomial n j)‖ ≤ E j) :
    ‖(∑ j ∈ Finset.range (J+1), t^j * I j) - z * F 1‖ ≤
      ∑ j ∈ Finset.range (J+1), ‖t‖^j * E j := by
  rw [sphereInversePolynomial_error_identity]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (hE j hj) (pow_nonneg (norm_nonneg t) j)

end Falconer

end OAI
