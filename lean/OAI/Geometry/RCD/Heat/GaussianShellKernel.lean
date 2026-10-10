import OAI.Geometry.RCD.Heat.GaussianDyadicShells

namespace OAI

/-! # Quantitative Gaussian bounds on the actual dyadic shells -/

open Set Metric MeasureTheory

noncomputable section

namespace RegularPointCoordinates

/-- The first shell contains the pole; subsequent shells have a Gaussian
factor at their inner radius. -/
def gaussianShellFactor (c : ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => Real.exp (-c * 4 ^ j)

theorem gaussianShellFactor_nonneg (c : ℝ) (j : ℕ) : 0 ≤ gaussianShellFactor c j := by
  cases j <;> simp [gaussianShellFactor, (Real.exp_pos _).le]

theorem summable_gaussianShellFactor {b c : ℝ} (hb : 0 ≤ b) (hc : 0 < c) :
    Summable (fun j : ℕ => b ^ j * gaussianShellFactor c j) := by
  rw [← summable_nat_add_iff 1]
  simpa only [gaussianShellFactor, pow_succ, mul_comm, mul_left_comm, mul_assoc] using
    (summable_dyadic_gaussian hb hc (by norm_num : (1 : ℝ) < 4)).mul_left b

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (k : ℝ → X → X → ℝ)

/-- Cancel the reference radius from a Gaussian exponent and retain the
actual volume normalization. -/
theorem gaussian_upper_scaled_distance (n : ℕ) {r q C V D B : ℝ}
    (hr : 0 < r) (hq : 0 ≤ q) (hC : 0 ≤ C) (hV : 0 < V) (hD : 0 < D)
    (p y : X)
    (hupper : k (r ^ 2) p y ≤ (C / μ.real (ball y r)) *
      Real.exp (-(dist p y) ^ 2 / (D * r ^ 2) + B * r ^ 2))
    (hvol : V * r ^ n ≤ μ.real (ball y r)) (hsep : q * r ≤ dist p y) :
    k (r ^ 2) p y ≤ (C / (V * r ^ n)) * Real.exp (B * r ^ 2) *
      Real.exp (-(q ^ 2) / D) := by
  have hv : 0 < V * r ^ n := mul_pos hV (pow_pos hr _)
  have hratio : C / μ.real (ball y r) ≤ C / (V * r ^ n) :=
    div_le_div_of_nonneg_left hC hv hvol
  have hsq : (q * r) ^ 2 ≤ (dist p y) ^ 2 :=
    sq_le_sq₀ (mul_nonneg hq hr.le) dist_nonneg |>.mpr hsep
  have hfrac : q ^ 2 / D ≤ (dist p y) ^ 2 / (D * r ^ 2) := by
    calc
      _ = (q * r) ^ 2 / (D * r ^ 2) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hsq (mul_pos hD (sq_pos_of_pos hr)).le
  calc
    _ ≤ _ := hupper
    _ ≤ (C / (V * r ^ n)) * Real.exp (-(q ^ 2) / D + B * r ^ 2) :=
      mul_le_mul hratio (Real.exp_le_exp.mpr (by
        simpa only [neg_div, add_comm] using add_le_add_right (neg_le_neg hfrac) (B * r ^ 2)))
        (Real.exp_pos _).le (div_nonneg hC hv.le)
    _ = _ := by rw [Real.exp_add]; ring

/-- A Gaussian kernel bound on one actual dyadic shell. -/
theorem gaussian_shell_upper (n : ℕ) {r C V D B : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C) (hV : 0 < V) (hD : 0 < D)
    (p : X) (j : ℕ) {y : X} (hy : y ∈ dyadicShell p r j)
    (hupper : k (r ^ 2) p y ≤ (C / μ.real (ball y r)) *
      Real.exp (-(dist p y) ^ 2 / (D * r ^ 2) + B * r ^ 2))
    (hvol : V * r ^ n ≤ μ.real (ball y r)) :
    k (r ^ 2) p y ≤ (C / (V * r ^ n)) * Real.exp (B * r ^ 2) *
      gaussianShellFactor D⁻¹ j := by
  cases j with
  | zero =>
    simpa only [gaussianShellFactor, zero_pow (by decide : 2 ≠ 0), zero_div,
      neg_zero, Real.exp_zero, mul_one] using
      gaussian_upper_scaled_distance μ k n hr (le_refl 0) hC hV hD p y
        hupper hvol (by simpa only [zero_mul] using (dist_nonneg : 0 ≤ dist p y))
  | succ j =>
    have he := gaussian_upper_scaled_distance μ k n hr
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j)
      hC hV hD p y hupper hvol
      (by simpa only [dist_comm] using dyadicShell_separation p hr j hy)
    have hpow : ((2 : ℝ) ^ j) ^ 2 = 4 ^ j := by
      rw [pow_two, ← mul_pow]
      norm_num
    simpa only [gaussianShellFactor, hpow, div_eq_mul_inv, neg_mul, mul_neg, mul_comm] using he

/-- The JLZ bound gives one explicit shell majorant for a cutoff kernel.
Only the centers where the cutoff is nonzero need the volume lower bound. -/
theorem gaussian_cutoff_shell_upper (n : ℕ) {r C V D B : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C) (hV : 0 < V) (hD : 0 < D)
    (p : X) {χ : X → ℝ} (hχ : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hk : ∀ y, 0 ≤ k (r ^ 2) p y)
    (hupper : ∀ y, k (r ^ 2) p y ≤ (C / μ.real (ball y r)) *
      Real.exp (-(dist p y) ^ 2 / (D * r ^ 2) + B * r ^ 2))
    (hvol : ∀ y, χ y ≠ 0 → V * r ^ n ≤ μ.real (ball y r))
    (j : ℕ) {y : X} (hy : y ∈ dyadicShell p r j) :
    χ y * k (r ^ 2) p y ≤ (C / (V * r ^ n)) * Real.exp (B * r ^ 2) *
      gaussianShellFactor D⁻¹ j := by
  by_cases hz : χ y = 0
  · rw [hz, zero_mul]
    exact mul_nonneg (mul_nonneg (div_nonneg hC (mul_pos hV (pow_pos hr _)).le)
      (Real.exp_pos _).le) (gaussianShellFactor_nonneg _ _)
  exact (mul_le_of_le_one_left (hk y) (hχ y).2).trans
    (gaussian_shell_upper μ k n hr hC hV hD p j hy (hupper y) (hvol y hz))

end RegularPointCoordinates

end

end OAI
