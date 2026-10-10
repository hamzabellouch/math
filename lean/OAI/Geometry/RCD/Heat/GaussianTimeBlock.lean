import OAI.Geometry.RCD.Heat.GaussianShellKernel

namespace OAI

/-! # Gaussian shell bounds uniform over a dyadic time block -/

open Set Metric MeasureTheory

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (ker : ℝ → X → X → ℝ)

/-- On times t≤r², the same spatial Gaussian at scale r bounds every
kernel in the block once the time-dependent volume has a uniform lower bound. -/
theorem gaussian_time_displacement_upper (n : ℕ) {t r q C V D B : ℝ}
    (ht : 0 < t) (htr : t ≤ r ^ 2) (hr : 0 < r) (hq : 0 ≤ q)
    (hC : 0 ≤ C) (hV : 0 < V) (hD : 0 < D) (hB : 0 ≤ B)
    (p z : X)
    (hupper : ker t p z ≤ (C / μ.real (ball z (Real.sqrt t))) *
      Real.exp (-(dist p z) ^ 2 / (D * t) + B * t))
    (hvol : V * r ^ n ≤ μ.real (ball z (Real.sqrt t)))
    (hsep : q * r ≤ dist p z) :
    ker t p z ≤ (C / (V * r ^ n)) * Real.exp (B * r ^ 2) * Real.exp (-q ^ 2 / D) := by
  have hv : 0 < V * r ^ n := mul_pos hV (pow_pos hr n)
  have hratio := div_le_div_of_nonneg_left hC hv hvol
  have hsq : (q * r) ^ 2 ≤ (dist p z) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hq hr.le) dist_nonneg).mpr hsep
  have htime := mul_le_mul_of_nonneg_left htr (sq_nonneg q)
  have hfrac : q ^ 2 / D ≤ (dist p z) ^ 2 / (D * t) := by
    apply (le_div_iff₀ (mul_pos hD ht)).mpr
    have he : q ^ 2 / D * (D * t) = q ^ 2 * t := by field_simp
    rw [he]
    nlinarith
  have hBt := mul_le_mul_of_nonneg_left htr hB
  calc
    _ ≤ _ := hupper
    _ ≤ (C / (V * r ^ n)) * Real.exp (-q ^ 2 / D + B * r ^ 2) :=
      mul_le_mul hratio (Real.exp_le_exp.mpr (by
        simpa only [neg_div] using add_le_add (neg_le_neg hfrac) hBt))
        (Real.exp_pos _).le (div_nonneg hC hv.le)
    _ = _ := by rw [Real.exp_add]; ring

/-- A single coefficient bounds a full spatial shell at every time in
the block. Its Gaussian tail has no dependence on the selected time. -/
theorem gaussian_time_shell_upper (n : ℕ) {t r C V D B : ℝ}
    (ht : 0 < t) (htr : t ≤ r ^ 2) (hr : 0 < r)
    (hC : 0 ≤ C) (hV : 0 < V) (hD : 0 < D) (hB : 0 ≤ B)
    (p : X) (j : ℕ) {z : X} (hz : z ∈ dyadicShell p r j)
    (hupper : ker t p z ≤ (C / μ.real (ball z (Real.sqrt t))) *
      Real.exp (-(dist p z) ^ 2 / (D * t) + B * t))
    (hvol : V * r ^ n ≤ μ.real (ball z (Real.sqrt t))) :
    ker t p z ≤ (C / (V * r ^ n)) * Real.exp (B * r ^ 2) * gaussianShellFactor D⁻¹ j := by
  cases j with
  | zero =>
    simpa only [gaussianShellFactor, zero_pow (by decide : 2 ≠ 0), neg_zero,
      zero_div, Real.exp_zero] using
      gaussian_time_displacement_upper μ ker n ht htr hr (le_refl 0) hC hV hD hB p z hupper hvol
        (by simpa only [zero_mul] using (dist_nonneg : 0 ≤ dist p z))
  | succ j =>
    have he := gaussian_time_displacement_upper μ ker n ht htr hr
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j) hC hV hD hB p z hupper hvol
      (by simpa only [dist_comm] using dyadicShell_separation p hr j hz)
    have hpow : ((2 : ℝ) ^ j) ^ 2 = 4 ^ j := by
      rw [pow_two, ← mul_pow]
      norm_num
    simpa only [gaussianShellFactor, hpow, div_eq_mul_inv, neg_mul, mul_neg, mul_comm] using he

end RegularPointCoordinates

end

end OAI
