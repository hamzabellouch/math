import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowRecurrenceBridge

namespace OAI

/-! # The derivative shift throughout the regularized parameter strip -/

open MeasureTheory Filter Topology

namespace DefocusingNLS

theorem integral_slowLaplaceKernel_eq (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    (∫ u : ℝ in Set.Ioi 0, slowLaplaceKernel q m x u) =
      (∫ u : ℝ in Set.Ioi 0, regularizedSlowKernel q m x u) + Complex.Gamma q := by
  have hg : IntegrableOn
      (fun u : ℝ => Complex.exp (-(u : ℂ)) * (u : ℂ) ^ (q - 1)) (Set.Ioi 0) := by
    simpa only [Complex.ofReal_exp, Complex.ofReal_neg] using
      Complex.GammaIntegral_convergent hq
  simp_rw [slowLaplaceKernel_eq]
  rw [integral_add (integrable_regularizedSlowKernel q m x (by linarith) hx hx0) hg]
  congr 1
  rw [Complex.Gamma_eq_integral hq]
  simp only [Complex.GammaIntegral, Complex.ofReal_exp, Complex.ofReal_neg]

theorem regularizedSlowSolution_bracket_eq (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    1 + (Complex.Gamma q)⁻¹ * (∫ u : ℝ in Set.Ioi 0, regularizedSlowKernel q m x u) =
      (Complex.Gamma (q + 1))⁻¹ *
        ((∫ u : ℝ in Set.Ioi 0, slowLaplaceKernel (q + 1) (m + 1) x u) -
          (((m : ℂ) - 1 - q) / x) *
            (∫ u : ℝ in Set.Ioi 0, slowLaplaceKernel (q + 1) m x u)) := by
  have hq' : 0 < (q + 1).re := by change 0 < q.re + 1; linarith
  rw [integral_slowLaplaceKernel_eq (q + 1) (m + 1) x hq' hx hx0,
    Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one]
  have h := slowRegularized_integral_recurrence q m x hq hx hx0
  have hΓ : (Complex.Gamma (q + 1))⁻¹ * Complex.Gamma (q + 1) = 1 :=
    inv_mul_cancel₀ (Complex.Gamma_ne_zero_of_re_pos hq')
  linear_combination (Complex.Gamma (q + 1))⁻¹ * h - hΓ

theorem integral_slowKernelSpatialDerivative_eq_laplace (q : ℂ) (m : ℕ) (x : ℂ) :
    (∫ u : ℝ in Set.Ioi 0, slowKernelSpatialDerivative q m x u) =
      (-((m : ℂ) - 1 - q) / x ^ 2) *
        (∫ u : ℝ in Set.Ioi 0, slowLaplaceKernel (q + 1) m x u) := by
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  rw [slowKernelSpatialDerivative_eq q m x hu, slowLaplaceKernel_eq]
  simp only [add_sub_cancel_right]

/-- The actual regularized definition satisfies the derivative recurrence
on the full parameter strip, including `q = 0`. -/
theorem hasDerivAt_regularizedSlowSolution_shift (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 < x.re) :
    HasDerivAt (regularizedSlowSolution q m)
      (-q * regularizedSlowSolution (q + 1) (m + 1) x) x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hq' : 0 < (q + 1).re := by change 0 < q.re + 1; linarith
  have hp : x ^ (-q) = x ^ (-q - 1) * x := by
    calc
      _ = x ^ ((-q - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Complex.cpow_add _ _ hx0, Complex.cpow_one]
  have h := hasDerivAt_regularizedSlowSolution q m x hq hx
  rw [regularizedSlowSolution_bracket_eq q m x hq hx.le hx0,
    integral_slowKernelSpatialDerivative_eq_laplace] at h
  rw [regularizedSlowSolution_eq_laplace (q + 1) (m + 1) x hq' hx.le hx0]
  convert h using 1
  rw [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one q, hp]
  have he : -(q + 1) = -q - 1 := by ring
  rw [he]
  field_simp
  ring

theorem hasDerivAt_deriv_regularizedSlowSolution (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 < x.re) :
    HasDerivAt (deriv (regularizedSlowSolution q m))
      (q * (q + 1) * regularizedSlowSolution (q + 2) (m + 2) x) x := by
  have hq' : -1 < (q + 1).re := by change -1 < q.re + 1; linarith
  have h := (hasDerivAt_regularizedSlowSolution_shift (q + 1) (m + 1) x hq' hx).const_mul (-q)
  have heq : deriv (regularizedSlowSolution q m) =ᶠ[𝓝 x]
      (fun z => -q * regularizedSlowSolution (q + 1) (m + 1) z) := by
    have hs : {z : ℂ | 0 < z.re} ∈ 𝓝 x :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx
    filter_upwards [hs] with z hz
    exact (hasDerivAt_regularizedSlowSolution_shift q m z hq hz).deriv
  have hqq : q + 1 + 1 = q + 2 := by ring
  convert h.congr_of_eventuallyEq heq using 1
  simp only [hqq, Nat.add_assoc, show (1 : ℕ) + 1 = 2 from rfl]
  ring

end DefocusingNLS

end OAI
