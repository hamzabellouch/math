import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowIntegralIdentification

namespace OAI

/-! # The regularized slow solution on the initial half-planes

The regularized integral satisfies the differential equation and derivative
shift identity on the initial complex half-planes.
-/

open Filter Topology

namespace DefocusingNLS

theorem regularizedSlowSolution_eventuallyEq_euler (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 < x.re) :
    regularizedSlowSolution q m =ᶠ[𝓝 x]
      (fun z => (Complex.Gamma q)⁻¹ * slowEulerIntegral q m z) := by
  have hs : {z : ℂ | 0 < z.re} ∈ 𝓝 x :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx
  filter_upwards [hs] with z hz
  exact regularizedSlowSolution_eq_euler_complex q m z hq hz

theorem hasDerivAt_regularizedSlowSolution_initial (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 < x.re) :
    HasDerivAt (regularizedSlowSolution q m)
      (-((Complex.Gamma q)⁻¹ * slowEulerIntegral (q + 1) (m + 1) x)) x := by
  have h := (hasDerivAt_slowEulerIntegral q m x hq hx).const_mul (Complex.Gamma q)⁻¹
  simpa only [mul_neg] using h.congr_of_eventuallyEq
    (regularizedSlowSolution_eventuallyEq_euler q m x hq hx)

theorem hasDerivAt_deriv_regularizedSlowSolution_initial (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 < x.re) :
    HasDerivAt (deriv (regularizedSlowSolution q m))
      ((Complex.Gamma q)⁻¹ * slowEulerIntegral (q + 2) (m + 2) x) x := by
  have hq' : 0 < (q + 1).re := by change 0 < q.re + 1; linarith
  have h := ((hasDerivAt_slowEulerIntegral (q + 1) (m + 1) x hq' hx).const_mul
    (Complex.Gamma q)⁻¹).neg
  have heq : deriv (regularizedSlowSolution q m) =ᶠ[𝓝 x]
      (fun z => -((Complex.Gamma q)⁻¹ * slowEulerIntegral (q + 1) (m + 1) z)) := by
    have hs : {z : ℂ | 0 < z.re} ∈ 𝓝 x :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx
    filter_upwards [hs] with z hz
    exact (hasDerivAt_regularizedSlowSolution_initial q m z hq hz).deriv
  have hqq : q + 1 + 1 = q + 2 := by ring
  simpa only [mul_neg, neg_neg, hqq, Nat.add_assoc, show (1 : ℕ) + 1 = 2 from rfl] using
    h.congr_of_eventuallyEq heq

/-- Kummer's equation for the actual regularized definition on the initial
complex half-planes. -/
theorem regularizedSlowSolution_kummer_equation_initial (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 < x.re) :
    x * deriv (deriv (regularizedSlowSolution q m)) x +
      ((m : ℂ) - x) * deriv (regularizedSlowSolution q m) x -
      q * regularizedSlowSolution q m x = 0 := by
  rw [(hasDerivAt_deriv_regularizedSlowSolution_initial q m x hq hx).deriv,
    (hasDerivAt_regularizedSlowSolution_initial q m x hq hx).deriv,
    regularizedSlowSolution_eq_euler_complex q m x hq hx]
  have h := slowEuler_integral_relation q m x hq hx
  change x * slowEulerIntegral (q + 2) (m + 2) x +
    (x - (m : ℂ)) * slowEulerIntegral (q + 1) (m + 1) x -
      q * slowEulerIntegral q m x = 0 at h
  linear_combination (Complex.Gamma q)⁻¹ * h

/-- The derivative shift identity, before continuation to `Re(q) > -1`. -/
theorem hasDerivAt_regularizedSlowSolution_shift_initial (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 < x.re) :
    HasDerivAt (regularizedSlowSolution q m)
      (-q * regularizedSlowSolution (q + 1) (m + 1) x) x := by
  have hq0 : q ≠ 0 := by intro h; simp [h] at hq
  have hΓ : Complex.Gamma q ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hq
  have he : -((Complex.Gamma q)⁻¹ * slowEulerIntegral (q + 1) (m + 1) x) =
      -q * regularizedSlowSolution (q + 1) (m + 1) x := by
    rw [regularizedSlowSolution_eq_euler_complex (q + 1) (m + 1) x
      (by change 0 < q.re + 1; linarith) hx, Complex.Gamma_add_one q hq0]
    field_simp
  rw [← he]
  exact hasDerivAt_regularizedSlowSolution_initial q m x hq hx

end DefocusingNLS

end OAI
