import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowShiftEquation

namespace OAI

/-! # Kummer's equation on the regularized parameter strip -/

open MeasureTheory

namespace DefocusingNLS

theorem slowEulerKernel_adjacent (q : ℂ) (m : ℕ) (x : ℂ) {u : ℝ} (hu : 0 < u) :
    slowEulerKernel q (m + 1) x u =
      slowEulerKernel q m x u + slowEulerKernel (q + 1) (m + 1) x u := by
  have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hb0 : 1 + (u : ℂ) ≠ 0 := by
    have : 0 < (1 + (u : ℂ)).re := by simp; linarith
    intro h
    simp [h] at this
  have hp : (u : ℂ) ^ q = (u : ℂ) ^ (q - 1) * (u : ℂ) := by
    calc
      _ = (u : ℂ) ^ (q - 1 + 1) := by congr 1; ring
      _ = _ := by rw [Complex.cpow_add _ _ hu0, Complex.cpow_one]
  have hb : (1 + (u : ℂ)) ^ ((m : ℂ) - q) =
      (1 + (u : ℂ)) ^ ((m : ℂ) - 1 - q) * (1 + (u : ℂ)) := by
    calc
      _ = (1 + (u : ℂ)) ^ (((m : ℂ) - 1 - q) + 1) := by congr 1; ring
      _ = _ := by rw [Complex.cpow_add _ _ hb0, Complex.cpow_one]
  have he : ((m + 1 : ℕ) : ℂ) - 1 - (q + 1) = (m : ℂ) - 1 - q := by
    push_cast
    ring
  have he' : ((m + 1 : ℕ) : ℂ) - 1 - q = (m : ℂ) - q := by
    push_cast
    ring
  simp only [slowEulerKernel, he, he', add_sub_cancel_right, hb, hp]
  ring

theorem slowEulerIntegral_adjacent (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 < x.re) :
    slowEulerIntegral q (m + 1) x =
      slowEulerIntegral q m x + slowEulerIntegral (q + 1) (m + 1) x := by
  have hq' : 0 < (q + 1).re := by change 0 < q.re + 1; linarith
  unfold slowEulerIntegral
  rw [← integral_add (integrable_slowEulerKernel q m x hq hx)
    (integrable_slowEulerKernel (q + 1) (m + 1) x hq' hx)]
  exact setIntegral_congr_fun measurableSet_Ioi fun u hu => slowEulerKernel_adjacent q m x hu

theorem slowEulerIntegral_contiguous (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 < x.re) :
    x * slowEulerIntegral (q + 1) (m + 2) x - (m : ℂ) * slowEulerIntegral q (m + 1) x +
      ((m : ℂ) - q) * slowEulerIntegral q m x = 0 := by
  have hq' : 0 < (q + 1).re := by change 0 < q.re + 1; linarith
  have h₀ := slowEulerIntegral_adjacent q m x hq hx
  have h₁ := slowEulerIntegral_adjacent (q + 1) (m + 1) x hq' hx
  have h := slowEuler_integral_relation q m x hq hx
  change x * slowEulerIntegral (q + 2) (m + 2) x +
    (x - (m : ℂ)) * slowEulerIntegral (q + 1) (m + 1) x -
      q * slowEulerIntegral q m x = 0 at h
  have hqq : q + 1 + 1 = q + 2 := by ring
  simp only [hqq, Nat.add_assoc, show (1 : ℕ) + 1 = 2 from rfl] at h₁
  linear_combination h + x * h₁ - (m : ℂ) * h₀

theorem regularizedSlowSolution_contiguous (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    regularizedSlowSolution q m x =
      x * regularizedSlowSolution (q + 1) (m + 1) x -
        ((m : ℂ) - 1 - q) * regularizedSlowSolution (q + 1) m x := by
  have hq' : 0 < (q + 1).re := by change 0 < q.re + 1; linarith
  have hp : x ^ (-q) = x ^ (-(q + 1)) * x := by
    calc
      _ = x ^ (-(q + 1) + 1) := by congr 1; ring
      _ = _ := by rw [Complex.cpow_add _ _ hx0, Complex.cpow_one]
  rw [regularizedSlowSolution_eq_laplace (q + 1) (m + 1) x hq' hx hx0,
    regularizedSlowSolution_eq_laplace (q + 1) m x hq' hx hx0]
  unfold regularizedSlowSolution
  rw [regularizedSlowSolution_bracket_eq q m x hq hx hx0, hp]
  field_simp

theorem regularizedSlowSolution_shift_relation (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 < x.re) :
    x * (q + 1) * regularizedSlowSolution (q + 2) (m + 2) x +
      (x - (m : ℂ)) * regularizedSlowSolution (q + 1) (m + 1) x -
        regularizedSlowSolution q m x = 0 := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hq' : 0 < (q + 1).re := by change 0 < q.re + 1; linarith
  have hq'' : 0 < (q + 2).re := by change 0 < q.re + 2; linarith
  rw [regularizedSlowSolution_contiguous q m x hq hx.le hx0,
    regularizedSlowSolution_eq_euler_complex (q + 2) (m + 2) x hq'' hx,
    regularizedSlowSolution_eq_euler_complex (q + 1) (m + 1) x hq' hx,
    regularizedSlowSolution_eq_euler_complex (q + 1) m x hq' hx]
  have h := slowEulerIntegral_contiguous (q + 1) m x hq' hx
  have hqq : q + 1 + 1 = q + 2 := by ring
  rw [hqq] at h
  have hg := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (q + 1)
  rw [hqq] at hg
  linear_combination (Complex.Gamma (q + 1))⁻¹ * h -
    x * slowEulerIntegral (q + 2) (m + 2) x * hg

/-- Kummer's equation for the defining regularized integral throughout
`Re(q)>-1`, with positive spatial real part. -/
theorem regularizedSlowSolution_kummer_equation (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 < x.re) :
    x * deriv (deriv (regularizedSlowSolution q m)) x +
      ((m : ℂ) - x) * deriv (regularizedSlowSolution q m) x -
        q * regularizedSlowSolution q m x = 0 := by
  rw [(hasDerivAt_deriv_regularizedSlowSolution q m x hq hx).deriv,
    (hasDerivAt_regularizedSlowSolution_shift q m x hq hx).deriv]
  linear_combination q * regularizedSlowSolution_shift_relation q m x hq hx

end DefocusingNLS

end OAI
