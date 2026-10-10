import OAI.MathematicalPhysics.DefocusingNLS.Profile.NormalizedSlowIdentification

namespace OAI

/-! # Adjacent spatial parameters and the first normalized tail value -/

open MeasureTheory Set

namespace DefocusingNLS

theorem regularizedSlowSolution_adjacent_interior (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 < x.re) :
    regularizedSlowSolution q (m + 1) x = regularizedSlowSolution q m x +
      q * regularizedSlowSolution (q + 1) (m + 1) x := by
  have hq' : 0 < (q + 1).re := by change 0 < q.re + 1; linarith
  rw [regularizedSlowSolution_eq_euler_complex q (m + 1) x hq hx,
    regularizedSlowSolution_eq_euler_complex q m x hq hx,
    regularizedSlowSolution_eq_euler_complex (q + 1) (m + 1) x hq' hx,
    slowEulerIntegral_adjacent q m x hq hx]
  have hg := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one q
  linear_combination slowEulerIntegral (q + 1) (m + 1) x * hg

theorem regularizedSlowSolution_adjacent (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    regularizedSlowSolution q (m + 1) x = regularizedSlowSolution q m x +
      q * regularizedSlowSolution (q + 1) (m + 1) x := by
  rcases hx.eq_or_lt with hx | hx
  · have hxim : x.im ≠ 0 := by
      intro hi
      exact hx0 (Complex.ext hx.symm hi)
    have hslit : x ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr hxim)
    have hq' : -1 < (q + 1).re := by change -1 < q.re + 1; linarith
    have hc₀ := (analyticOnNhd_regularizedSlowSolution_slit q (m + 1)
      (by linarith) x hslit).continuousAt
    have hc₁ := (analyticOnNhd_regularizedSlowSolution_slit q m
      (by linarith) x hslit).continuousAt
    have hc₂ := (analyticOnNhd_regularizedSlowSolution_slit (q + 1) (m + 1)
      hq' x hslit).continuousAt
    have he : regularizedSlowSolution q (m + 1) x -
        (regularizedSlowSolution q m x + q * regularizedSlowSolution (q + 1) (m + 1) x) = 0 := by
      apply eq_zero_on_imaginary_boundary hx.symm
      · exact hc₀.sub (hc₁.add (continuousAt_const.mul hc₂))
      · intro y hy
        exact sub_eq_zero.mpr (regularizedSlowSolution_adjacent_interior q m y hq hy)
    exact sub_eq_zero.mp he
  · exact regularizedSlowSolution_adjacent_interior q m x hq hx

theorem slowLaguerreCoefficient_zero (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : 0 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    slowLaguerreCoefficient q (m + 1) s 0 = regularizedSlowSolution q m (-s) := by
  have hq' : -1 < q.re := by linarith
  have hdiff := shiftedSlowDerivative_coefficient_step 0 0 q m s hq' hsre hsim
  have hi₀ := integrableOn_laguerreIntegrand_shiftedSlowDerivative 0 0 q m s hq' hsre hsim
  have hi₁ := integrableOn_laguerreIntegrand_shiftedSlowDerivative 1 0 q m s hq' hsre hsim
  have he : slowLaguerreCoefficient q (m + 1) s 0 =
      laguerreCoefficientIntegral (shiftedSlowDerivative 0 q m s) 0 -
        laguerreCoefficientIntegral (shiftedSlowDerivative 1 q m s) 0 := by
    unfold slowLaguerreCoefficient laguerreCoefficientIntegral
    rw [← integral_sub hi₀ hi₁]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hx : 0 < ((t : ℂ) - s).re := by simpa [hsre] using ht
    have ha := regularizedSlowSolution_adjacent_interior q m ((t : ℂ) - s) hq hx
    have hd := (hasDerivAt_regularizedSlowSolution_shift q m ((t : ℂ) - s) hq' hx).deriv
    simp only [laguerreIntegrand, shiftedSlowDerivative, iteratedDeriv_zero,
      iteratedDeriv_succ]
    rw [ha, hd]
    ring
  rw [he, hdiff]
  simp [shiftedSlowDerivative]

/-- The first normalized B entry is a boundary value, including when q=0. -/
theorem normalizedSlowB_one (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    normalizedSlowB q m s 1 = regularizedSlowSolution (q + 1) m (-s) := by
  have hq' : 0 < (q + 1).re := by change 0 < q.re + 1; linarith
  simpa only [normalizedSlowB, Nat.sub_self] using
    slowLaguerreCoefficient_zero (q + 1) m s hq' hsre hsim

end DefocusingNLS

end OAI
