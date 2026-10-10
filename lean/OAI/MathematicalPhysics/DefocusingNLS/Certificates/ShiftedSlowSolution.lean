import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowHigherDerivatives

namespace OAI

/-! # The translated slow solution used in the Laguerre calculation -/

namespace DefocusingNLS

noncomputable def shiftedSlowSolution (q : ℂ) (m : ℕ) (s : ℂ) (t : ℝ) : ℂ :=
  regularizedSlowSolution q m ((t : ℂ) - s)

theorem shifted_argument_mem_slitPlane (s : ℂ) (hs : s.im ≠ 0) (t : ℝ) :
    (t : ℂ) - s ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  right
  simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub, ne_eq, neg_eq_zero] using hs

theorem hasDerivAt_shiftedSlowSolution (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hs : s.im ≠ 0) (t : ℝ) :
    HasDerivAt (shiftedSlowSolution q m s)
      (deriv (regularizedSlowSolution q m) ((t : ℂ) - s)) t := by
  have hh := (analyticOnNhd_regularizedSlowSolution_slit q m hq
    _ (shifted_argument_mem_slitPlane s hs t)).differentiableAt.hasDerivAt
  have h := (hh.comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).sub_const s)).comp_ofReal
  convert! h using 1
  all_goals simp only [mul_one]

theorem hasDerivAt_deriv_shiftedSlowSolution (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hs : s.im ≠ 0) (t : ℝ) :
    HasDerivAt (deriv (shiftedSlowSolution q m s))
      (deriv (deriv (regularizedSlowSolution q m)) ((t : ℂ) - s)) t := by
  have he : deriv (shiftedSlowSolution q m s) =
      (fun u : ℝ => deriv (regularizedSlowSolution q m) ((u : ℂ) - s)) :=
    funext fun u => (hasDerivAt_shiftedSlowSolution q m s hq hs u).deriv
  rw [he]
  have hh := ((analyticOnNhd_regularizedSlowSolution_slit q m hq).deriv
    _ (shifted_argument_mem_slitPlane s hs t)).differentiableAt.hasDerivAt
  have h := (hh.comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).sub_const s)).comp_ofReal
  convert! h using 1
  all_goals simp only [mul_one]

/-- This is the equation projected onto Laguerre polynomials in the paper. -/
theorem shiftedSlowSolution_laguerre_equation (q : ℂ) (M : ℕ) (s : ℂ) (t : ℝ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) (ht : 0 ≤ t) :
    (t : ℂ) * deriv (deriv (shiftedSlowSolution q (M + 1) s)) t +
      (1 - (t : ℂ)) * deriv (shiftedSlowSolution q (M + 1) s) t +
      (M : ℂ) * deriv (shiftedSlowSolution q (M + 1) s) t -
      s * (deriv (deriv (shiftedSlowSolution q (M + 1) s)) t -
        deriv (shiftedSlowSolution q (M + 1) s) t) -
      q * shiftedSlowSolution q (M + 1) s t = 0 := by
  have hx : 0 ≤ ((t : ℂ) - s).re := by simpa [hsre] using ht
  have hx0 := Complex.slitPlane_ne_zero (shifted_argument_mem_slitPlane s hsim t)
  rw [(hasDerivAt_deriv_shiftedSlowSolution q (M + 1) s hq hsim t).deriv,
    (hasDerivAt_shiftedSlowSolution q (M + 1) s hq hsim t).deriv]
  have h := regularizedSlowSolution_kummer_equation_closed q (M + 1) ((t : ℂ) - s) hq hx hx0
  simp only [Nat.cast_add, Nat.cast_one] at h
  unfold shiftedSlowSolution
  linear_combination h

end DefocusingNLS

end OAI
