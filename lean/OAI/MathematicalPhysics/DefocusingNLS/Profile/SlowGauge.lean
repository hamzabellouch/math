import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowBoundaryEquation

namespace OAI

/-! The gauge used in the high-angular multiplier identity. -/

namespace DefocusingNLS

noncomputable def slowGauge (M : ℕ) (x : ℂ) : ℂ :=
  Complex.exp (-x/2)*x^((M : ℂ)/2)

noncomputable def gaugedSlowSolution (q : ℂ) (M : ℕ) (x : ℂ) : ℂ :=
  slowGauge M x*regularizedSlowSolution q (M+1) x

theorem hasDerivAt_slowGauge (M : ℕ) (x : ℂ) (hx : x ∈ Complex.slitPlane) :
    HasDerivAt (slowGauge M) (((M : ℂ)/(2*x)-1/2)*slowGauge M x) x := by
  have hx0 := Complex.slitPlane_ne_zero hx
  have he := (((hasDerivAt_id x).neg).div_const 2).cexp
  have hp := (hasDerivAt_id x).cpow_const (c := (M : ℂ)/2) hx
  convert! he.mul hp using 1
  simp only [slowGauge,Pi.neg_apply,id_eq,mul_one]
  rw [Complex.cpow_sub _ _ hx0,Complex.cpow_one]
  field_simp [hx0]
  ring

theorem hasDerivAt_gaugedSlowSolution (q : ℂ) (M : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    HasDerivAt (gaugedSlowSolution q M)
      (slowGauge M x*(deriv (regularizedSlowSolution q (M+1)) x+
        ((M : ℂ)/(2*x)-1/2)*regularizedSlowSolution q (M+1) x)) x := by
  have hslit : x ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    rcases hx.eq_or_lt with he | he
    · right
      intro hi
      exact hx0 (Complex.ext he.symm hi)
    · exact Or.inl he
  have hH := (hasDerivAt_regularizedSlowSolution_shift_closed q (M+1) x hq hx hx0)
  have hd := (hasDerivAt_slowGauge M x hslit).mul hH
  rw [← hH.deriv] at hd
  convert! hd using 1
  · ring

end DefocusingNLS

end OAI
