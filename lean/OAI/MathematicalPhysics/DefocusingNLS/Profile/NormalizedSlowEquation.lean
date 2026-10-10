import OAI.MathematicalPhysics.DefocusingNLS.Profile.NormalizedSlowDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowBoundaryEquation

namespace OAI

/-! The differential equation for the actual normalized outgoing H solution. -/

namespace DefocusingNLS

noncomputable def normalizedSlowFirst (q : ℂ) (m : ℕ) (x : ℂ) : ℂ :=
  q*x^(q-1)*regularizedSlowSolution q m x+
    x^q*deriv (regularizedSlowSolution q m) x

theorem hasDerivAt_normalizedSlowFirst_value (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : x ∈ Complex.slitPlane) :
    HasDerivAt (normalizedSlowSolution q m) (normalizedSlowFirst q m x) x := by
  have hf := (analyticOnNhd_regularizedSlowSolution_slit q m hq x hx).differentiableAt.hasDerivAt
  convert ((hasDerivAt_id x).cpow_const (c := q) hx).mul hf using 1
  · rfl
  · simp only [normalizedSlowFirst,id_eq,mul_one]

theorem hasDerivAt_normalizedSlowFirst (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : x ∈ Complex.slitPlane) :
    HasDerivAt (normalizedSlowFirst q m)
      (q*(q-1)*x^(q-2)*regularizedSlowSolution q m x+
        2*q*x^(q-1)*deriv (regularizedSlowSolution q m) x+
        x^q*deriv (deriv (regularizedSlowSolution q m)) x) x := by
  have ha := analyticOnNhd_regularizedSlowSolution_slit q m hq
  have hf := (ha x hx).differentiableAt.hasDerivAt
  have hdf := (ha.deriv x hx).differentiableAt.hasDerivAt
  have hp := (hasDerivAt_id x).cpow_const (c := q) hx
  have hp1 := (hasDerivAt_id x).cpow_const (c := q-1) hx
  convert ((hp1.const_mul q).mul hf).add (hp.mul hdf) using 1
  · rfl
  · simp only [id_eq,mul_one]
    rw [show q-1-1=q-2 by ring]
    ring

theorem normalizedSlowFirst_eq_shift (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    normalizedSlowFirst q m x =
      -q*((m : ℂ)-1-q)/x^2*normalizedSlowSolution (q+1) m x := by
  have hs : x ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    rcases hx.eq_or_lt with h | h
    · right
      intro hi
      exact hx0 (Complex.ext h.symm hi)
    · exact Or.inl h
  exact (hasDerivAt_normalizedSlowFirst_value q m x hq hs).unique
    (hasDerivAt_normalizedSlowSolution q m x hq hx hx0)

theorem normalizedSlowSolution_equation (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    x^2*deriv (normalizedSlowFirst q m) x+
      (((m : ℂ)-2*q)*x-x^2)*normalizedSlowFirst q m x+
        q*(q+1-m)*normalizedSlowSolution q m x=0 := by
  have hs : x ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    rcases hx.eq_or_lt with h | h
    · right
      intro hi
      exact hx0 (Complex.ext h.symm hi)
    · exact Or.inl h
  rw [(hasDerivAt_normalizedSlowFirst q m x hq hs).deriv]
  have he1 : x^(q-1)*x=x^q := by
    calc
      _ = x^(q-1)*x^(1 : ℂ) := by rw [Complex.cpow_one]
      _ = x^((q-1)+1) := (Complex.cpow_add _ _ hx0).symm
      _ = _ := by congr 1; ring
  have he2 : x^(q-2)*x^2=x^q := by
    calc
      _ = x^(q-2)*x^(2 : ℂ) := by rw [Complex.cpow_two]
      _ = x^((q-2)+2) := (Complex.cpow_add _ _ hx0).symm
      _ = _ := by congr 1; ring
  have hK := regularizedSlowSolution_kummer_equation_closed q m x hq hx hx0
  dsimp only [normalizedSlowFirst,normalizedSlowSolution]
  calc
    _ = x^q*x*(x*deriv (deriv (regularizedSlowSolution q m)) x+
      ((m : ℂ)-x)*deriv (regularizedSlowSolution q m) x-q*regularizedSlowSolution q m x) := by
      linear_combination
        q*(q-1)*regularizedSlowSolution q m x*he2 +
        (q*((m : ℂ)-2*q)*regularizedSlowSolution q m x+
          2*q*x*deriv (regularizedSlowSolution q m) x)*he1 -
        q*regularizedSlowSolution q m x*he1*x
    _ = 0 := by rw [hK,mul_zero]

end DefocusingNLS

end OAI
