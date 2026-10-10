import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowGauge
import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowJetUniqueness

namespace OAI

/-! The actual gauged Kummer equation used in the high-angular multiplier proof. -/

open Filter Topology
namespace DefocusingNLS

private theorem gauged_hasDerivAt_slit (q : ℂ) (M : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : x ∈ Complex.slitPlane) :
    HasDerivAt (gaugedSlowSolution q M)
      (slowGauge M x*(deriv (regularizedSlowSolution q (M+1)) x+
        ((M : ℂ)/(2*x)-1/2)*regularizedSlowSolution q (M+1) x)) x := by
  have hH := ((analyticOnNhd_regularizedSlowSolution_slit q (M+1) hq) x hx).differentiableAt.hasDerivAt
  convert! (hasDerivAt_slowGauge M x hx).mul hH using 1
  · ring

theorem gaugedSlowSolution_equation (q : ℂ) (M : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    -x*deriv (deriv (gaugedSlowSolution q M)) x-deriv (gaugedSlowSolution q M) x+
      (x/4+(M : ℂ)^2/(4*x))*gaugedSlowSolution q M x =
      (((M : ℂ)+1)/2-q)*gaugedSlowSolution q M x := by
  have hs : x ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    rcases hx.eq_or_lt with he | he
    · exact Or.inr (fun hi => hx0 (Complex.ext he.symm hi))
    · exact Or.inl he
  let H := regularizedSlowSolution q (M+1)
  let G := slowGauge M
  let A : ℂ → ℂ := fun z => (M : ℂ)/(2*z)-1/2
  have hA : HasDerivAt A (-(M : ℂ)/(2*x^2)) x := by
    have h := ((hasDerivAt_const x (M : ℂ)).div
      ((hasDerivAt_id x).const_mul 2) (mul_ne_zero (by norm_num) hx0)).sub_const (1/2)
    simp only [id_eq] at h
    convert! h using 1
    field_simp [hx0]
    ring
  have hH := ((analyticOnNhd_regularizedSlowSolution_slit q (M+1) hq) x hs).differentiableAt.hasDerivAt
  have hH' := ((analyticOnNhd_regularizedSlowSolution_slit q (M+1) hq).deriv x hs).differentiableAt.hasDerivAt
  have hG := hasDerivAt_slowGauge M x hs
  have hF := hG.mul (hH'.add (hA.mul hH))
  have heq : deriv (gaugedSlowSolution q M) =ᶠ[𝓝 x]
      (fun z => G z*(deriv H z+A z*H z)) := by
    filter_upwards [Complex.isOpen_slitPlane.mem_nhds hs] with z hz
    exact (gauged_hasDerivAt_slit q M z hq hz).deriv
  have hD₂ := (hF.congr_of_eventuallyEq heq).deriv
  have hD₁ := (gauged_hasDerivAt_slit q M x hq hs).deriv
  rw [hD₂,hD₁]
  change -x*(A x*G x*(deriv H x+A x*H x)+
      G x*(deriv (deriv H) x+(-(M : ℂ)/(2*x^2)*H x+A x*deriv H x)))-
      G x*(deriv H x+A x*H x)+(x/4+(M : ℂ)^2/(4*x))*(G x*H x) =
      (((M : ℂ)+1)/2-q)*(G x*H x)
  have hODE := regularizedSlowSolution_kummer_equation_closed q (M+1) x hq hx hx0
  change x*deriv (deriv H) x+(((M+1 : ℕ) : ℂ)-x)*deriv H x-q*H x=0 at hODE
  push_cast at hODE
  have he : (-x*(A x*G x*(deriv H x+A x*H x)+
        G x*(deriv (deriv H) x+(-(M : ℂ)/(2*x^2)*H x+A x*deriv H x)))-
        G x*(deriv H x+A x*H x)+(x/4+(M : ℂ)^2/(4*x))*(G x*H x))-
        ((((M : ℂ)+1)/2-q)*(G x*H x)) =
      -G x*(x*deriv (deriv H) x+((M : ℂ)+1-x)*deriv H x-q*H x) := by
    dsimp only [A]
    field_simp [hx0]
    ring
  apply sub_eq_zero.mp
  rw [he,hODE,mul_zero]

end DefocusingNLS

end OAI
