import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularArcFluxSign
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularBoundaryFlux
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.FreeMatching

namespace OAI

/-! The actual initial flux is a scaled cone form of the ungauged boundary jet. -/

namespace DefocusingNLS

theorem highArcActualFlux_initial (q : ℂ) (M : ℕ) (Z h : ℝ)
    (hq : -1 < q.re) (hh : h=1 ∨ h= -1) (hZ : 2704/1000 ≤ Z) :
    let x : ℂ := -Complex.I*(h*Z : ℝ)
    highArcActualFlux q M Z h 0 = Complex.normSq (slowGauge M x)*
      coneForm ((M : ℝ)-2*Z) x (regularizedSlowSolution q (M+1) x)
        (deriv (regularizedSlowSolution q (M+1)) x) := by
  intro x
  have hx : x.re=0 := by simp [x]
  have hx0 : x ≠ 0 := by
    intro hz
    have hi := congrArg Complex.im hz
    rcases hh with rfl | rfl <;> norm_num [x] at hi <;> linarith
  have hpoint : highArcPoint Z h 0=x := by
    simp [highArcPoint,highArcU,highArcV,x]
    ring
  have htangent : highArcTangent h 0=1 := by simp [highArcTangent]
  have hcorrection : highArcCorrection Z 0= -Z := by
    simp [highArcCorrection,highArcL,highArcN,highArcU,highArcV]
  unfold highArcActualFlux highAngularFlux
  dsimp only
  rw [highArcWave_deriv q M Z h 0 hq hh hZ (by norm_num)
      (by simpa only [mul_zero,highArcAngle] using Real.arccos_nonneg (99/101 : ℝ)),hpoint,htangent,hcorrection]
  simp only [one_pow,div_one,one_mul]
  dsimp only [highArcWave]
  rw [hpoint,(hasDerivAt_gaugedSlowSolution q M x hq hx.ge hx0).deriv]
  unfold gaugedSlowSolution
  rw [gaugedFlux_at_imaginary_boundary x (slowGauge M x)
    (regularizedSlowSolution q (M+1) x) (deriv (regularizedSlowSolution q (M+1)) x) M hx hx0,
    Complex.normSq_mul]
  dsimp only [coneForm]
  ring

theorem conjugate_boundary_gauge_normSq (M : ℕ) (Z : ℝ) :
    Complex.normSq (slowGauge M (-Complex.I*(Z : ℂ))) =
      Complex.normSq (slowGauge M (Complex.I*(Z : ℂ))) := by
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,
    slowGauge_norm,slowGauge_norm]
  simp only [Complex.neg_re,Complex.mul_re,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,neg_zero,
    zero_div,Real.exp_zero,one_mul,neg_mul,norm_neg]

end DefocusingNLS

end OAI
