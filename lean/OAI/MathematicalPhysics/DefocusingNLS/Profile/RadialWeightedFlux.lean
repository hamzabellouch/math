import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedSmooth
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexFlux

namespace OAI

/-! The exact weighted velocity divergence identity for the true stationary profile. -/

namespace DefocusingNLS
open ProfileCertificate
open Set
open scoped ContDiff

noncomputable def radialWeightedFlux (Q : ℝ → ℂ) (r : ℝ) : ℝ :=
  r/2*Complex.normSq (Q r)+2*(star (Q r)*deriv Q r).im

theorem radialWeightedFlux_hasDerivAt (m : ℕ) (a b r : ℝ) (hr : r ≠ 0)
    (Q : ℝ → ℂ) (hQ : DifferentiableAt ℝ Q r)
    (hD : DifferentiableAt ℝ (deriv Q) r)
    (hEq : deriv (deriv Q) r+(11/r : ℝ)*deriv Q r+
      Complex.I*((r/2 : ℝ)*deriv Q r+(a : ℂ)*Q r)+(b : ℂ)*Q r=
        oddPowerNonlinearity m (Q r)) :
    HasDerivAt (radialWeightedFlux Q)
      ((6-2*a)*Complex.normSq (Q r)-11/r*radialWeightedFlux Q r) r := by
  have hμ : HasDerivAt (fun t => Complex.normSq (Q t))
      (2*(star (Q r)*deriv Q r).re) r := by
    have hh := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r
      (hQ.hasDerivAt.star.mul hQ.hasDerivAt)
    convert hh using 1
    · funext t
      simp [Complex.normSq_apply,Complex.mul_re]
    · simp [Complex.mul_re]
      ring
  have hJ := Complex.imCLM.hasFDerivAt.comp_hasDerivAt r
    (hQ.hasDerivAt.star.mul hD.hasDerivAt)
  have hF := (((hasDerivAt_id r).div_const 2).mul hμ).add (hJ.const_mul 2)
  change HasDerivAt (radialWeightedFlux Q) _ r at hF
  apply hF.congr_deriv
  have hi := congrArg Complex.im (congrArg (fun z : ℂ => star (Q r)*z) hEq)
  rw [oddPowerNonlinearity_eq] at hi
  simp only [Complex.mul_im,Complex.mul_re,Complex.add_re,Complex.add_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add,add_zero,sub_zero,zero_sub] at hi
  simp only [radialWeightedFlux,Complex.normSq_apply,Complex.imCLM_apply,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im,id_eq]
  field_simp [hr] at hi ⊢
  nlinarith [hi]

theorem radialMatchedWeightedFlux_hasDerivAt (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (radialWeightedFlux (radialMatchedProfile n z))
      ((6-2*radialShootingA n)*Complex.normSq (radialMatchedProfile n z r)-
        11/r*radialWeightedFlux (radialMatchedProfile n z) r) r := by
  have hs := ((radialMatchedProfile_contDiffOn n z hX hz) r hr).contDiffAt
    (Ioi_mem_nhds hr)
  apply radialWeightedFlux_hasDerivAt (n+radialInnerShootingThreshold)
    (radialShootingA n) (radialShootingB (profileMatchingParameter z)) r hr.ne' _
    (hs.differentiableAt (by simp))
    ((hs.derivWithin (m := 1) (by simp)).differentiableAt (by simp))
  exact radialMatchedProfile_stationary n z hX hz r hr

end DefocusingNLS

end OAI
