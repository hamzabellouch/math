import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedAmplitude

namespace OAI

/-! The real amplitude equation of the actual stationary matched profile. -/

open Set Filter
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem complexAmplitude_first_derivative (Q : ℝ → ℂ) (r : ℝ)
    (hQ : DifferentiableAt ℝ Q r) (hn : Q r ≠ 0) :
    ‖Q r‖*deriv (fun t => ‖Q t‖) r=(star (Q r)*deriv Q r).re := by
  have hA := hQ.norm ℂ hn
  have hh := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r
    (hQ.hasDerivAt.star.mul hQ.hasDerivAt)
  have hμ : HasDerivAt (fun t => ‖Q t‖^2)
      (2*(star (Q r)*deriv Q r).re) r := by
    convert hh using 1
    · funext t
      simp [Complex.sq_norm,Complex.normSq_apply,Complex.mul_re]
    · simp only [Complex.reCLM_apply,Complex.add_re,Complex.mul_re,
        Complex.star_def,Complex.conj_re,Complex.conj_im]
      ring
  have he := (hA.hasDerivAt.pow 2).unique hμ
  norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one] at he
  linarith

theorem radial_amplitude_balance (A d dd w r b P R J N U : ℝ) (hA : A ≠ 0)
    (hfirst : A*d=R) (hsecond : d^2+A*dd=N+U)
    (hgeom : R^2+J^2=A^2*N)
    (hODE : U+11/r*R-r/2*J+b*A^2=P*A^2)
    (hw : w=r/2+2*J/A^2) :
    -dd-11/r*d+P*A=(b+r^2/16-w^2/4)*A := by
  have hw2 : A^4*w^2=r^2/4*A^4+2*r*J*A^2+4*J^2 := by
    rw [hw]
    field_simp [hA]
    ring
  have hD : A^3*(-dd-11/r*d+P*A-(b+r^2/16-w^2/4)*A)=0 := by
    linear_combination -A^2*hsecond+hgeom+(R+A*d-11/r*A^2)*hfirst-A^2*hODE+hw2/4
  have he := (mul_eq_zero.mp hD).resolve_left (pow_ne_zero 3 hA)
  linarith

theorem radialMatchedAmplitude_second_identity (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : 0 < r) :
    let Q := radialMatchedProfile n z
    let A := fun t => ‖Q t‖
    (deriv A r)^2+A r*deriv (deriv A) r=
      Complex.normSq (deriv Q r)+(star (Q r)*deriv (deriv Q) r).re := by
  dsimp only
  have hQ := ((radialMatchedProfile_contDiffOn n z hX hz) r hr).contDiffAt
    (Ioi_mem_nhds hr)
  have hA := ((radialMatchedAmplitude_contDiffOn n z hX hz) r hr).contDiffAt
    (Ioi_mem_nhds hr)
  have hQA := hQ.differentiableAt (by simp)
  have hQD := (hQ.derivWithin (m := 1) (by simp)).differentiableAt (by simp)
  have hAA := hA.differentiableAt (by simp)
  have hAD := (hA.derivWithin (m := 1) (by simp)).differentiableAt (by simp)
  have hleft := hAA.hasDerivAt.mul hAD.hasDerivAt
  have hright := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r
    (hQA.hasDerivAt.star.mul hQD.hasDerivAt)
  have he : (fun t => ‖radialMatchedProfile n z t‖*
      deriv (fun s => ‖radialMatchedProfile n z s‖) t) =ᶠ[nhds r]
      (fun t => (star (radialMatchedProfile n z t)*deriv (radialMatchedProfile n z) t).re) := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact complexAmplitude_first_derivative _ t
      (radialMatchedProfile_differentiable n z hX hz t)
      (radialMatchedProfile_ne_zero n z hX t ht.le)
  have hh := hleft.unique (hright.congr_of_eventuallyEq he)
  simpa only [Complex.reCLM_apply,Complex.add_re,Complex.mul_re,Complex.star_def,
    Complex.conj_re,Complex.conj_im,Complex.normSq_apply,pow_two,neg_mul,sub_neg_eq_add] using hh

theorem radialMatchedAmplitude_stationary (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : 0 < r) :
    let A := fun t => ‖radialMatchedProfile n z t‖;
    -deriv (deriv A) r-11/r*deriv A r+(A r)^(2*(n+radialInnerShootingThreshold))*A r=
      radialAmplitudePotential (6-2*radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) A r*A r := by
  let Q := radialMatchedProfile n z
  let A := fun t => ‖Q t‖
  let R := (star (Q r)*deriv Q r).re
  let J := (star (Q r)*deriv Q r).im
  have hgeom : R^2+J^2=(A r)^2*Complex.normSq (deriv Q r) := by
    calc
      _ = Complex.normSq (star (Q r)*deriv Q r) := by
        simp only [R,J,Complex.normSq_apply,pow_two]
      _ = _ := by
        rw [Complex.normSq_eq_norm_sq,norm_mul,norm_star,mul_pow]
        change ‖Q r‖^2*‖deriv Q r‖^2=‖Q r‖^2*Complex.normSq (deriv Q r)
        rw [Complex.sq_norm (deriv Q r)]
  have hODE := congrArg Complex.re
    (congrArg (fun v : ℂ => star (Q r)*v) (radialMatchedProfile_stationary n z hX hz r hr))
  rw [oddPowerNonlinearity_eq] at hODE
  have hreal : (star (Q r)*deriv (deriv Q) r).re+11/r*R-r/2*J+
      radialShootingB (profileMatchingParameter z)*(A r)^2=
        (A r)^(2*(n+radialInnerShootingThreshold))*(A r)^2 := by
    dsimp only [R,J,A,Q]
    simp only [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
      Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add,add_zero,sub_zero,zero_sub] at hODE
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,
      Complex.star_def,Complex.conj_re,Complex.conj_im]
    nlinarith [hODE]
  have hbalance := radial_amplitude_balance (A r) (deriv A r) (deriv (deriv A) r)
    (radialVelocity (6-2*radialShootingA n) A r) r
    (radialShootingB (profileMatchingParameter z))
    ((A r)^(2*(n+radialInnerShootingThreshold))) R J
    (Complex.normSq (deriv Q r)) (star (Q r)*deriv (deriv Q) r).re
    (norm_ne_zero_iff.mpr (radialMatchedProfile_ne_zero n z hX r hr.le))
    (complexAmplitude_first_derivative Q r (radialMatchedProfile_differentiable n z hX hz r)
      (radialMatchedProfile_ne_zero n z hX r hr.le))
    (radialMatchedAmplitude_second_identity n z hX hz r hr) hgeom hreal (by
      simpa only [J,A,Q,Complex.sq_norm] using (radialMatchedVelocity_formula n z hX hz r hr).symm)
  dsimp only [radialAmplitudePotential,radialVelocity] at hbalance ⊢
  convert hbalance using 1
  ring

end DefocusingNLS

end OAI
