import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVelocityEquation

namespace OAI

/-! Local velocity differentiation, allowing a merely continuous extension outside the ball. -/

namespace DefocusingNLS

theorem radialVelocity_hasDerivAt_local (c d : ℝ) (A : ℝ → ℝ) (hA : Continuous A)
    (r : ℝ) (hr : r ≠ 0) (hAr : A r ≠ 0) (hd : HasDerivAt A d r) :
    HasDerivAt (radialVelocity c A)
      (c-11*radialVelocityRatio c A r-2*radialVelocity c A r*d/A r) r := by
  have hav := hasDerivAt_radialAverage (fun t => (A t)^2) (hA.pow 2) r hr
  have hn := (hasDerivAt_id r).mul (hav.const_mul c)
  have hden := hd.pow 2
  convert! hn.div hden (pow_ne_zero 2 hAr) using 1
  · funext t
    simp only [radialVelocity,radialVelocityRatio,Pi.mul_apply,Pi.div_apply,Pi.pow_apply,id_eq]
    ring
  · simp only [radialVelocity,radialVelocityRatio,Pi.mul_apply,Pi.pow_apply,id_eq,
      one_mul,Nat.cast_ofNat,Nat.reduceSub,pow_one]
    field_simp [hr,hAr]
    ring

end DefocusingNLS

end OAI
