import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVelocityBounds

namespace OAI

/-! The actual radial velocity obeys the amplitude-divergence equation. -/

namespace DefocusingNLS

noncomputable def radialVelocity (c : ℝ) (A : ℝ → ℝ) (r : ℝ) : ℝ :=
  r*radialVelocityRatio c A r

theorem radialVelocity_origin (c : ℝ) (A : ℝ → ℝ) : radialVelocity c A 0=0 := by
  simp only [radialVelocity,zero_mul]

theorem radialVelocity_hasDerivAt (c : ℝ) (A : ℝ → ℝ) (hA : Differentiable ℝ A)
    (r : ℝ) (hr : r ≠ 0) (hAr : A r ≠ 0) :
    HasDerivAt (radialVelocity c A)
      (c-11*radialVelocityRatio c A r-2*radialVelocity c A r*deriv A r/A r) r := by
  have hav := hasDerivAt_radialAverage (fun t => (A t)^2) (hA.continuous.pow 2) r hr
  have hn := (hasDerivAt_id r).mul (hav.const_mul c)
  have hd := (hA r).hasDerivAt.pow 2
  convert! hn.div hd (pow_ne_zero 2 hAr) using 1
  · funext t
    simp only [radialVelocity,radialVelocityRatio,Pi.mul_apply,Pi.div_apply,Pi.pow_apply,id_eq]
    ring
  · simp only [radialVelocity,radialVelocityRatio,Pi.mul_apply,Pi.pow_apply,id_eq,
      one_mul,Nat.cast_ofNat,Nat.reduceSub,pow_one]
    field_simp [hr,hAr]
    ring

theorem radialVelocity_divergence_identity (c : ℝ) (A : ℝ → ℝ) (hA : Differentiable ℝ A)
    (r : ℝ) (hr : r ≠ 0) (hAr : A r ≠ 0) :
    deriv (fun t => (A t)^2*radialVelocity c A t) r+
      11/r*((A r)^2*radialVelocity c A r)=c*(A r)^2 := by
  have hd := ((hA r).hasDerivAt.pow 2).mul (radialVelocity_hasDerivAt c A hA r hr hAr)
  have he := hd.deriv
  change deriv (fun t => (A t)^2*radialVelocity c A t) r= _ at he
  rw [he]
  unfold radialVelocity radialVelocityRatio
  norm_num
  field_simp [hr,hAr]
  ring

end DefocusingNLS

end OAI
