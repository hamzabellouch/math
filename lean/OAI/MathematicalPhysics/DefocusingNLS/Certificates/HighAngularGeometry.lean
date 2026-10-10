import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularContour

namespace OAI

/-! The complex kinetic coefficient of the two actual contour pieces. -/

namespace DefocusingNLS

noncomputable def highRayN (Z t : ℝ) : ℝ :=
  (3960*highRayU t-9401*highRayV Z t)/10201

private theorem inv_eq_star_of_normSq (z : ℂ) (hz : Complex.normSq z = 1) : z⁻¹=star z := by
  apply Complex.inv_eq_conj
  rw [Complex.normSq_eq_norm_sq] at hz
  nlinarith [norm_nonneg z]

theorem highArc_kinetic_coefficient (Z h t : ℝ) (hh : h=1 ∨ h= -1) :
    highArcPoint Z h t/(highArcTangent h t)^2 =
      (highArcL Z (2*t) : ℂ)+Complex.I*(h*highArcN Z (2*t) : ℝ) := by
  rw [div_eq_mul_inv,← inv_pow,inv_eq_star_of_normSq _ (highArcTangent_normSq h t hh)]
  rcases hh with rfl | rfl <;> apply Complex.ext <;>
    simp only [highArcPoint,highArcTangent,highArcL,highArcN,Complex.add_re,
      Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
      pow_two,Complex.ofReal_re,Complex.ofReal_im,Complex.ofReal_mul,
      Complex.I_re,Complex.I_im,Complex.star_def,Complex.conj_re,Complex.conj_im] <;> ring

theorem highRay_kinetic_coefficient (Z h t : ℝ) (hh : h=1 ∨ h= -1) :
    highRayPoint Z h t/(highRayTangent h)^2 =
      (highRayL Z t : ℂ)+Complex.I*(h*highRayN Z t : ℝ) := by
  rw [div_eq_mul_inv,← inv_pow,inv_eq_star_of_normSq _ (highRayTangent_normSq h hh)]
  rcases hh with rfl | rfl <;> apply Complex.ext <;>
    norm_num [highRayPoint,highRayTangent,highRayL,highRayN,Complex.mul_re,
      Complex.mul_im,pow_two,Complex.star_def] <;> ring

theorem hasDerivAt_highArcTangent (h t : ℝ) (hh : h=1 ∨ h= -1) :
    HasDerivAt (highArcTangent h) (-Complex.I*(h*2 : ℝ)*highArcTangent h t) t := by
  have hc := (((hasDerivAt_id t).const_mul 2).cos).ofReal_comp
  have hs := ((((hasDerivAt_id t).const_mul 2).sin).const_mul h).ofReal_comp
  convert! hc.sub (hs.const_mul Complex.I) using 1
  rcases hh with rfl | rfl <;> apply Complex.ext <;>
    norm_num [highArcTangent,Complex.mul_re,Complex.mul_im] <;> ring

theorem highRayPoint_re (Z h t : ℝ) : (highRayPoint Z h t).re = highRayU t := by
  simp [highRayPoint]

theorem highArcPoint_re (Z h t : ℝ) : (highArcPoint Z h t).re = highArcU (2*t) := by
  simp [highArcPoint]

theorem highRayPoint_ne_zero (Z h t : ℝ) (ht : 0 ≤ t) : highRayPoint Z h t ≠ 0 := by
  intro hz
  have hr := congrArg Complex.re hz
  rw [highRayPoint_re] at hr
  simp only [Complex.zero_re] at hr
  dsimp [highRayU] at hr
  linarith

theorem highArcPoint_ne_zero (Z h t : ℝ) (hh : h=1 ∨ h= -1)
    (hZ : 2704/1000 ≤ Z) (ht : 0 ≤ 2*t) (ht' : 2*t ≤ highArcAngle) :
    highArcPoint Z h t ≠ 0 := by
  have hv := (highArc_geometry Z (2*t) hZ ht ht').2.1
  intro hz
  have hi := congrArg Complex.im hz
  rcases hh with rfl | rfl <;> simp [highArcPoint] at hi <;> linarith

end DefocusingNLS

end OAI
