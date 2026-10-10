import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularGeometry

namespace OAI

/-! Derivatives of the kinetic coefficient and of its real and imaginary parts. -/

namespace DefocusingNLS

theorem hasDerivAt_kineticCoefficient (γ g : ℝ → ℂ) (t : ℝ) (C : ℂ)
    (hγ : HasDerivAt γ (g t) t) (hg : HasDerivAt g (-C*g t) t) (hg0 : g t ≠ 0) :
    HasDerivAt (fun s => γ s/(g s)^2)
      (1/g t+2*C*(γ t/(g t)^2)) t := by
  convert! hγ.div (hg.pow 2) (pow_ne_zero 2 hg0) using 1
  simp only [Pi.pow_apply]
  field_simp [hg0]
  ring

theorem hasDerivAt_highArcKinetic (Z h t : ℝ) (hh : h=1 ∨ h= -1) :
    HasDerivAt (fun s => highArcPoint Z h s/(highArcTangent h s)^2)
      ((Real.cos (2*t)-4*highArcN Z (2*t) : ℝ)+
        Complex.I*(h*(Real.sin (2*t)+4*highArcL Z (2*t)) : ℝ)) t := by
  have hn := highArcTangent_normSq h t hh
  have hg0 : highArcTangent h t ≠ 0 := by
    intro hz
    rw [hz,Complex.normSq_zero] at hn
    norm_num at hn
  have hd := hasDerivAt_kineticCoefficient (highArcPoint Z h) (highArcTangent h) t
    (Complex.I*(h*2 : ℝ)) (hasDerivAt_highArcPoint Z h t)
    (by convert! hasDerivAt_highArcTangent h t hh using 1; ring) hg0
  convert! hd using 1
  rw [highArc_kinetic_coefficient Z h t hh,one_div]
  have hinv : (highArcTangent h t)⁻¹=star (highArcTangent h t) := by
    apply Complex.inv_eq_conj
    rw [Complex.normSq_eq_norm_sq] at hn
    nlinarith [norm_nonneg (highArcTangent h t)]
  rw [hinv]
  rcases hh with rfl | rfl <;> apply Complex.ext <;>
    simp only [highArcTangent,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,Complex.star_def,Complex.conj_re,Complex.conj_im] <;> norm_num <;> ring

theorem hasDerivAt_highRayKinetic (Z h t : ℝ) (hh : h=1 ∨ h= -1) :
    HasDerivAt (fun s => highRayPoint Z h s/(highRayTangent h)^2)
      ((99/101 : ℂ)+Complex.I*(h*(20/101) : ℝ)) t := by
  have hn := highRayTangent_normSq h hh
  have hg0 : highRayTangent h ≠ 0 := by
    intro hz
    rw [hz,Complex.normSq_zero] at hn
    norm_num at hn
  have hd := (hasDerivAt_highRayPoint Z h t).div_const ((highRayTangent h)^2)
  convert! hd using 1
  have hinv : (highRayTangent h)⁻¹=star (highRayTangent h) := by
    apply Complex.inv_eq_conj
    rw [Complex.normSq_eq_norm_sq] at hn
    nlinarith [norm_nonneg (highRayTangent h)]
  have hdiv : highRayTangent h/(highRayTangent h)^2=(highRayTangent h)⁻¹ := by
    field_simp
  rw [hdiv,hinv]
  simp [highRayTangent]

theorem hasDerivAt_highArcL (Z t : ℝ) :
    HasDerivAt (fun s => highArcL Z (2*s))
      (Real.cos (2*t)-4*highArcN Z (2*t)) t := by
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_highArcKinetic Z 1 t (Or.inl rfl))
  convert! hd using 1
  · ext s
    change highArcL Z (2*s) = (highArcPoint Z 1 s/(highArcTangent 1 s)^2).re
    rw [highArc_kinetic_coefficient Z 1 s (Or.inl rfl)]
    simp
  · simp only [Complex.reCLM_apply,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im]
    ring

theorem hasDerivAt_highArcN (Z t : ℝ) :
    HasDerivAt (fun s => highArcN Z (2*s))
      (Real.sin (2*t)+4*highArcL Z (2*t)) t := by
  have hd := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_highArcKinetic Z 1 t (Or.inl rfl))
  convert! hd using 1
  · ext s
    change highArcN Z (2*s) = (highArcPoint Z 1 s/(highArcTangent 1 s)^2).im
    rw [highArc_kinetic_coefficient Z 1 s (Or.inl rfl)]
    simp
  · simp only [Complex.imCLM_apply,Complex.add_im,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im]
    ring

end DefocusingNLS

end OAI
