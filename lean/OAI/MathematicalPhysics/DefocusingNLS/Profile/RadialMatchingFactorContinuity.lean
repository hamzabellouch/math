import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeMatchingWronskian

namespace OAI

/-! Continuity of the nonzero Wronskian normalization on the certified disk. -/

namespace DefocusingNLS

theorem continuous_radialShootingRaw_radius :
    Continuous (fun w : RadialShootingDisk =>
      radialFreeRaw (radialShootingB w) (radialShootingR w)) := by
  have hp : Continuous (fun w : RadialShootingDisk => (radialShootingB w,radialShootingZ w)) := by
    unfold radialShootingB radialShootingZ
    fun_prop
  have hm (w : RadialShootingDisk) : (radialShootingB w,radialShootingZ w) ∈ freeParameterRectangle := by
    have hb := (radialShooting_geometry w).1
    have hz := (ProfileCertificate.disk_coordinates w).2
    dsimp [freeParameterRectangle,radialShootingZ]
    norm_num [ProfileCertificate.centerZ,ProfileCertificate.radius] at hz ⊢
    exact ⟨by rw [abs_of_pos (by linarith [hb.1])]; linarith [hb.2],
      by linarith [(abs_le.mp hz).1],by linarith [(abs_le.mp hz).2]⟩
  have h := (continuousOn_free_regularizedSlowSolution 0 (by norm_num) 6).comp_continuous hp hm
  have he (w : RadialShootingDisk) : (radialShootingR w)^2/4=radialShootingZ w :=
    freeProfileRadius_sq (by have hh := (hm w).2.1; linarith)
  simpa only [Function.comp_def,radialFreeRaw,freeRadialArgument,he,freeShiftedQ,freeSpatialArgument,
    Complex.ofReal_zero,zero_sub,neg_mul] using! h

theorem continuous_radialShootingRaw_boundary :
    Continuous (fun w : RadialShootingDisk =>
      radialFreeRaw (radialShootingB w) innerBoundaryRadius) := by
  have hp : Continuous (fun w : RadialShootingDisk =>
      (radialShootingB w,innerBoundaryRadius^2/4)) := by
    unfold radialShootingB
    fun_prop
  have hm (w : RadialShootingDisk) :
      (radialShootingB w,innerBoundaryRadius^2/4) ∈ freeParameterRectangle := by
    have hb := (radialShooting_geometry w).1
    have hl : (3 : ℝ) ≤ innerBoundaryRadius :=
      (radialShooting_geometry w).2.1.trans (radialShooting_geometry w).2.2.2.1
    have hu := (radialShooting_geometry w).2.2.1
    exact ⟨by rw [abs_of_pos (by linarith [hb.1])]; linarith [hb.2],
      by nlinarith,by nlinarith⟩
  have h := (continuousOn_free_regularizedSlowSolution 0 (by norm_num) 6).comp_continuous hp hm
  simpa only [Function.comp_def,radialFreeRaw,freeRadialArgument,freeShiftedQ,freeSpatialArgument,
    Complex.ofReal_zero,zero_sub,neg_mul] using! h

theorem continuous_radialFreeMatchingFactor : Continuous radialFreeMatchingFactor := by
  have hR : Continuous radialShootingR := by unfold radialShootingR radialShootingZ; fun_prop
  have hnum : Continuous (fun w : RadialShootingDisk =>
      -((radialShootingR w)^11 : ℝ)*Complex.exp (Complex.I*((radialShootingR w)^2/4 : ℝ))*
        (Complex.I*(radialShootingR w/2 : ℝ))*radialFreeRaw (radialShootingB w) (radialShootingR w)) := by
    apply Continuous.mul _ continuous_radialShootingRaw_radius
    fun_prop
  have hden : Continuous (fun w : RadialShootingDisk =>
      (((innerBoundaryRadius^11 : ℝ) : ℂ)*Complex.exp (Complex.I*(innerBoundaryRadius^2/4 : ℝ)))*
        (radialFreeInnerJet w innerBoundaryRadius).1*radialFreeRaw (radialShootingB w) innerBoundaryRadius) :=
    ((continuous_const.mul continuous_radialFreeInner_boundary.fst).mul
    continuous_radialShootingRaw_boundary)
  exact hnum.div hden (fun w => mul_ne_zero
    (mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr
      (pow_ne_zero _ (by linarith [innerBoundaryRadius_bounds.1]))) (Complex.exp_ne_zero _))
        (radialFreeInner_boundary_ne_zero w))
    (radialShootingRaw_ne_zero w _ (radialShooting_geometry w).2.2.2.1))

end DefocusingNLS

end OAI
