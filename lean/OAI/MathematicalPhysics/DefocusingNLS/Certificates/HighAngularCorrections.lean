import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularKineticDerivative

namespace OAI

/-! The two correction terms in the actual high-angular boundary flux. -/

namespace DefocusingNLS

noncomputable def highArcCorrection (Z t : ℝ) : ℝ :=
  (3/10)*highArcL Z (2*t)+highArcN Z (2*t)

noncomputable def highRayCorrection (t : ℝ) : ℝ := -3/2+5*t/(1+(3/2)*t)

theorem hasDerivAt_highArcCorrection (Z t : ℝ) :
    HasDerivAt (highArcCorrection Z)
      ((3/10)*(Real.cos (2*t)-4*highArcN Z (2*t))+
        Real.sin (2*t)+4*highArcL Z (2*t)) t := by
  convert! ((hasDerivAt_highArcL Z t).const_mul (3/10)).add
    (hasDerivAt_highArcN Z t) using 1
  ring

theorem hasDerivAt_highRayCorrection (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt highRayCorrection (5/(1+(3/2)*t)^2) t := by
  have hd : 1+(3/2)*t ≠ 0 := by positivity
  have h := (((hasDerivAt_id t).const_mul 5).div
    (((hasDerivAt_id t).const_mul (3/2)).const_add 1) hd).const_add (-3/2)
  convert! h using 1
  simp only [id_eq,mul_one]
  field_simp [hd]
  ring

theorem highRayCorrection_quotient (t : ℝ) (ht : 0 ≤ t) :
    highRayCorrection t = (-3/2+(11/4)*t)/(1+(3/2)*t) := by
  unfold highRayCorrection
  field_simp [show 1+(3/2)*t ≠ 0 by positivity]
  ring

theorem highCorrection_join (Z : ℝ) (hZ : 2704/1000 ≤ Z) (hZ' : Z ≤ 2706/1000) :
    0 < highRayCorrection 0-highArcCorrection Z (highArcAngle/2) := by
  have h := highArc_join_jump_pos Z hZ hZ'
  simpa only [highRayCorrection,highArcCorrection,mul_zero,add_zero,zero_div,
    show 2*(highArcAngle/2)=highArcAngle by ring,sub_add_eq_sub_sub] using h

end DefocusingNLS

end OAI
