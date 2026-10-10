import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreePhysicalEquation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeSlowLogarithm
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeMatchingWronskian

namespace OAI

/-! Nonvanishing and the exact logarithmic derivative of the physical free profile. -/

namespace DefocusingNLS
open ProfileCertificate

theorem radialShootingFreeSlowValue_ne_zero (z : ProfileMatchingBall) (r : ℝ)
    (hr : radialShootingR (profileMatchingParameter z) ≤ r) :
    (radialFreeSlowJet (radialShootingQ z) (radialShootingM z) (Real.log r)).1 ≠ 0 := by
  have hr0 : 0 < r := lt_of_lt_of_le (by linarith [(radialShooting_geometry (profileMatchingParameter z)).2.1]) hr
  have he : Real.exp (2*Real.log r)=r^2 := by rw [two_mul,Real.exp_add,Real.exp_log hr0]; ring
  have harg : radialFreeSlowArgument (Real.log r)=freeRadialArgument r := by
    simp only [radialFreeSlowArgument,freeRadialArgument,he]
  have hx : freeRadialArgument r ≠ 0 := Complex.slitPlane_ne_zero (freeRadialArgument_mem_slit hr0)
  change radialShootingM z*(radialFreeSlowArgument (Real.log r)^radialShootingQ z*
    regularizedSlowSolution (radialShootingQ z) 6 (radialFreeSlowArgument (Real.log r))) ≠ 0
  rw [harg]
  exact mul_ne_zero (radialShootingM_ne_zero z)
    (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hx))
      (radialShootingRaw_ne_zero (profileMatchingParameter z) r hr))

theorem radialShootingFreeExterior_ne_zero (z : ProfileMatchingBall) (r : ℝ)
    (hr : radialShootingR (profileMatchingParameter z) ≤ r) :
    radialShootingFreeExterior z r ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (radialShootingFreeSlowValue_ne_zero z r hr)

theorem radialShootingFreeExterior_log (z : ProfileMatchingBall) (r : ℝ)
    (hr : radialShootingR (profileMatchingParameter z) ≤ r) :
    deriv (radialShootingFreeExterior z) r/radialShootingFreeExterior z r=
      radialFreeLog (radialShootingB (profileMatchingParameter z)) r := by
  have hr0 : 0 < r := lt_of_lt_of_le (by linarith [(radialShooting_geometry (profileMatchingParameter z)).2.1]) hr
  have hj := radialFreeSlow_physical_log (radialShootingB (profileMatchingParameter z)) r hr0
    (radialShootingM z) (radialShootingFreeSlowValue_ne_zero z r hr)
  rw [(radialShootingFreeExterior_hasDerivAt z r hr0).deriv]
  unfold radialShootingFreeJet spectralPhysicalJet radialShootingFreeExterior
  have hn := radialShootingFreeSlowValue_ne_zero z r hr
  have hexp := Complex.exp_ne_zero ((-2*radialShootingQ z)*(Real.log r : ℂ))
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  rw [← hj]
  change (Complex.exp _/(r : ℂ)*((-2*radialShootingQ z)*_+_))/(Complex.exp _*_)=_
  unfold radialShootingQ
  field_simp

theorem radialShooting_radius_square (w : RadialShootingDisk) :
    (radialShootingR w)^2/4=radialShootingZ w := by
  have hZ : 0 ≤ radialShootingZ w := by
    have hh := (ProfileCertificate.disk_coordinates w).2
    dsimp [radialShootingZ]
    norm_num [ProfileCertificate.centerZ,ProfileCertificate.radius] at hh ⊢
    linarith [(abs_le.mp hh).1]
  exact freeProfileRadius_sq hZ

theorem radialShootingFreeExterior_neumann (z : ProfileMatchingBall)
    (hz : diskProfile (profileMatchingParameter z)=0) :
    deriv (radialShootingFreeExterior z) (radialShootingR (profileMatchingParameter z))=0 := by
  let L := radialShootingR (profileMatchingParameter z)
  have hL : 0 < L := by dsimp only [L]; linarith [(radialShooting_geometry (profileMatchingParameter z)).2.1]
  have h := radialShootingFreeExterior_log z L le_rfl
  rw [radialFreeLog_eq_j _ _ hL,radialShooting_radius_square] at h
  change freeProfileJ (radialShootingB (profileMatchingParameter z))
    (radialShootingZ (profileMatchingParameter z))=0 at hz
  rw [hz,mul_zero] at h
  exact (div_eq_iff (radialShootingFreeExterior_ne_zero z L le_rfl)).mp h |>.trans (zero_mul _)

theorem radialShootingFreeExterior_boundary (z : ProfileMatchingBall) (hz : z.val.1=0) :
    radialShootingFreeExterior z innerBoundaryRadius=
      (radialFreeInnerJet (profileMatchingParameter z) innerBoundaryRadius).1 := by
  have he : -2*radialShootingQ z=2*Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ) := by
    unfold radialShootingQ
    ring
  unfold radialShootingFreeExterior
  rw [he]
  change Complex.exp _*radialFreeSlowValue _ _ _=_
  rw [radialShooting_free_value]
  simp only [radialShootingValue,hz,zero_div,add_zero]

end DefocusingNLS

end OAI
