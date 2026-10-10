import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeDeformation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeSlowLogarithm

namespace OAI

/-! Identify the limiting canonical-jet deformation with the actual free velocity. -/

namespace DefocusingNLS

theorem radialFree_deformation_jet (b r : ℝ) (hr : 0 < r) (m : ℂ)
    (hn : (radialFreeSlowJet (-Complex.I*(b : ℂ)) m (Real.log r)).1 ≠ 0) :
    let ν := 2*Complex.I*(b : ℂ)
    let J := radialFreeSlowJet (-Complex.I*(b : ℂ)) m (Real.log r)
    let ξ := J.2/J.1
    radialFreeVelocity b r/r=1/2+2/r^2*(ν.im+ξ.im) ∧
      deriv (radialFreeVelocity b) r=
        1/2-ξ.re-2/r^2*(ν.im+ξ.im)*(11+2*ν.re+2*ξ.re) := by
  intro ν J ξ
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hJ : J.1 ≠ 0 := hn
  have he : (ν+ξ)/(r : ℂ)=radialFreeLog b r := by
    rw [← radialFreeSlow_physical_log b r hr m hn]
    change (ν+J.2/J.1)/(r : ℂ)=(ν*J.1+J.2)/((r : ℂ)*J.1)
    field_simp [hJ,hrC]
  have htan : radialFreeVelocity b r/r=1/2+2/r^2*(ν.im+ξ.im) := by
    unfold radialFreeVelocity
    rw [← he]
    simp only [Complex.div_ofReal_im,Complex.add_im]
    field_simp [hr.ne']
  have hν : ν.re=0 := by
    simp [ν,Complex.mul_re,Complex.mul_im]
  have hlog : (radialFreeLog b r).re=ξ.re/r := by
    rw [← he,Complex.div_ofReal_re,Complex.add_re,hν,zero_add]
  have harg : radialFreeSlowArgument (Real.log r)=freeRadialArgument r := by
    have he : Real.exp (2*Real.log r)=r^2 := by
      rw [two_mul,Real.exp_add,Real.exp_log hr]
      ring
    simp only [radialFreeSlowArgument,freeRadialArgument,he]
  have hraw : radialFreeRaw b r ≠ 0 := by
    intro hz
    apply hn
    change m*((radialFreeSlowArgument (Real.log r))^(-Complex.I*(b : ℂ))*
      regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (radialFreeSlowArgument (Real.log r)))=0
    rw [harg]
    change regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (freeRadialArgument r)=0 at hz
    rw [hz,mul_zero,mul_zero]
  refine ⟨htan,?_⟩
  rw [(radialFreeVelocity_hasDerivAt b r hr hraw).deriv,hlog,hν]
  have hw : radialFreeVelocity b r=(1/2+2/r^2*(ν.im+ξ.im))*r :=
    (div_eq_iff hr.ne').1 htan
  rw [hw]
  field_simp [hr.ne']
  ring

end DefocusingNLS

end OAI
