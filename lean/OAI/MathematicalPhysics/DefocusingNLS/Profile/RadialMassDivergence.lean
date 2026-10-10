import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressureContinuity

namespace OAI

/-! The exact radial divergence identity for the true mass density and velocity. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialMassDensity (n : ℕ) (z : ProfileMatchingBall) (r : ℝ) : ℝ :=
  r^11*‖radialMatchedProfile n z r‖^2

noncomputable def radialMassFlux (n : ℕ) (z : ProfileMatchingBall) (r : ℝ) : ℝ :=
  radialMassDensity n z r*radialVelocity (6-2*radialShootingA n)
    (fun t => ‖radialMatchedProfile n z t‖) r

theorem radialMassFlux_eq (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : 0 ≤ r) :
    radialMassFlux n z r=r^11*radialWeightedFlux (radialMatchedProfile n z) r := by
  rcases hr.eq_or_lt with he | hp
  · subst r
    simp [radialMassFlux,radialMassDensity]
  · have hN := (Complex.normSq_pos.mpr (radialMatchedProfile_ne_zero n z hX r hp.le)).ne'
    unfold radialMassFlux radialMassDensity
    rw [← radialMatchedVelocity_formula n z hX hz r hp,Complex.sq_norm]
    unfold radialWeightedFlux
    field_simp

theorem radialMassFlux_hasDerivAt (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (radialMassFlux n z)
      ((6-2*radialShootingA n)*radialMassDensity n z r) r := by
  have hf := radialMatchedWeightedFlux_hasDerivAt n z hX hz r hr
  have h := ((hasDerivAt_id r).pow 11).mul hf
  have hh : HasDerivAt (fun t => t^11*radialWeightedFlux (radialMatchedProfile n z) t)
      ((6-2*radialShootingA n)*radialMassDensity n z r) r := by
    apply h.congr_deriv
    simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,mul_one]
    unfold radialMassDensity
    rw [Complex.sq_norm]
    field_simp [hr.ne']
    ring
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hr] with t ht
  exact radialMassFlux_eq n z hX hz t ht.le

end DefocusingNLS

end OAI
