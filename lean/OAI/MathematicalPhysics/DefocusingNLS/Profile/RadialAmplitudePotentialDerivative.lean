import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVelocityLocal

namespace OAI

/-! The exact potential derivative used in the pressure transport estimate. -/

namespace DefocusingNLS

theorem radialAmplitudePotential_hasDerivAt (c b d : ℝ) (A : ℝ → ℝ)
    (hA : Continuous A) (r : ℝ) (hr : r ≠ 0) (hAr : A r ≠ 0)
    (hd : HasDerivAt A d r) :
    HasDerivAt (radialAmplitudePotential c b A)
      (r*(1/8-c/2*(radialVelocity c A r/r)+
        11/2*(radialVelocity c A r/r)^2)+(radialVelocity c A r)^2*d/A r) r := by
  have hw := radialVelocity_hasDerivAt_local c d A hA r hr hAr hd
  have hv := ((((hasDerivAt_id r).pow 2).div_const 16).const_add b).sub
    ((hw.pow 2).div_const 4)
  convert hv using 1
  · funext t
    dsimp only [radialAmplitudePotential,radialVelocity,Pi.sub_apply,Pi.add_apply,
      Pi.div_apply,Pi.pow_apply,id_eq]
    ring
  · dsimp only [radialVelocity,id_eq]
    field_simp [hr,hAr]
    ring

end DefocusingNLS

end OAI
