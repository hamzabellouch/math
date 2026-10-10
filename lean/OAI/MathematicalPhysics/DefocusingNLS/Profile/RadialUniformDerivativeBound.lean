import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeightLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformExteriorPressure
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedEvenProfile
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialStationaryDerivativeBound

namespace OAI

/-! Uniform first-derivative bounds on a fixed ball follow from the
regular-origin stationary flux and the already proved pressure bound. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

variable (s : ℕ → ℕ) (hs : StrictMono s)
  (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
  (hz : Tendsto z atTop (𝓝 z₀))
  (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
    (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
  (hm : ∀ i, radialMatchingMap (s i) (z i)=0)

include s hs z hz hX hm


theorem radialMatched_uniform_derivative_bound (R : ℝ) (hR : 0 < R) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ i in atTop, ∀ r ∈ Ioc 0 R,
      ‖deriv (radialMatchedEvenProfile (s i) (z i)) r‖ ≤ D := by
  obtain ⟨c,M,hc,hM,_,hbound⟩ := radialMatched_uniform_weight_bounds s hs z z₀ hz hX hm R
  let S := 3*Real.sqrt M
  let D := S*R/12
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D,hD,?_⟩
  filter_upwards [hbound,hs.tendsto_atTop.eventually radialMatched_global_pressure_bound] with i hi hp
  let Q := radialMatchedEvenProfile (s i) (z i)
  have hQ : ContDiff ℝ 2 Q := (radialMatchedEvenProfile_contDiff (s i) (z i) (hX i) (hm i)).of_le (by simp)
  have hQbound r (hr : r ∈ Icc 0 R) : ‖Q r‖ ≤ Real.sqrt M := by
    apply (Real.le_sqrt (norm_nonneg _) hM).mpr
    have hb := (hi r hr).2
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)] at hb
    simpa only [Q,radialMatchedEvenProfile_nonneg (s i) (z i) r hr.1] using hb
  have hsource r (hr : r ∈ Icc 0 R) :
      ‖radialComplexSource (s i+radialInnerShootingThreshold) (radialShootingA (s i))
        (radialShootingB (profileMatchingParameter (z i))) (Q r)‖ ≤ S := by
    have hP : ‖Q r‖^(2*(s i+radialInnerShootingThreshold)) ≤ 1 := by
      simpa only [Q,radialMatchedEvenProfile_nonneg (s i) (z i) r hr.1] using hp (z i) r hr.1
    have ha := radialShootingA_bounds (s i) (profileMatchingParameter (z i))
    have hb := (radialShooting_geometry (profileMatchingParameter (z i))).1
    have hcoef : ‖((radialShootingB (profileMatchingParameter (z i)) : ℂ)+
        Complex.I*(radialShootingA (s i) : ℂ))‖ ≤ 2 := by
      have hn := norm_add_le (radialShootingB (profileMatchingParameter (z i)) : ℂ)
        (Complex.I*(radialShootingA (s i) : ℂ))
      simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs] at hn
      rw [abs_of_pos ha.1,abs_of_nonneg (by linarith [hb.1])] at hn
      linarith [ha.2,hb.2]
    have hN : ‖oddPowerNonlinearity (s i+radialInnerShootingThreshold) (Q r)‖ ≤ ‖Q r‖ := by
      rw [oddPowerNonlinearity_eq,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
      exact mul_le_of_le_one_left (norm_nonneg _) hP
    have hs := norm_sub_le (oddPowerNonlinearity (s i+radialInnerShootingThreshold) (Q r))
      ((((radialShootingB (profileMatchingParameter (z i)) : ℂ)+Complex.I*(radialShootingA (s i) : ℂ)))*(Q r))
    change ‖radialComplexSource _ _ _ (Q r)‖ ≤ _ at hs
    rw [norm_mul] at hs
    have hp' := mul_le_mul_of_nonneg_right hcoef (norm_nonneg (Q r))
    dsimp only [S]
    linarith [hQbound r hr]
  have he r (hr : r ∈ Ioo 0 R) := radialMatchedProfile_stationary (s i) (z i) (hX i) (hm i) r hr.1
  have heq r (hr : r ∈ Ioo 0 R) :
      deriv (deriv Q) r+(11/r : ℝ)*deriv Q r+
        Complex.I*((r/2 : ℝ)*deriv Q r+(radialShootingA (s i) : ℂ)*Q r)+
        (radialShootingB (profileMatchingParameter (z i)) : ℂ)*Q r=
        oddPowerNonlinearity (s i+radialInnerShootingThreshold) (Q r) := by
    have heven := radialMatchedEvenProfile_eventuallyEq (s i) (z i) r hr.1
    simpa only [← heven.eq_of_nhds,← heven.deriv_eq,← heven.deriv.deriv_eq] using he r hr
  intro r hr
  have hd := radialStationary_derivative_bound _ _ _ R S hS Q hQ heq hsource r hr
  exact hd.trans (by dsimp only [D]; gcongr; exact hr.2)

end DefocusingNLS

end OAI
