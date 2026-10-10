import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformDerivativeBound
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialGaugeEnergy

namespace OAI

/-! Physical unit energy gives the uniform gauge energy needed for the
pressure-free cross pairing. Constants depend only on the fixed ball. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

variable (s : ℕ → ℕ) (hs : StrictMono s)
  (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
  (hz : Tendsto z atTop (𝓝 z₀))
  (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
    (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
  (hm : ∀ i, radialMatchingMap (s i) (z i)=0)

include s hs z hz hX hm

theorem radialMatched_uniform_gauge_energy (R : ℝ) (hR : 0 < R)
    (ell : ℕ → ℕ) (F G f g : ℕ → ℝ → ℂ)
    (hF : ∀ i, ContDiff ℝ 2 (F i)) (hG : ∀ i, ContDiff ℝ 2 (G i))
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (hpair : ∀ i r, (radialMatchedEvenProfile (s i) (z i) r*(f i r+Complex.I*g i r),
      star (radialMatchedEvenProfile (s i) (z i) r)*(f i r-Complex.I*g i r)) = (F i r,G i r))
    (hnorm : ∀ i, (∫ r in (0 : ℝ)..R,
      spectralRadialEnergyDensity ((ell i : ℝ)*(ell i+10)) (F i) (G i) r) ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ i in atTop,
      (∫ r in (0 : ℝ)..R, radialMatchedMassFunction (s i) (z i) r*
        spectralRadialEnergyDensity ((ell i : ℝ)*(ell i+10)) (f i) (g i) r) ≤ K := by
  obtain ⟨c,M,hc,_,_,hb⟩ := radialMatched_uniform_weight_bounds s hs z z₀ hz hX hm R
  obtain ⟨D,_,hd⟩ := radialMatched_uniform_derivative_bound s hs z z₀ hz hX hm R hR
  let K := 1+D^2/c
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K,hK,?_⟩
  filter_upwards [hb,hd] with i hi hdi
  have hQi : ContDiff ℝ 2 (radialMatchedEvenProfile (s i) (z i)) :=
    (radialMatchedEvenProfile_contDiff _ _ (hX i) (hm i)).of_le (by simp)
  have hbound := spectralRadialGaugeEnergy_integral ((ell i : ℝ)*(ell i+10)) c D R hc
    (by positivity) hR.le (radialMatchedEvenProfile (s i) (z i)) (f i) (g i) (F i) (G i)
    hQi (hf i) (hg i) (hF i) (hG i) (hpair i) (fun r hr => ?_) hdi
  · have heq : (∫ r in (0 : ℝ)..R, ‖radialMatchedEvenProfile (s i) (z i) r‖^2*
        spectralRadialEnergyDensity ((ell i : ℝ)*(ell i+10)) (f i) (g i) r) =
        (∫ r in (0 : ℝ)..R, radialMatchedMassFunction (s i) (z i) r*
        spectralRadialEnergyDensity ((ell i : ℝ)*(ell i+10)) (f i) (g i) r) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le hR.le] at hr
      dsimp only
      rw [radialMatchedEvenProfile_nonneg (s i) (z i) r hr.1]
      rfl
    rw [heq] at hbound
    exact hbound.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hnorm i) hK)
  · simpa only [radialMatchedEvenProfile_nonneg (s i) (z i) r hr.1] using (hi r hr).1

theorem radialMatched_uniform_cross_energy (R : ℝ) (hR : 0 < R)
    (ell : ℕ → ℕ) (F G f g : ℕ → ℝ → ℂ)
    (hF : ∀ i, ContDiff ℝ 2 (F i)) (hG : ∀ i, ContDiff ℝ 2 (G i))
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (hpair : ∀ i r, (radialMatchedEvenProfile (s i) (z i) r*(f i r+Complex.I*g i r),
      star (radialMatchedEvenProfile (s i) (z i) r)*(f i r-Complex.I*g i r)) = (F i r,G i r))
    (hnorm : ∀ i, (∫ r in (0 : ℝ)..R,
      spectralRadialEnergyDensity ((ell i : ℝ)*(ell i+10)) (F i) (G i) r) ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ i in atTop,
      (∫ r in (0 : ℝ)..R,
        r^11*radialMatchedMassFunction (s i) (z i) r*(‖f i r‖^2+‖deriv (g i) r‖^2)+
        ((ell i : ℝ)*(ell i+10))*r^9*radialMatchedMassFunction (s i) (z i) r*‖g i r‖^2) ≤ K := by
  obtain ⟨K,hK,hb⟩ := radialMatched_uniform_gauge_energy s hs z z₀ hz hX hm R hR
    ell F G f g hF hG hf hg hpair hnorm
  refine ⟨K,hK,?_⟩
  filter_upwards [hb] with i hi
  apply le_trans _ hi
  exact spectralGaugeCrossEnergy_integral_le _ R (by positivity) hR.le
    (radialMatchedMassFunction (s i) (z i))
    (radialMatchedMassFunction_continuous (s i) (z i) (hX i) (hm i))
    (fun r _ => sq_nonneg _) (f i) (g i) (hf i) (hg i)

end DefocusingNLS

end OAI
