import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformCrossBound
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCrossFluxLimit

namespace OAI

/-! The actual physical total flux vanishes on the square-root frequency
scale once the normalized gauge energy and boundary pairing are bounded. -/

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



theorem radialMatched_sqrt_flux_limit (R M L : ℝ) (hR : 0 < R)
    (lam : ℕ → ℂ) (ell : ℕ → ℕ)
    (hhalf : ∀ i, -(1/32 : ℝ) ≤ (lam i).re) (hupper : ∀ i, (lam i).re ≤ 4)
    (hw : Tendsto (fun i => (lam i).im) atTop atTop)
    (F G f g : ℕ → ℝ → ℂ)
    (hF : ∀ i, ContDiff ℝ 2 (F i)) (hG : ∀ i, ContDiff ℝ 2 (G i))
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (he : ∀ i, IsHarmonicRadialEigenpair (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold)
      (radialMatchedProfile (s i) (z i)) (((ell i : ℝ)*(ell i+10) : ℝ) : ℂ) (lam i) (F i) (G i))
    (hpair : ∀ i r, (radialMatchedEvenProfile (s i) (z i) r*(f i r+Complex.I*g i r),
      star (radialMatchedEvenProfile (s i) (z i) r)*(f i r-Complex.I*g i r)) = (F i r,G i r))
    (henergy : ∀ᶠ i in atTop, (∫ r in (0 : ℝ)..R,
      r^11*radialMatchedMassFunction (s i) (z i) r*(‖f i r‖^2+‖deriv (g i) r‖^2)+
      ((ell i : ℝ)*(ell i+10))*r^9*radialMatchedMassFunction (s i) (z i) r*‖g i r‖^2) ≤ M)
    (hboundary : ∀ᶠ i in atTop, ‖star (g i R)*spectralGaugeSecondFlux
      (radialMatchedMassFunction (s i) (z i)) (radialMatchedTransportFunction (s i) (z i)) (f i) (g i) R‖ ≤ L) :
    Tendsto (fun i => Real.sqrt (lam i).im*
      (spectralScalarFlux (spectralPhysicalLiouvillePair (F i) (G i) R).1+
        spectralScalarFlux (spectralPhysicalLiouvillePair (F i) (G i) R).2)) atTop (𝓝 0) := by
  have heg i := radialMatchedGauge_equation (s i) (z i) (hX i) (hm i) _ (lam i)
    (F i) (G i) (f i) (g i) (hf i) (hg i) (hpair i) (he i)
  obtain ⟨K,hK,hcross⟩ := radialMatchedGauge_uniform_cross_bound s hs z z₀ hz hX hm
    R M L hR lam ell f g hf hg heg henergy hboundary
  let cross := fun i => ∫ r in (0 : ℝ)..R, (r : ℂ)^11*
    (radialMatchedMassFunction (s i) (z i) r : ℂ)*star (g i r)*f i r
  apply spectralCross_total_flux_limit (fun i => (lam i).im)
    (fun i => radialShootingA (s i)+(lam i).re-3) _ cross K 8 (by norm_num) hw
  · filter_upwards [hcross] with i hi
    exact (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)).trans hi
  · apply Eventually.of_forall
    intro i
    have ha := radialShootingA_bounds (s i) (profileMatchingParameter (z i))
    exact abs_le.mpr ⟨by linarith [hhalf i],by linarith [hupper i]⟩
  · intro i
    have he' : IsHarmonicRadialEigenpair (radialShootingA (s i))
        (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold)
        (radialMatchedEvenProfile (s i) (z i)) (((ell i : ℝ)*(ell i+10) : ℝ) : ℂ)
        (lam i) (F i) (G i) := by
      intro r hr
      simpa only [radialMatchedEvenProfile_nonneg (s i) (z i) r hr.le] using he i r hr
    have hi := spectralPhysicalLiouvillePair_gauge_flux_integral _ _ _ _ _ (lam i)
      (F i) (G i) (f i) (g i) (hF i) (hG i) he'
      (radialMatchedEvenProfile_contDiff (s i) (z i) (hX i) (hm i)).continuous
      (hf i).continuous (hg i).continuous
      (fun r => ⟨(congrArg Prod.fst (hpair i r)).symm,(congrArg Prod.snd (hpair i r)).symm⟩) R hR
    have hcrossEq : (∫ r in (0 : ℝ)..R, (r : ℂ)^11*
        ((‖radialMatchedEvenProfile (s i) (z i) r‖^2 : ℝ) : ℂ)*star (g i r)*f i r) = cross i := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le hR.le] at hr
      dsimp only
      rw [radialMatchedEvenProfile_nonneg (s i) (z i) r hr.1]
      rfl
    rw [hcrossEq] at hi
    exact hi

end DefocusingNLS

end OAI
