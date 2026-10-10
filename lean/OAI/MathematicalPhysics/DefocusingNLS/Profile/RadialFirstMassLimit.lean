import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeFirstMass
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformTransportBound

namespace OAI

/-! The first gauge component has vanishing weighted L2 mass along every
escaping frequency sequence with bounded energy and boundary pairing. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem spectralFrequency_mass_limit (omega mass : ℕ → ℝ) (K : ℝ)
    (hw : Tendsto omega atTop atTop) (hm : ∀ n, 0 ≤ mass n)
    (hb : ∀ᶠ n in atTop, omega n*mass n ≤ K) :
    Tendsto mass atTop (𝓝 0) := by
  have hzero : Tendsto (fun n => K/omega n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hw).const_mul K
  apply squeeze_zero' (Eventually.of_forall hm) _ hzero
  filter_upwards [hb,hw.eventually (eventually_gt_atTop 0)] with n hn hwn
  exact (le_div_iff₀ hwn).mpr (by simpa only [mul_comm] using hn)

variable (s : ℕ → ℕ) (hs : StrictMono s)
  (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
  (hz : Tendsto z atTop (𝓝 z₀))
  (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
    (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
  (hmatch : ∀ i, radialMatchingMap (s i) (z i)=0)

include s hs z hz hX hmatch

theorem radialMatched_first_mass_limit (R M L : ℝ) (hR : 0 < R)
    (lam : ℕ → ℂ) (ell : ℕ → ℕ) (hw : Tendsto (fun i => (lam i).im) atTop atTop)
    (f g : ℕ → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i)) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (he : ∀ i, IsRadialLogGaugeEigenpair (s i+radialInnerShootingThreshold)
      (radialMatchedEvenProfile (s i) (z i))
      (((ell i : ℝ)*(ell i+10) : ℝ) : ℂ) (lam i) (f i) (g i))
    (henergy : ∀ᶠ i in atTop, (∫ r in (0 : ℝ)..R,
      radialMatchedMassFunction (s i) (z i) r*
        spectralRadialEnergyDensity ((ell i : ℝ)*(ell i+10)) (f i) (g i) r) ≤ M)
    (hboundary : ∀ᶠ i in atTop, ‖star (f i R)*spectralGaugeSecondFlux
      (radialMatchedMassFunction (s i) (z i)) (radialMatchedTransportFunction (s i) (z i))
      (f i) (g i) R‖ ≤ L) :
    Tendsto (fun i => ∫ r in (0 : ℝ)..R,
      r^11*radialMatchedMassFunction (s i) (z i) r*‖f i r‖^2) atTop (𝓝 0) := by
  obtain ⟨C,hC,hA⟩ := radialMatched_uniform_transport_bound s hs z z₀ hz hX hmatch R hR.le
  have hnonneg i : 0 ≤ ∫ r in (0 : ℝ)..R,
      r^11*radialMatchedMassFunction (s i) (z i) r*‖f i r‖^2 := by
    apply intervalIntegral.integral_nonneg hR.le
    intro r hr
    have hr0 := hr.1
    change 0 ≤ r^11*‖radialMatchedProfile (s i) (z i) r‖^2*‖f i r‖^2
    positivity
  apply spectralFrequency_mass_limit (fun i => (lam i).im) _ ((1+C)*M+L) hw hnonneg
  filter_upwards [hA,henergy,hboundary] with i hi hei hbi
  have hbound := spectralGaugeFirst_mass_bound R C M L hR.le hC _ _
    (radialMatchedMassFunction_continuous (s i) (z i) (hX i) (hmatch i))
    (radialMatchedTransportFunction_continuous (s i) (z i) (hX i) (hmatch i))
    ((ell i : ℝ)*(ell i+10)) (6-2*radialShootingA (s i)) (by positivity)
    (lam i) (f i) (g i) (hf i) (hg i)
    (fun r hr => (hi r hr).1.le) (fun r hr => (hi r hr).2) ?_ hei hbi
  · exact (mul_le_mul_of_nonneg_right (le_abs_self _) (hnonneg i)).trans hbound
  · intro r hr
    exact (radialMatchedGauge_flux (s i) (z i) (hX i) (hmatch i) _ (lam i)
      (f i) (g i) (hf i) (hg i) (he i) r hr.1).2

end DefocusingNLS

end OAI
