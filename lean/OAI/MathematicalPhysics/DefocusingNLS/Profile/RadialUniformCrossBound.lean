import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformTransportBound
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeCrossBound

namespace OAI

/-! Uniform cross-pairing control for actual gauged eigenmodes with bounded
energy and boundary data. The transport constant is constructed from the profiles. -/

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


theorem radialMatchedGauge_uniform_cross_bound (R M L : ℝ) (hR : 0 < R)
    (lam : ℕ → ℂ) (ell : ℕ → ℕ) (f g : ℕ → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (he : ∀ i, IsRadialLogGaugeEigenpair (s i+radialInnerShootingThreshold)
      (radialMatchedEvenProfile (s i) (z i))
      (((ell i : ℝ)*(ell i+10) : ℝ) : ℂ) (lam i) (f i) (g i))
    (henergy : ∀ᶠ i in atTop, (∫ r in (0 : ℝ)..R,
      r^11*radialMatchedMassFunction (s i) (z i) r*(‖f i r‖^2+‖deriv (g i) r‖^2)+
      ((ell i : ℝ)*(ell i+10))*r^9*radialMatchedMassFunction (s i) (z i) r*‖g i r‖^2) ≤ M)
    (hboundary : ∀ᶠ i in atTop, ‖star (g i R)*spectralGaugeSecondFlux
      (radialMatchedMassFunction (s i) (z i)) (radialMatchedTransportFunction (s i) (z i)) (f i) (g i) R‖ ≤ L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ i in atTop, |(lam i).im| *
      ‖∫ r in (0 : ℝ)..R, (r : ℂ)^11*(radialMatchedMassFunction (s i) (z i) r : ℂ)*star (g i r)*f i r‖ ≤ K := by
  obtain ⟨C,hC,hA⟩ := radialMatched_uniform_transport_bound s hs z z₀ hz hX hm R hR.le
  refine ⟨max 0 ((1+C)*M+L),le_max_left _ _,?_⟩
  filter_upwards [hA,henergy,hboundary] with i hi hei hbi
  apply le_trans _ (le_max_right _ _)
  apply spectralGaugeSecond_cross_bound R C M L hR.le hC _ _
    (radialMatchedMassFunction_continuous (s i) (z i) (hX i) (hm i))
    (radialMatchedTransportFunction_continuous (s i) (z i) (hX i) (hm i))
    ((ell i : ℝ)*(ell i+10)) (6-2*radialShootingA (s i)) (by positivity)
    (lam i) (f i) (g i) (hf i) (hg i)
    (fun r hr => (hi r hr).1.le) (fun r hr => (hi r hr).2) _ hei hbi
  intro r hr
  exact (radialMatchedGauge_flux (s i) (z i) (hX i) (hm i) _ (lam i) (f i) (g i)
    (hf i) (hg i) (he i) r hr.1).2

end DefocusingNLS

end OAI
