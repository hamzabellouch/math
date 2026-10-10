import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedClassicalSourceTests
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralObservedSourceEquation

namespace OAI

/-! Actual classical source pairs satisfy the differentiated finite-power compact pencil. -/

open Set MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

noncomputable local instance classicalSourcePencilNormed (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R) := by
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem radialMatchedClassical_source_pencil (n ell i : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R l : ℝ) (hR : 0 < R)
    (s : SpectralPenaltyFamily R l)
    (hw : (s.weight i).density=radialMatchedMassFunction n z)
    (hp : s.pressure i=fun r => ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold)))
    (ha : s.scale i=radialShootingA n) (lam : ℂ) (f g f₀ g₀ : ℝ → ℂ)
    (hf₀ : Continuous f₀) (hg₀ : Continuous g₀)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsRadialLogGaugeSourcePair (n+radialInnerShootingThreshold)
      (radialMatchedEvenProfile n z) (((ell : ℝ)*(ell+10) : ℝ) : ℂ) lam f g f₀ g₀)
    (u : SpectralHarmonicPair ell R)
    (huf : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.fst r=f r)
    (hug : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.snd r=g r)
    (hudf : spectralHarmonicDerivative ell R u.fst =ᵐ[radialPressureMeasure R] deriv f)
    (hudg : spectralHarmonicDerivative ell R u.snd =ᵐ[radialPressureMeasure R] deriv g)
    (u₀ : SpectralHarmonicPair ell R)
    (huf₀ : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u₀.fst r=f₀ r)
    (hug₀ : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u₀.snd r=g₀ r)
    (B : ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ) (B' : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hB : HasDerivAt B B' lam)
    (hb : (spectralGaugeFirstFlux (radialMatchedMassFunction n z)
      (radialMatchedTransportFunction n z) f g R,
      spectralGaugeSecondFlux (radialMatchedMassFunction n z)
        (radialMatchedTransportFunction n z) f g R)=B lam (f R,g R)+B' (f₀ R,g₀ R)) :
    spectralHarmonicObservation ell R hR u-
      s.compactPencil ell hR i (radialMatchedWeakOperator n ell z hX hz R hR lam (B lam))
        (spectralHarmonicObservation ell R hR u)=
      deriv (fun t => s.compactPencil ell hR i
        (radialMatchedWeakOperator n ell z hX hz R hR t (B t))) lam
          (spectralHarmonicObservation ell R hR u₀) := by
  let K := fun t => radialMatchedWeakOperator n ell z hX hz R hR t (B t)
  let D := spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R (s.weight i)) B'
  have hK : HasDerivAt K D lam :=
    radialMatchedWeakOperator_hasDerivAt n ell z hX hz R hR (s.weight i) hw B B' lam hB
  have hP := s.compactPencil_hasDerivAt ell i hR K D lam hK
  change spectralHarmonicObservation ell R hR u-
    s.compactPencil ell hR i (K lam) (spectralHarmonicObservation ell R hR u)=
      deriv (fun t => s.compactPencil ell hR i (K t)) lam
        (spectralHarmonicObservation ell R hR u₀)
  rw [hP.deriv]
  apply s.compactPencil_source_of_complex_tests ell i hR (K lam) D u u₀
  · exact radialMatchedSource_first_test n ell i z hX hz R l hR s hw hp ha lam
      f g f₀ g₀ hf₀ hg₀ hf hg he u huf hug hudf hudg u₀ huf₀ hug₀ (B lam) B' hb
  · exact radialMatchedSource_second_test n ell i z hX hz R l hR s hw hp ha lam
      f g f₀ g₀ hf₀ hg₀ hf hg he u huf hug hudf hudg u₀ huf₀ hug₀ (B lam) B' hb

end DefocusingNLS

end OAI
