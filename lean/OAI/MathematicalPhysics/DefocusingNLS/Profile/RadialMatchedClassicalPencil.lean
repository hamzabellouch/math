import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedGaugeBalance
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakOperator

namespace OAI

/-! An actual classical gauge eigenmode satisfying the outer flux condition is
an eigenvector of the completed compact pencil. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS
open ProfileCertificate

private theorem radialMatchedClassical_first_test (n ell i : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R l : ℝ) (hR : 0 < R)
    (s : SpectralPenaltyFamily R l)
    (hw : (s.weight i).density=radialMatchedMassFunction n z)
    (hp : s.pressure i=fun r => ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold)))
    (ha : s.scale i=radialShootingA n) (lam : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsRadialLogGaugeEigenpair (n+radialInnerShootingThreshold)
      (radialMatchedEvenProfile n z) (((ell : ℝ)*(ell+10) : ℝ) : ℂ) lam f g)
    (u : SpectralHarmonicPair ell R)
    (huf : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.fst r=f r)
    (hug : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.snd r=g r)
    (hudf : spectralHarmonicDerivative ell R u.fst =ᵐ[radialPressureMeasure R] deriv f)
    (_hudg : spectralHarmonicDerivative ell R u.snd =ᵐ[radialPressureMeasure R] deriv g)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hb : (spectralGaugeFirstFlux (radialMatchedMassFunction n z)
      (radialMatchedTransportFunction n z) f g R,
      spectralGaugeSecondFlux (radialMatchedMassFunction n z)
        (radialMatchedTransportFunction n z) f g R)=B (f R,g R)) (φ : 𝓢(ℝ,ℂ)) :
    star (s.penaltyComplexForm ell i u (spectralFirstTest ell R φ))=
      inner ℂ (spectralFirstTest ell R φ)
        (radialMatchedWeakOperator n ell z hX hz R hR lam B
          (spectralHarmonicObservation ell R hR u)) := by
  let w := spectralContinuousCoefficient R (radialMatchedMassFunction n z)
    (radialMatchedMassFunction_continuous n z hX hz)
  let a := spectralContinuousCoefficient R (radialMatchedTransportFunction n z)
    (radialMatchedTransportFunction_continuous n z hX hz)
  have hb₁ := congrArg Prod.fst hb
  change spectralGaugeFirstFlux _ _ _ _ _=(B (f R,g R)).1 at hb₁
  rw [s.penaltyComplexForm_first_classical ell i hR u f huf hudf φ]
  change _ = inner ℂ (spectralFirstTest ell R φ)
    (spectralLowerOrderOperator ell R hR (spectralRadialWeightMultiplier R w)
      (spectralRadialWeightMultiplier R a) ((6-2*radialShootingA n : ℝ) : ℂ) lam B
      (spectralHarmonicObservation ell R hR u))
  rw [spectralLowerOrder_first_classical ell R hR w a _ lam B u f g huf hug φ,
    hw,hp,ha]
  have ht := (radialMatchedGauge_balance n z hX hz R hR
    (((ell : ℝ)*(ell+10) : ℝ) : ℂ) lam f g hf hg he φ).1
  rw [hb₁] at ht
  change _ = spectralClassicalRadialPairing R (radialMatchedMassFunction n z) f φ+
    (((6-2*radialShootingA n : ℝ) : ℂ)-lam)*
      spectralClassicalRadialPairing R (radialMatchedMassFunction n z) g φ+
    spectralClassicalRadialPairing R (radialMatchedTransportFunction n z) g (deriv φ)+
    star (φ R)*(B (f R,g R)).1
  linear_combination ht

private theorem radialMatchedClassical_second_test (n ell i : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R l : ℝ) (hR : 0 < R)
    (s : SpectralPenaltyFamily R l)
    (hw : (s.weight i).density=radialMatchedMassFunction n z)
    (_hp : s.pressure i=fun r => ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold)))
    (_ha : s.scale i=radialShootingA n) (lam : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsRadialLogGaugeEigenpair (n+radialInnerShootingThreshold)
      (radialMatchedEvenProfile n z) (((ell : ℝ)*(ell+10) : ℝ) : ℂ) lam f g)
    (u : SpectralHarmonicPair ell R)
    (huf : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.fst r=f r)
    (hug : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.snd r=g r)
    (_hudf : spectralHarmonicDerivative ell R u.fst =ᵐ[radialPressureMeasure R] deriv f)
    (hudg : spectralHarmonicDerivative ell R u.snd =ᵐ[radialPressureMeasure R] deriv g)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hb : (spectralGaugeFirstFlux (radialMatchedMassFunction n z)
      (radialMatchedTransportFunction n z) f g R,
      spectralGaugeSecondFlux (radialMatchedMassFunction n z)
        (radialMatchedTransportFunction n z) f g R)=B (f R,g R)) (φ : 𝓢(ℝ,ℂ)) :
    star (s.penaltyComplexForm ell i u (spectralSecondTest ell R φ))=
      inner ℂ (spectralSecondTest ell R φ)
        (radialMatchedWeakOperator n ell z hX hz R hR lam B
          (spectralHarmonicObservation ell R hR u)) := by
  let w := spectralContinuousCoefficient R (radialMatchedMassFunction n z)
    (radialMatchedMassFunction_continuous n z hX hz)
  let a := spectralContinuousCoefficient R (radialMatchedTransportFunction n z)
    (radialMatchedTransportFunction_continuous n z hX hz)
  have hb₂ := congrArg Prod.snd hb
  change spectralGaugeSecondFlux _ _ _ _ _=(B (f R,g R)).2 at hb₂
  rw [s.penaltyComplexForm_second_classical ell i hR u g hug hudg φ]
  change _ = inner ℂ (spectralSecondTest ell R φ)
    (spectralLowerOrderOperator ell R hR (spectralRadialWeightMultiplier R w)
      (spectralRadialWeightMultiplier R a) ((6-2*radialShootingA n : ℝ) : ℂ) lam B
      (spectralHarmonicObservation ell R hR u))
  rw [spectralLowerOrder_second_classical ell R hR w a _ lam B u f g huf hug φ,hw]
  have ht := (radialMatchedGauge_balance n z hX hz R hR
    (((ell : ℝ)*(ell+10) : ℝ) : ℂ) lam f g hf hg he φ).2
  rw [hb₂] at ht
  change _ = spectralClassicalRadialPairing R (radialMatchedMassFunction n z) g φ-
    (((6-2*radialShootingA n : ℝ) : ℂ)-lam)*
      spectralClassicalRadialPairing R (radialMatchedMassFunction n z) f φ-
    spectralClassicalRadialPairing R (radialMatchedTransportFunction n z) f (deriv φ)+
    star (φ R)*(B (f R,g R)).2
  linear_combination ht

theorem radialMatchedClassical_pencil (n ell i : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R l : ℝ) (hR : 0 < R)
    (s : SpectralPenaltyFamily R l)
    (hw : (s.weight i).density=radialMatchedMassFunction n z)
    (hp : s.pressure i=fun r => ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold)))
    (ha : s.scale i=radialShootingA n) (lam : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsRadialLogGaugeEigenpair (n+radialInnerShootingThreshold)
      (radialMatchedEvenProfile n z) (((ell : ℝ)*(ell+10) : ℝ) : ℂ) lam f g)
    (u : SpectralHarmonicPair ell R)
    (huf : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.fst r=f r)
    (hug : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.snd r=g r)
    (hudf : spectralHarmonicDerivative ell R u.fst =ᵐ[radialPressureMeasure R] deriv f)
    (hudg : spectralHarmonicDerivative ell R u.snd =ᵐ[radialPressureMeasure R] deriv g)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hb : (spectralGaugeFirstFlux (radialMatchedMassFunction n z)
      (radialMatchedTransportFunction n z) f g R,
      spectralGaugeSecondFlux (radialMatchedMassFunction n z)
        (radialMatchedTransportFunction n z) f g R)=B (f R,g R)) :
    s.compactPencil ell hR i (radialMatchedWeakOperator n ell z hX hz R hR lam B)
      (spectralHarmonicObservation ell R hR u)=spectralHarmonicObservation ell R hR u := by
  apply s.compactPencil_of_complex_tests ell i hR _ u
  · exact radialMatchedClassical_first_test n ell i z hX hz R l hR s hw hp ha lam
      f g hf hg he u huf hug hudf hudg B hb
  · exact radialMatchedClassical_second_test n ell i z hX hz R l hR s hw hp ha lam
      f g hf hg he u huf hug hudf hudg B hb

end DefocusingNLS

end OAI
