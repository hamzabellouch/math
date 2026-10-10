import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedSourceBalance
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakOperator
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClassicalSlopePairing

namespace OAI

/-! Classical Jordan sources give the exact two differentiated pencil test equations. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedSource_first_test (n ell i : ℕ) (z : ProfileMatchingBall)
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
    (_hudg : spectralHarmonicDerivative ell R u.snd =ᵐ[radialPressureMeasure R] deriv g)
    (u₀ : SpectralHarmonicPair ell R)
    (huf₀ : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u₀.fst r=f₀ r)
    (hug₀ : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u₀.snd r=g₀ r)
    (B B' : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hb : (spectralGaugeFirstFlux (radialMatchedMassFunction n z)
      (radialMatchedTransportFunction n z) f g R,
      spectralGaugeSecondFlux (radialMatchedMassFunction n z)
        (radialMatchedTransportFunction n z) f g R)=B (f R,g R)+B' (f₀ R,g₀ R)) (φ : 𝓢(ℝ,ℂ)) :
    star (s.penaltyComplexForm ell i u (spectralFirstTest ell R φ))=
      inner ℂ (spectralFirstTest ell R φ)
        (radialMatchedWeakOperator n ell z hX hz R hR lam B
          (spectralHarmonicObservation ell R hR u)+
          spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R (s.weight i)) B'
            (spectralHarmonicObservation ell R hR u₀)) := by
  let w := spectralContinuousCoefficient R (radialMatchedMassFunction n z)
    (radialMatchedMassFunction_continuous n z hX hz)
  let a := spectralContinuousCoefficient R (radialMatchedTransportFunction n z)
    (radialMatchedTransportFunction_continuous n z hX hz)
  have hb₁ := congrArg Prod.fst hb
  change spectralGaugeFirstFlux _ _ _ _ _=(B (f R,g R)).1+(B' (f₀ R,g₀ R)).1 at hb₁
  rw [s.penaltyComplexForm_first_classical ell i hR u f huf hudf φ]
  change _ = inner ℂ (spectralFirstTest ell R φ)
    (spectralLowerOrderOperator ell R hR (spectralRadialWeightMultiplier R w)
      (spectralRadialWeightMultiplier R a) ((6-2*radialShootingA n : ℝ) : ℂ) lam B
      (spectralHarmonicObservation ell R hR u)+
        spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R (s.weight i)) B'
          (spectralHarmonicObservation ell R hR u₀))
  rw [inner_add_right (𝕜 := ℂ) (E := SpectralHarmonicPair ell R),spectralLowerOrder_first_classical ell R hR w a _ lam B u f g huf hug φ,
    spectralLowerOrderSlope_first_classical ell R hR (s.weight i) B' u₀ f₀ g₀ huf₀ hug₀ φ,
    hw,hp,ha]
  have ht := (radialMatchedSource_balance n z hX hz R hR
    (((ell : ℝ)*(ell+10) : ℝ) : ℂ) lam f g f₀ g₀ hf₀ hg₀ hf hg he φ).1
  rw [hb₁] at ht
  have hw' : w.density=radialMatchedMassFunction n z := rfl
  have ha' : a.density=radialMatchedTransportFunction n z := rfl
  rw [hw',ha']
  linear_combination ht

theorem radialMatchedSource_second_test (n ell i : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R l : ℝ) (hR : 0 < R)
    (s : SpectralPenaltyFamily R l)
    (hw : (s.weight i).density=radialMatchedMassFunction n z)
    (_hp : s.pressure i=fun r => ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold)))
    (_ha : s.scale i=radialShootingA n) (lam : ℂ) (f g f₀ g₀ : ℝ → ℂ)
    (hf₀ : Continuous f₀) (hg₀ : Continuous g₀)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsRadialLogGaugeSourcePair (n+radialInnerShootingThreshold)
      (radialMatchedEvenProfile n z) (((ell : ℝ)*(ell+10) : ℝ) : ℂ) lam f g f₀ g₀)
    (u : SpectralHarmonicPair ell R)
    (huf : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.fst r=f r)
    (hug : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.snd r=g r)
    (_hudf : spectralHarmonicDerivative ell R u.fst =ᵐ[radialPressureMeasure R] deriv f)
    (hudg : spectralHarmonicDerivative ell R u.snd =ᵐ[radialPressureMeasure R] deriv g)
    (u₀ : SpectralHarmonicPair ell R)
    (huf₀ : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u₀.fst r=f₀ r)
    (hug₀ : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u₀.snd r=g₀ r)
    (B B' : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hb : (spectralGaugeFirstFlux (radialMatchedMassFunction n z)
      (radialMatchedTransportFunction n z) f g R,
      spectralGaugeSecondFlux (radialMatchedMassFunction n z)
        (radialMatchedTransportFunction n z) f g R)=B (f R,g R)+B' (f₀ R,g₀ R)) (φ : 𝓢(ℝ,ℂ)) :
    star (s.penaltyComplexForm ell i u (spectralSecondTest ell R φ))=
      inner ℂ (spectralSecondTest ell R φ)
        (radialMatchedWeakOperator n ell z hX hz R hR lam B
          (spectralHarmonicObservation ell R hR u)+
          spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R (s.weight i)) B'
            (spectralHarmonicObservation ell R hR u₀)) := by
  let w := spectralContinuousCoefficient R (radialMatchedMassFunction n z)
    (radialMatchedMassFunction_continuous n z hX hz)
  let a := spectralContinuousCoefficient R (radialMatchedTransportFunction n z)
    (radialMatchedTransportFunction_continuous n z hX hz)
  have hb₂ := congrArg Prod.snd hb
  change spectralGaugeSecondFlux _ _ _ _ _=(B (f R,g R)).2+(B' (f₀ R,g₀ R)).2 at hb₂
  rw [s.penaltyComplexForm_second_classical ell i hR u g hug hudg φ]
  change _ = inner ℂ (spectralSecondTest ell R φ)
    (spectralLowerOrderOperator ell R hR (spectralRadialWeightMultiplier R w)
      (spectralRadialWeightMultiplier R a) ((6-2*radialShootingA n : ℝ) : ℂ) lam B
      (spectralHarmonicObservation ell R hR u)+
        spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R (s.weight i)) B'
          (spectralHarmonicObservation ell R hR u₀))
  rw [inner_add_right (𝕜 := ℂ) (E := SpectralHarmonicPair ell R),spectralLowerOrder_second_classical ell R hR w a _ lam B u f g huf hug φ,
    spectralLowerOrderSlope_second_classical ell R hR (s.weight i) B' u₀ f₀ g₀ huf₀ hug₀ φ,hw]
  have ht := (radialMatchedSource_balance n z hX hz R hR
    (((ell : ℝ)*(ell+10) : ℝ) : ℂ) lam f g f₀ g₀ hf₀ hg₀ hf hg he φ).2
  rw [hb₂] at ht
  have hw' : w.density=radialMatchedMassFunction n z := rfl
  have ha' : a.density=radialMatchedTransportFunction n z := rfl
  rw [hw',ha']
  linear_combination ht

end DefocusingNLS

end OAI
