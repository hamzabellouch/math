import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedPhysicalPencil
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClassicalObservationLine

namespace OAI

/-! # Compact-pencil lifts retaining the actual physical radial functions -/

open Set MeasureTheory
open scoped ContDiff

namespace DefocusingNLS

open ProfileCertificate

structure SpectralPhysicalGaugeLift (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (Q F G : ℝ → ℂ) where
  first : ℝ → ℂ
  second : ℝ → ℂ
  first_c2 : ContDiff ℝ 2 first
  second_c2 : ContDiff ℝ 2 second
  vector : SpectralHarmonicPair ell R
  first_repr : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR vector.fst r = first r
  second_repr : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR vector.snd r = second r
  physical : ∀ r, (Q r * (first r + Complex.I * second r),
    star (Q r) * (first r - Complex.I * second r)) = (F r, G r)

namespace SpectralPhysicalGaugeLift

theorem observation_ne_zero {ell : ℕ} {R : ℝ} {hR : 0 < R} {Q F G : ℝ → ℂ}
    (L : SpectralPhysicalGaugeLift ell R hR Q F G)
    (hne : ∃ r ∈ Ioc 0 R, F r ≠ 0 ∨ G r ≠ 0) :
    spectralHarmonicObservation ell R hR L.vector ≠ 0 := by
  apply spectralObservation_ne_zero_of_classical ell R hR L.vector L.first L.second
    L.first_c2.continuous.continuousOn L.second_c2.continuous.continuousOn
    L.first_repr L.second_repr
  obtain ⟨r, hr, hn⟩ := hne
  refine ⟨r, ⟨hr.1.le, hr.2⟩, ?_⟩
  by_contra hz
  push Not at hz
  have hp := L.physical r
  rw [hz.1, hz.2] at hp
  simp only [mul_zero, add_zero, sub_zero] at hp
  rcases hn with hn | hn
  · exact hn (congrArg Prod.fst hp).symm
  · exact hn (congrArg Prod.snd hp).symm

theorem physical_eq_of_observation {ell : ℕ} {R : ℝ} {hR : 0 < R}
    {Q F G U V : ℝ → ℂ}
    (L : SpectralPhysicalGaugeLift ell R hR Q F G)
    (M : SpectralPhysicalGaugeLift ell R hR Q U V) (c : ℂ)
    (he : spectralHarmonicObservation ell R hR L.vector =
      c • spectralHarmonicObservation ell R hR M.vector) :
    ∀ r ∈ Icc 0 R, F r = c * U r ∧ G r = c * V r := by
  have hv := spectralClassical_pair_eq_of_observation ell R hR L.vector M.vector
    L.first L.second M.first M.second
    L.first_c2.continuous.continuousOn L.second_c2.continuous.continuousOn
    M.first_c2.continuous.continuousOn M.second_c2.continuous.continuousOn
    L.first_repr L.second_repr M.first_repr M.second_repr c he
  intro r hr
  obtain ⟨hf, hg⟩ := hv r hr
  have hl := L.physical r
  have hm := M.physical r
  have hl₁ := congrArg Prod.fst hl
  have hl₂ := congrArg Prod.snd hl
  have hm₁ := congrArg Prod.fst hm
  have hm₂ := congrArg Prod.snd hm
  dsimp only at hl₁ hl₂ hm₁ hm₂
  constructor
  · rw [← hl₁, ← hm₁]
    rw [hf, hg]
    ring
  · rw [← hl₂, ← hm₂]
    rw [hf, hg]
    ring

end SpectralPhysicalGaugeLift

attribute [local irreducible] SpectralPenaltyFamily.compactPencil
  radialMatchedWeakOperator spectralHarmonicObservation spectralFluxBoundary spectralGaugeRobin

theorem radialMatchedPhysical_pencil_lift (n ell i : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (R l : ℝ) (hR : 0 < R)
    (s : SpectralPenaltyFamily R l)
    (hw : (s.weight i).density = radialMatchedMassFunction n z)
    (hp : s.pressure i = fun r => ‖radialMatchedProfile n z r‖ ^ (2 * (n + radialInnerShootingThreshold)))
    (ha : s.scale i = radialShootingA n) (lam : ℂ) (F G : ℝ → ℂ)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G)
    (he : IsHarmonicRadialEigenpair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold)
      (radialMatchedProfile n z) (((ell : ℝ) * (ell + 10) : ℝ) : ℂ) lam F G)
    (M : ℂ × ℂ →L[ℂ] ℂ × ℂ) (hM : (deriv F R, deriv G R) = M (F R, G R)) :
    ∃ L : SpectralPhysicalGaugeLift ell R hR (radialMatchedEvenProfile n z) F G,
      s.compactPencil ell hR i
        (radialMatchedWeakOperator n ell z hX hz R hR lam
          (spectralFluxBoundary R (radialMatchedMassFunction n z R)
            (radialMatchedTransportFunction n z R)
            (spectralGaugeRobin (radialMatchedProfile n z R)
              (deriv (radialMatchedProfile n z) R) M)))
        (spectralHarmonicObservation ell R hR L.vector) =
          spectralHarmonicObservation ell R hR L.vector := by
  obtain ⟨f, g, hf, hg, u, huf, hug, hudf, hudg, hpair, _⟩ :=
    radialMatchedGaugeJet 2 (by norm_num) n ell z hX hz R hR F G hF hG
  have hEq := radialMatchedGauge_equation n z hX hz _ lam F G f g hf hg hpair he
  have hQ := (radialMatchedEvenProfile_contDiff n z hX hz).differentiable (by simp) R
  have hμn : radialMatchedMassFunction n z R ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (radialMatchedProfile_ne_zero n z hX R hR.le))
  have hb := spectralPhysicalGaugeBoundary R (radialMatchedMassFunction n z R)
    (radialMatchedTransportFunction n z R) hR.ne' hμn
    (radialMatchedEvenProfile n z) f g F G hQ
    (hf.differentiable (by norm_num) R) (hg.differentiable (by norm_num) R)
    (radialMatchedEvenProfile_ne_zero n z hX R) hpair M hM
  rw [radialMatchedEvenProfile_nonneg n z R hR.le,
    (radialMatchedEvenProfile_eventuallyEq n z R hR).deriv_eq] at hb
  refine ⟨⟨f, g, hf, hg, u, huf, hug, hpair⟩, ?_⟩
  exact radialMatchedClassical_pencil n ell i z hX hz R l hR s hw hp ha lam
    f g hf hg hEq u huf hug hudf hudg _ hb

end DefocusingNLS

end OAI
