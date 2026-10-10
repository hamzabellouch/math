import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPhysicalPencilLift
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HarmonicRadialLinearCombination
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralMode

namespace OAI

/-! # A simple compact-pencil kernel gives proportional actual radial modes -/

open Set

namespace DefocusingNLS

open ProfileCertificate

attribute [local irreducible] SpectralPenaltyFamily.compactPencil
  radialMatchedWeakOperator spectralHarmonicObservation spectralFluxBoundary spectralGaugeRobin

theorem radialSpectralMode_eq_of_kernel_line (n ell i N : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (R l : ℝ) (hR : 0 < R)
    (s : SpectralPenaltyFamily R l)
    (hw : (s.weight i).density = radialMatchedMassFunction n z)
    (hp : s.pressure i = fun r => ‖radialMatchedProfile n z r‖ ^ (2 * (n + radialInnerShootingThreshold)))
    (ha : s.scale i = radialShootingA n) (lam : ℂ)
    (u v : RadialSpectralMode (radialShootingA n) (radialShootingB (profileMatchingParameter z))
      (n + radialInnerShootingThreshold) N (radialMatchedProfile n z) ((ell : ℂ) * (ell + 10)) lam)
    (M : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hu : (deriv u.first R, deriv u.second R) = M (u.first R, u.second R))
    (hv : (deriv v.first R, deriv v.second R) = M (v.first R, v.second R))
    (hline :
      let P := s.compactPencil ell hR i
        (radialMatchedWeakOperator n ell z hX hz R hR lam
          (spectralFluxBoundary R (radialMatchedMassFunction n z R)
            (radialMatchedTransportFunction n z R)
            (spectralGaugeRobin (radialMatchedProfile n z R)
              (deriv (radialMatchedProfile n z) R) M)))
      ∀ x y : SpectralRadialObservationSpace R, P x = x → x ≠ 0 → P y = y →
        ∃ c : ℂ, y = c • x) :
    ∃ c : ℂ, ∀ r : ℝ, 0 < r → v.first r = c * u.first r ∧ v.second r = c * u.second r := by
  have hη : (((ell : ℝ) * (ell + 10) : ℝ) : ℂ) = (ell : ℂ) * (ell + 10) := by
    push_cast
    rfl
  have hEu : IsHarmonicRadialEigenpair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold)
      (radialMatchedProfile n z) (((ell : ℝ) * (ell + 10) : ℝ) : ℂ) lam u.first u.second := by
    rw [hη]
    exact u.equation
  have hEv : IsHarmonicRadialEigenpair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold)
      (radialMatchedProfile n z) (((ell : ℝ) * (ell + 10) : ℝ) : ℂ) lam v.first v.second := by
    rw [hη]
    exact v.equation
  obtain ⟨U, hU⟩ := radialMatchedPhysical_pencil_lift n ell i z hX hz R l hR s hw hp ha lam
    u.first u.second u.first_c2 u.second_c2 hEu M hu
  obtain ⟨V, hV⟩ := radialMatchedPhysical_pencil_lift n ell i z hX hz R l hR s hw hp ha lam
    v.first v.second v.first_c2 v.second_c2 hEv M hv
  have hne := harmonicRadialEigenpair_nonzero_on_ball _ _ _ _ u.first u.second _ _
    (radialMatchedProfile_differentiable n z hX hz).continuous.continuousOn
    u.first_c2 u.second_c2 u.equation u.nonzero R hR
  obtain ⟨c, hc⟩ := hline _ _ hU (U.observation_ne_zero hne) hV
  refine ⟨c, harmonicRadialEigenpair_eq_of_ball (radialShootingA n)
    (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold)
    (radialMatchedProfile n z) v.first v.second u.first u.second ((ell : ℂ) * (ell + 10)) lam
    (radialMatchedProfile_differentiable n z hX hz).continuous.continuousOn
    v.first_c2 v.second_c2 u.first_c2 u.second_c2 v.equation u.equation R hR c ?_⟩
  intro r hr
  exact V.physical_eq_of_observation U c hc r ⟨hr.1.le, hr.2⟩

end DefocusingNLS

end OAI
