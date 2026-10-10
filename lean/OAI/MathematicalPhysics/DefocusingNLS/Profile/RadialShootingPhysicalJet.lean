import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialShootingInnerJet
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPhysicalJet

namespace OAI

/-! The actual outgoing exterior jet in physical radial coordinates. -/

namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialShootingPhysicalJet (n : ℕ) (z : ProfileMatchingBall) : ℝ → ℂ × ℂ :=
  radialPhysicalJet (radialShootingNu (n+radialInnerShootingThreshold) z)
    (radialExteriorCanonical (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))

theorem radialShootingPhysicalJet_hasDerivAt (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (r : ℝ) (hr : innerBoundaryRadius ≤ r) :
    HasDerivAt (radialShootingPhysicalJet n z)
      (radialStationaryField (n+radialInnerShootingThreshold) (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) r (radialShootingPhysicalJet n z r)) r := by
  have hr0 : 0 < r := lt_of_lt_of_le (by linarith [innerBoundaryRadius_bounds.1]) hr
  let Z := radialExteriorCanonical (radialShootingNu (n+radialInnerShootingThreshold) z)
    (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius)
  have hν : radialShootingNu (n+radialInnerShootingThreshold) z=
      -1/((n+radialInnerShootingThreshold : ℕ) : ℂ)+
        2*Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ) := by
    unfold radialShootingNu radialShootingQ
    ring
  have hZ := ((radialExteriorCanonical_spec hX).2.2 (Real.log r)
    (Real.log_le_log (by linarith [innerBoundaryRadius_bounds.1]) hr)).2
  change HasDerivAt Z (radialExteriorODEField
    (radialShootingNu (n+radialInnerShootingThreshold) z) _ (Real.log r) (Z (Real.log r))) _ at hZ
  rw [hν] at hZ
  have hh := radialPhysicalJet_hasDerivAt (n+radialInnerShootingThreshold)
    (radialShootingInner_power_pos n (profileMatchingParameter z))
    (radialShootingB (profileMatchingParameter z)) r hr0 Z hZ
  dsimp only at hh
  rw [← hν] at hh
  exact hh

theorem radialShootingPhysicalJet_snd (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (r : ℝ) (hr : innerBoundaryRadius ≤ r) :
    (radialShootingPhysicalJet n z r).2=deriv (radialShootingExteriorProfile n z) r := by
  exact ((radialPhysicalExterior_hasDerivAt _ _ _ r
    (lt_of_lt_of_le (by linarith [innerBoundaryRadius_bounds.1]) hr)
    ((radialExteriorCanonical_spec hX).2.2 (Real.log r)
      (Real.log_le_log (by linarith [innerBoundaryRadius_bounds.1]) hr)).2).deriv).symm

theorem radialShootingJet_match (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) :
    radialShootingInnerJet n (profileMatchingParameter z) innerBoundaryRadius=
      radialShootingPhysicalJet n z innerBoundaryRadius := by
  obtain ⟨hv,hd⟩ := radialMatchingMap_zero_boundary n z hX hz
  apply Prod.ext
  · exact hv.symm
  · rw [radialShootingPhysicalJet_snd n z hX _ le_rfl]
    exact hd.symm

end DefocusingNLS

end OAI
