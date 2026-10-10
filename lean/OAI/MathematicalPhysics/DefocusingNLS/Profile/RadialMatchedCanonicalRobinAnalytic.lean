import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCanonicalAnalytic

namespace OAI

/-! Holomorphy of the physical outgoing Robin matrix used for first chains. -/

namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def radialMatchedCanonicalRobin (n : ℕ) (z : ProfileMatchingBall)
    (R : ℝ) (Y Z : ℂ → ℝ → E₄) (lam : ℂ) : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  spectralJetRobin
    (spectralPhysicalPair (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
      (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam) (Y lam) R)
    (spectralPhysicalPair (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
      (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam) (Z lam) R)

theorem radialMatchedCanonicalRobin_analyticAt (n ell : ℕ) (z : ProfileMatchingBall)
    (R : ℝ) (hR : 1 ≤ R) (Y Z : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (1,0) Y)
    (hZ : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (0,1) Z)
    (lam : ℂ)
    (hd : spectralValueDet
      (spectralPhysicalValueMap (spectralPhysicalPair
        (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
        (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam) (Y lam) R))
      (spectralPhysicalValueMap (spectralPhysicalPair
        (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
        (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam) (Z lam) R)) ≠ 0) :
    AnalyticAt ℂ (radialMatchedCanonicalRobin n z R Y Z) lam := by
  have ha (W : ℂ → ℝ → E₄)
      (hW : ∀ v t, 0 ≤ t → AnalyticAt ℂ (fun w => W w t) v) :
      AnalyticAt ℂ (fun w => spectralPhysicalPair
        (radialShootingNu (n+radialInnerShootingThreshold) z-2*w)
        (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*w) (W w) R) lam := by
    apply spectralPhysicalPair_analyticAt
    · fun_prop
    · fun_prop
    · exact hW lam (Real.log R) (Real.log_nonneg hR)
  have hM := spectralJetRobin_analyticAt _ _ lam
    (ha Y hY.2.2.1) (ha Z hZ.2.2.1) hd
  exact hM

end DefocusingNLS

end OAI
