import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCanonicalJordanResidual
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedTailBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRobinSourcePlane
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCanonicalRobinAnalytic

namespace OAI

/-! The actual generalized mode's tail energy forces the differentiated outgoing boundary condition. -/

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialMatched_source_canonical_robin (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (eta lam : ℂ) (hlam : 0≤lam.re) (N : ℕ) (hN : 7≤N)
    (u : RadialSpectralMode (radialShootingA n) (radialShootingB (profileMatchingParameter z))
      (n+radialInnerShootingThreshold) N (radialMatchedProfile n z) eta lam)
    (v w : ℝ → ℂ) (hv : ContDiff ℝ 2 v) (hw : ContDiff ℝ 2 w)
    (he : IsHarmonicRadialSourcePair (radialShootingA n) (radialShootingB (profileMatchingParameter z))
      (n+radialInnerShootingThreshold) (radialMatchedProfile n z) eta lam v w u.first u.second)
    (hvt : IntegrableOn (fun r => r^11*‖iteratedDeriv N v r‖^2) (Ioi 0))
    (hwt : IntegrableOn (fun r => r^11*‖iteratedDeriv N w r‖^2) (Ioi 0))
    (hb : ∃ M : ℝ, 0≤M ∧ ∀ r, ‖(v r,w r)‖≤M)
    (Y Z : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (1,0) Y)
    (hZ : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (0,1) Z)
    (R : ℝ) (hR : innerBoundaryRadius<R)
    (hd : spectralValueDet
      (spectralPhysicalValueMap (spectralPhysicalPair
        (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
        (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam) (Y lam) R))
      (spectralPhysicalValueMap (spectralPhysicalPair
        (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
        (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam) (Z lam) R)) ≠ 0) :
    (deriv v R,deriv w R)=radialMatchedCanonicalRobin n z R Y Z lam (v R,w R)+
      deriv (radialMatchedCanonicalRobin n z R Y Z) lam (u.first R,u.second R) := by
  obtain ⟨c,hc,hWe,T,hRT,_,hWs,hWb,hWp,hWm⟩ := radialCanonicalJordan_residual n z hX hz
    eta lam hlam N hN u v w hv hw he hvt hwt hb Y Z hY hZ R hR
  let ν := radialShootingNu (n+radialInnerShootingThreshold) z
  let W := canonicalParameterResidualState ν Y Z lam c (harmonicRadialState v w)
  have hhalf : -(1/32 : ℝ)≤lam.re := by linarith
  have hres := radialMatched_state_canonical_tail_span_at n z hX hz eta N hN lam hhalf
    W R T hR hRT.le hWe hWs hWb hWp hWm Y Z hY hZ
  let P := fun la => spectralPhysicalPair (ν-2*la) (star ν-2*la) (Y la) R
  let Q := fun la => spectralPhysicalPair (ν-2*la) (star ν-2*la) (Z la) R
  have hr₁ : 1≤R := le_trans innerBoundaryRadius_bounds.1 hR.le
  have hP : AnalyticAt ℂ P lam := by
    apply spectralPhysicalPair_analyticAt
    · fun_prop
    · fun_prop
    · exact hY.2.2.1 lam (Real.log R) (Real.log_nonneg hr₁)
  have hQ : AnalyticAt ℂ Q lam := by
    apply spectralPhysicalPair_analyticAt
    · fun_prop
    · fun_prop
    · exact hZ.2.2.1 lam (Real.log R) (Real.log_nonneg hr₁)
  have hresult := spectralJetRobin_parameter_chain_of_residual P Q lam hP hQ hd c.1 c.2
    (harmonicRadialState u.first u.second R) (harmonicRadialState v w R) (hc R le_rfl) hres
  exact hresult

end DefocusingNLS

end OAI
