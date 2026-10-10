import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCanonicalMultiplicity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCanonicalSourceExclusion
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedSourceRobin

namespace OAI

/-! Actual finite-energy generalized radial modes are excluded without an outgoing-boundary hypothesis. -/

open Filter Topology Set MeasureTheory
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable local instance canonicalJordanExclusionNormed (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R) := by
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem radialMatchedCanonical_no_generalized_mode (hRou : RectangleRouche)
    (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hz₁ : z₀.val.1=0) (hz₀ : diskProfile (profileMatchingParameter z₀)=0)
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0) (ell N : ℕ) (hN : 7 ≤ N)
    (Y Z : ℕ → ℂ → ℝ → E₄)
    (hY : ∀ i, IsCanonicalHolomorphicColumn
      (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM (z i))
      (s i+radialInnerShootingThreshold) (Real.log innerBoundaryRadius) (1,0) (Y i))
    (hZ : ∀ i, IsCanonicalHolomorphicColumn
      (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM (z i))
      (s i+radialInnerShootingThreshold) (Real.log innerBoundaryRadius) (0,1) (Z i))
    (R : ℝ) (hR : innerBoundaryRadius < R)
    (hLR : radialShootingR (profileMatchingParameter z₀) < R)
    (F : SpectralPenaltyFamily R (radialShootingR (profileMatchingParameter z₀)))
    (hmass : F.limitWeight.density=radialMatchedFreeMassFunction z₀)
    (hw : ∀ i, (F.weight i).density=radialMatchedMassFunction (s i) (z i))
    (hp : ∀ i, F.pressure i=fun r => ‖radialMatchedProfile (s i) (z i) r‖^(2*(s i+radialInnerShootingThreshold)))
    (ha : ∀ i, F.scale i=radialShootingA (s i))
    (lam₀ : ℂ) (hsym : (ell=0 ∧ (lam₀=0 ∨ lam₀=1)) ∨ (ell=1 ∧ lam₀=1/2))
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell
        (radialShootingB (profileMatchingParameter z₀)) lam₀ R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell
        (radialShootingB (profileMatchingParameter z₀)) lam₀ R)) ≠ 0)
    (x : ℕ → ℂ) (hx : Tendsto x atTop (𝓝 lam₀)) (hxnonneg : ∀ i, 0≤(x i).re) :
    ∀ᶠ i in atTop,
      ∀ u : RadialSpectralMode (radialShootingA (s i))
        (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold) N
        (radialMatchedProfile (s i) (z i)) ((ell : ℂ)*(ell+10)) (x i),
      ∀ v w : ℝ → ℂ, ContDiff ℝ 2 v → ContDiff ℝ 2 w →
      IsHarmonicRadialSourcePair (radialShootingA (s i))
        (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold)
        (radialMatchedProfile (s i) (z i)) ((ell : ℂ)*(ell+10)) (x i) v w u.first u.second →
      IntegrableOn (fun r => r^11*‖iteratedDeriv N v r‖^2) (Ioi 0) →
      IntegrableOn (fun r => r^11*‖iteratedDeriv N w r‖^2) (Ioi 0) →
      (∃ M : ℝ, 0≤M ∧ ∀ r, ‖(v r,w r)‖≤M) →
      False := by
  have hhalf₀ : -(1/32 : ℝ) < lam₀.re := by
    rcases hsym with ⟨_,rfl | rfl⟩ | ⟨_,rfl⟩ <;> norm_num
  have hns := radialMatchedCanonical_no_source hRou s hs z z₀ hz hz₁ hz₀ hX hm ell N hN
    Y Z hY hZ R hR hLR F hmass hw hp ha lam₀ hsym hdet x hx
  have hval := (radialMatchedCanonicalValueDet_joint_tendsto s hs z z₀ hz ell Y Z hY hZ
    R hR lam₀ hhalf₀.le).comp (tendsto_id.prodMk hx)
  have hd := hval.eventually (eventually_ne_nhds hdet)
  filter_upwards [hns,hd] with i hi hdi
  intro u v w hv hw₂ he hvt hwt hb
  have hboundary := radialMatched_source_canonical_robin (s i) (z i) (hX i) (hm i)
    ((ell : ℂ)*(ell+10)) (x i) (hxnonneg i) N hN u v w hv hw₂ he hvt hwt hb
    (Y i) (Z i)
    (by simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using hY i)
    (by simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using hZ i) R hR hdi
  exact hi u v w hv hw₂ he hboundary

end DefocusingNLS

end OAI
