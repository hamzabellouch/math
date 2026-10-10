import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCanonicalMultiplicity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralCanonicalSourceChain

namespace OAI

/-! Actual generalized radial modes satisfying the outgoing derivative condition are eventually excluded. -/

open Filter Topology Set
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable local instance canonicalSourceExclusionNormed (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R) := by
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem radialMatchedCanonical_no_source (hRou : RectangleRouche)
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
    (x : ℕ → ℂ) (hx : Tendsto x atTop (𝓝 lam₀)) :
    ∀ᶠ i in atTop,
      ∀ u : RadialSpectralMode (radialShootingA (s i))
        (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold) N
        (radialMatchedProfile (s i) (z i)) ((ell : ℂ)*(ell+10)) (x i),
      ∀ v w : ℝ → ℂ, ContDiff ℝ 2 v → ContDiff ℝ 2 w →
      IsHarmonicRadialSourcePair (radialShootingA (s i))
        (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold)
        (radialMatchedProfile (s i) (z i)) ((ell : ℂ)*(ell+10)) (x i) v w u.first u.second →
      (deriv v R,deriv w R)=radialMatchedCanonicalRobin (s i) (z i) R (Y i) (Z i) (x i) (v R,w R)+
        deriv (radialMatchedCanonicalRobin (s i) (z i) R (Y i) (Z i)) (x i) (u.first R,u.second R) →
      False := by
  have hhalf₀ : -(1/32 : ℝ) < lam₀.re := by
    rcases hsym with ⟨_,rfl | rfl⟩ | ⟨_,rfl⟩ <;> norm_num
  have hsimple := radialMatchedCanonicalPencil_eventually_simple hRou s hs z z₀ hz hz₁ hz₀
    hX hm ell Y Z hY hZ R hR hLR F hmass lam₀ hsym hdet x hx
  have hval := (radialMatchedCanonicalValueDet_joint_tendsto s hs z z₀ hz ell Y Z hY hZ
    R hR lam₀ hhalf₀.le).comp (tendsto_id.prodMk hx)
  have hd := hval.eventually (eventually_ne_nhds hdet)
  have hh := (Complex.continuous_re.continuousAt.tendsto.comp hx).eventually
    (lt_mem_nhds hhalf₀)
  filter_upwards [hsimple,hd,hh] with i hi hdi hhi
  intro u v w hv hw₂ he hb
  obtain ⟨v₀,v₁,hne,hker,hchain⟩ := radialSpectralMode_canonical_source_chain
    (s i) ell i N hN (z i) (hX i) (hm i) R _ hR F (hw i) (hp i) (ha i)
    (x i) hhi.le u (Y i) (Z i) (hY i) (hZ i) hdi v w hv hw₂ he hb
  exact hi.2 v₀ v₁ hker hne hchain

end DefocusingNLS

end OAI
