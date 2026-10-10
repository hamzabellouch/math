import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedFreePencilDerivative

namespace OAI

/-! The actual constrained free compact pencil has no first analytic chain,
as used in the paper's spectral simplicity argument. -/

namespace DefocusingNLS
open ProfileCertificate

noncomputable local instance freePencilChainLiftNormed (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R) := by
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem radialMatchedFreePencil_chain_lift (ell : ℕ) (z : ProfileMatchingBall)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (s : SpectralPenaltyFamily R (radialShootingR (profileMatchingParameter z)))
    (hmass : s.limitWeight.density=radialMatchedFreeMassFunction z)
    (lam : ℂ) (hhalf : -(1/32 : ℝ) ≤ lam.re)
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) lam R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) lam R)) ≠ 0)
    (v₀ v₁ : SpectralRadialObservationSpace R)
    (h₀ : radialMatchedFreePencil ell z hc R hLR s lam v₀ = v₀)
    (h₁ : v₁-radialMatchedFreePencil ell z hc R hLR s lam v₁ =
      deriv (radialMatchedFreePencil ell z hc R hLR s) lam v₀) :

    let L := radialShootingR (profileMatchingParameter z)
    let hR := (radialMatchedCore_radius_pos z).trans hLR
    let B := radialMatchedFreeBoundary ell z R
    let K := radialMatchedLimitWeakOperator ell z hc R hR lam (B lam)
    let D := spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R s.limitWeight) (deriv B lam)
    ∃ u₀ u₁ : SpectralHarmonicPair ell R,
      u₀ ∈ spectralHarmonicCoreSubspace ell R L ∧
      u₁ ∈ spectralHarmonicCoreSubspace ell R L ∧
      spectralHarmonicObservation ell R hR u₀=v₀ ∧
      spectralHarmonicObservation ell R hR u₁=v₁ ∧
      (∀ v : spectralHarmonicCoreSubspace ell R L,
        spectralHarmonicPairComplexForm ell R s.limitWeight u₀ v=inner ℂ (K v₀) v) ∧
      ∀ v : spectralHarmonicCoreSubspace ell R L,
        spectralHarmonicPairComplexForm ell R s.limitWeight u₁ v=inner ℂ (K v₁+D v₀) v := by
  let L := radialShootingR (profileMatchingParameter z)
  have hL : 0 < L := radialMatchedCore_radius_pos z
  let hR := hL.trans hLR
  let B := radialMatchedFreeBoundary ell z R
  let K := fun t => radialMatchedLimitWeakOperator ell z hc R hR t (B t)
  let D := spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R s.limitWeight) (deriv B lam)
  have hP := radialMatchedFreePencil_hasDerivAt ell z hc R hLR s hmass lam hhalf hdet
  have h₀' : s.limitPencil ell hL hLR (K lam) v₀=v₀ := by
    simpa only [radialMatchedFreePencil,K,B,hR] using h₀
  have h₁' : v₁-s.limitPencil ell hL hLR (K lam) v₁ = s.limitPencil ell hL hLR D v₀ := by
    have hd := congrArg (fun T : SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R => T v₀) hP.deriv
    simpa only [radialMatchedFreePencil,K,D,B,hR] using h₁.trans hd
  simpa only [K,D,B,hR,L] using
    s.limitPencil_chain_lift ell hL hLR (K lam) D v₀ v₁ h₀' h₁'

end DefocusingNLS

end OAI
