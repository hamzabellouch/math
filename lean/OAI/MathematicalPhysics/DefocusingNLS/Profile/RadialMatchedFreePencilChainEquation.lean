import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedFreePencilDerivative

namespace OAI

/-! The actual constrained free compact pencil has no first analytic chain,
as used in the paper's spectral simplicity argument. -/

namespace DefocusingNLS
open ProfileCertificate

noncomputable local instance freePencilChainEquationNormed (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R) := by
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem radialMatchedFreePencil_chain_equation (ell : ℕ) (z : ProfileMatchingBall)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (s : SpectralPenaltyFamily R (radialShootingR (profileMatchingParameter z)))
    (hmass : s.limitWeight.density=radialMatchedFreeMassFunction z)
    (lam : ℂ) (hhalf : -(1/32 : ℝ) ≤ lam.re)
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) lam R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) lam R)) ≠ 0)
    (v₀ v₁ : SpectralRadialObservationSpace R)
    (h₁ : v₁-radialMatchedFreePencil ell z hc R hLR s lam v₁ =
      deriv (radialMatchedFreePencil ell z hc R hLR s) lam v₀) :
    let hL := radialMatchedCore_radius_pos z
    v₁-radialMatchedFreePencil ell z hc R hLR s lam v₁ =
      s.limitPencil ell hL hLR
        (spectralLowerOrderSlope ell R (hL.trans hLR)
          (spectralRadialWeightMultiplier R s.limitWeight)
          (deriv (radialMatchedFreeBoundary ell z R) lam)) v₀ := by
  have hP := radialMatchedFreePencil_hasDerivAt ell z hc R hLR s hmass lam hhalf hdet
  exact h₁.trans (congrArg (fun T : SpectralRadialObservationSpace R →L[ℂ]
    SpectralRadialObservationSpace R => T v₀) hP.deriv)

end DefocusingNLS

end OAI
