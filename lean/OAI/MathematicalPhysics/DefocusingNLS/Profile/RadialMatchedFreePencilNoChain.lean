import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedFreePencilChainLift
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakChainExclusion

namespace OAI

/-! The actual constrained free compact pencil has no first analytic chain,
as used in the paper's spectral simplicity argument. -/

namespace DefocusingNLS
open ProfileCertificate

noncomputable local instance freePencilNoChainNormed (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R) := by
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem radialMatchedFreePencil_no_chain (hRou : RectangleRouche) (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (s : SpectralPenaltyFamily R (radialShootingR (profileMatchingParameter z)))
    (hmass : s.limitWeight.density=radialMatchedFreeMassFunction z)
    (lam : ℂ) (hs : (ell=0 ∧ (lam=0 ∨ lam=1)) ∨ (ell=1 ∧ lam=1/2))
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) lam R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) lam R)) ≠ 0)
    (v₀ v₁ : SpectralRadialObservationSpace R) (hv₀ : v₀ ≠ 0)
    (h₀ : radialMatchedFreePencil ell z hc R hLR s lam v₀ = v₀) :
    v₁-radialMatchedFreePencil ell z hc R hLR s lam v₁ ≠
      deriv (radialMatchedFreePencil ell z hc R hLR s) lam v₀ := by
  intro h₁
  have hhalf : -(1/32 : ℝ) ≤ lam.re := by
    rcases hs with ⟨_,rfl | rfl⟩ | ⟨_,rfl⟩ <;> norm_num
  obtain ⟨u₀,u₁,hu₀,hu₁,ho₀,ho₁,he₀,he₁⟩ :=
    radialMatchedFreePencil_chain_lift ell z hc R hLR s hmass lam hhalf hdet v₀ v₁ h₀ h₁
  clear h₀ h₁
  subst v₀
  subst v₁
  refine radialMatchedWeak_chain_exclusion hRou ell z hz₁ hz hc R hLR s.limitWeight hmass
    lam (radialMatchedFreeBoundary ell z R lam) (deriv (radialMatchedFreeBoundary ell z R) lam)
    u₀ u₁ hu₀ hu₁ hs hv₀ hdet rfl ?_ ?_ ?_
  · exact (radialMatchedFreeBoundary_hasDerivAt ell z R hLR lam hhalf hdet).deriv
  · exact he₀
  · exact he₁

end DefocusingNLS

end OAI
