import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreePhysicalEquation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedSmooth
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalRobinLimit

namespace OAI

/-! Pointwise convergence of both physical profile coordinates on the exterior. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialShootingPhysicalJet_tendsto (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀)) (R : ℝ) (hR : innerBoundaryRadius ≤ R) :
    Tendsto (fun i => radialShootingPhysicalJet (s i) (z i) R) atTop
      (𝓝 (radialShootingFreeJet z₀ R)) := by
  let N := fun i => s i+radialInnerShootingThreshold
  have hN : StrictMono N := fun i j hij => Nat.add_lt_add_right (hs hij) _
  let ν := fun i => radialShootingNu (N i) (z i)
  have hν : Tendsto ν atTop (𝓝 (-2*radialShootingQ z₀)) :=
    radialShootingNu_subsequence_tendsto N hN z z₀ hz
  obtain ⟨δ,ρ,hδ,hδm,hsmall,hρ,hupper,hlower⟩ := radialShooting_free_annulus z₀
  have hq : -1 < (radialShootingQ z₀).re := by simp [radialShootingQ]
  have hH := (radialExteriorCanonical_H_limit_subsequence N hN ν
    (fun i => radialShootingM (z i)) (radialShootingQ z₀) (radialShootingM z₀)
    hq hν (continuous_radialShootingM.continuousAt.tendsto.comp hz) δ ρ
    (Real.log innerBoundaryRadius) hδ hδm hsmall hρ hupper hlower).2
  have hpoint := hH.tendsto_at
    (Real.log_le_log (by linarith [innerBoundaryRadius_bounds.1]) hR)
  exact spectralPhysicalJet_tendsto ν (-2*radialShootingQ z₀) _ _ R hν hpoint

theorem radialMatchedProfile_deriv_tendsto (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0)
    (R : ℝ) (hR : innerBoundaryRadius < R) :
    Tendsto (fun i => deriv (radialMatchedProfile (s i) (z i)) R) atTop
      (𝓝 (deriv (radialShootingFreeExterior z₀) R)) := by
  have hR₀ : 0 < R := (by linarith [innerBoundaryRadius_bounds.1] : 0 < innerBoundaryRadius).trans hR
  have he (i : ℕ) : (radialShootingPhysicalJet (s i) (z i) R).2=
      deriv (radialMatchedProfile (s i) (z i)) R := by
    rw [(radialMatchedProfile_hasDerivAt (s i) (z i) (hX i) (hm i) R hR₀).deriv]
    simp only [radialMatchedJet,ite_eq_right (not_le.mpr hR)]
  simpa only [he,← (radialShootingFreeExterior_hasDerivAt z₀ R hR₀).deriv] using
    (radialShootingPhysicalJet_tendsto s hs z z₀ hz R hR.le).snd_nhds

end DefocusingNLS

end OAI
