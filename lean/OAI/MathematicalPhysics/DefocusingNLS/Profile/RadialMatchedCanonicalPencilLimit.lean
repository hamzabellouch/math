import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCanonicalUniform
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedPencilUniformLimit

namespace OAI

/-! Local uniform convergence of the actual canonical compact spectral pencil. -/

open Filter Topology Set
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable local instance compactCanonicalNormed (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R) := by
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem radialMatchedCanonicalPencil_locallyUniform
    (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0) (ell : ℕ)
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
    (U : Set ℂ) (hU : IsOpen U)
    (hhalf : ∀ lam ∈ U, -(1/32 : ℝ) ≤ lam.re)
    (hd : ∀ lam ∈ U, spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell
        (radialShootingB (profileMatchingParameter z₀)) lam R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell
        (radialShootingB (profileMatchingParameter z₀)) lam R)) ≠ 0) :
    let hL := radialMatchedCore_radius_pos z₀
    let hR₀ := hL.trans hLR
    TendstoLocallyUniformlyOn (fun i lam => F.compactPencil ell hR₀ i
      (radialMatchedWeakOperator (s i) ell (z i) (hX i) (hm i) R hR₀ lam
        (radialMatchedCanonicalFlux (s i) (z i) R (Y i) (Z i) lam)))
      (radialMatchedFreePencil ell z₀
        (radialMatchedFreeMassFunction_continuous s hs z z₀ hz hX hm) R hLR F) atTop U := by
  have hB := radialMatchedCanonicalFlux_locallyUniform s hs z z₀ hz hX hm ell
    Y Z hY hZ R hR hLR U hU hhalf hd
  exact radialMatchedPencil_tendstoLocallyUniformlyOn ell s hs z z₀ hz hX hm R hLR F U hU
    (fun i => radialMatchedCanonicalFlux (s i) (z i) R (Y i) (Z i))
    (radialMatchedFreeBoundary ell z₀ R) hB
    (fun lam hlam => radialMatchedFreeBoundary_analyticAt ell z₀ R hLR lam
      (hhalf lam hlam) (hd lam hlam))

end DefocusingNLS

end OAI
