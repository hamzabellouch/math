import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCanonicalRobinJoint
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialShootingCanonicalValueDet

namespace OAI

/-! Joint convergence of the canonical outgoing value determinant. -/

open Filter Topology Set
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialMatchedCanonicalValueDet_joint_tendsto
    (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀)) (ell : ℕ)
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
    (lam₀ : ℂ) (hlam₀ : -(1/32 : ℝ) ≤ lam₀.re)
    : Tendsto (fun p : ℕ × ℂ => spectralValueDet (spectralPhysicalValueMap (spectralPhysicalPair (radialShootingNu (s p.1+radialInnerShootingThreshold) (z p.1)-2*p.2) (star (radialShootingNu (s p.1+radialInnerShootingThreshold) (z p.1))-2*p.2) (Y p.1 p.2) R)) (spectralPhysicalValueMap (spectralPhysicalPair (radialShootingNu (s p.1+radialInnerShootingThreshold) (z p.1)-2*p.2) (star (radialShootingNu (s p.1+radialInnerShootingThreshold) (z p.1))-2*p.2) (Z p.1 p.2) R)))
      (atTop ×ˢ 𝓝 lam₀) (𝓝 (spectralValueDet
        (spectralPhysicalValueMap (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z₀)) lam₀ R))
        (spectralPhysicalValueMap (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z₀)) lam₀ R)))) := by
  let N := fun i => s i+radialInnerShootingThreshold
  have hN : StrictMono N := fun i j hij => Nat.add_lt_add_right (hs hij) _
  let ze := radialIndexedExtension N z (fun _ => z₀)
  have hze : Tendsto ze atTop (𝓝 z₀) := radialIndexedExtension_constant_tendsto N hN z z₀ hz
  obtain ⟨Ye,hYe,hYc⟩ := radialCanonicalExtension N hN z z₀ ell (1,0) Y hY
  obtain ⟨Ze,hZe,hZc⟩ := radialCanonicalExtension N hN z z₀ ell (0,1) Z hZ
  have hR1 : 1 ≤ R := innerBoundaryRadius_bounds.1.trans hR.le
  have hlog : Real.log innerBoundaryRadius ≤ Real.log R :=
    Real.log_le_log (by linarith [innerBoundaryRadius_bounds.1]) hR.le
  have hh := radialShooting_canonical_valueDet_joint_limit ze z₀ hze ell Ye Ze hYc hZc
    R hR1 hlog lam₀ hlam₀
  have hmap : Tendsto (fun p : ℕ × ℂ => (N p.1,p.2))
      (atTop ×ˢ 𝓝 lam₀) (atTop ×ˢ 𝓝 lam₀) :=
    hN.tendsto_atTop.prodMap tendsto_id
  have hh' := hh.comp hmap
  simpa only [Function.comp_def,ze,radialIndexedExtension_apply N hN,hYe,hZe,N] using hh'

end DefocusingNLS

end OAI
