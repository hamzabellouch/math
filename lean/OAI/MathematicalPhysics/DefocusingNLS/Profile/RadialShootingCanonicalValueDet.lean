import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialShootingCanonicalRobin

namespace OAI

/-! Joint convergence of the canonical outgoing value determinant. -/

open Filter Topology Set
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialShooting_canonical_valueDet_joint_limit
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀)) (ell : ℕ)
    (Y Z : ℕ → ℂ → ℝ → E₄)
    (hY : ∀ᶠ n in atTop, IsCanonicalHolomorphicColumn (radialShootingNu n (z n))
      ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM (z n)) n
      (Real.log innerBoundaryRadius) (1,0) (Y n))
    (hZ : ∀ᶠ n in atTop, IsCanonicalHolomorphicColumn (radialShootingNu n (z n))
      ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM (z n)) n
      (Real.log innerBoundaryRadius) (0,1) (Z n))
    (R : ℝ) (hR : 1 ≤ R) (hLR : Real.log innerBoundaryRadius ≤ Real.log R)
    (lam₀ : ℂ) (hlam₀ : -(1/32 : ℝ) ≤ lam₀.re)
    : Tendsto (fun p : ℕ × ℂ => spectralValueDet (spectralPhysicalValueMap (spectralPhysicalPair (radialShootingNu p.1 (z p.1)-2*p.2) (star (radialShootingNu p.1 (z p.1))-2*p.2) (Y p.1 p.2) R)) (spectralPhysicalValueMap (spectralPhysicalPair (radialShootingNu p.1 (z p.1)-2*p.2) (star (radialShootingNu p.1 (z p.1))-2*p.2) (Z p.1 p.2) R)))
      (atTop ×ˢ 𝓝 lam₀) (𝓝 (spectralValueDet
        (spectralPhysicalValueMap (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z₀)) lam₀ R))
        (spectralPhysicalValueMap (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z₀)) lam₀ R)))) := by
  refine spectral_joint_of_moving_parameters (fun n lam => spectralValueDet (spectralPhysicalValueMap (spectralPhysicalPair (radialShootingNu n (z n)-2*lam) (star (radialShootingNu n (z n))-2*lam) (Y n lam) R)) (spectralPhysicalValueMap (spectralPhysicalPair (radialShootingNu n (z n)-2*lam) (star (radialShootingNu n (z n))-2*lam) (Z n lam) R))) lam₀ _ ?_
  intro lam hlam
  obtain ⟨hYlim,hZlim⟩ := radialShooting_canonical_fixed_limit z z₀ hz ell Y Z hY hZ
    lam lam₀ hlam hlam₀ (Real.log R) (Real.log_nonneg hR) hLR
  have hν := radialShootingNu_parameter_tendsto z z₀ hz
  have hp := hν.sub (hlam.const_mul 2)
  have hm := hν.star.sub (hlam.const_mul 2)
  have hPY := spectralPhysicalPair_tendsto _ _ _ _ (fun n => Y n (lam n)) _ R hp hm
    (hYlim.tendsto_at (le_refl (Real.log R)))
  have hPZ := spectralPhysicalPair_tendsto _ _ _ _ (fun n => Z n (lam n)) _ R hp hm
    (hZlim.tendsto_at (le_refl (Real.log R)))
  have hD := spectralValueDet_tendsto _ _ _ _
    (spectralPhysicalValueMap.continuous.continuousAt.tendsto.comp hPY)
    (spectralPhysicalValueMap.continuous.continuousAt.tendsto.comp hPZ)
  simpa only [Function.comp_def,spectralFreePhysicalPair_first,spectralFreePhysicalPair_second] using hD

end DefocusingNLS

end OAI
