import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralCanonicalKernel
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCanonicalValueDet

namespace OAI

/-! Nonzero canonical compact-pencil kernels along a sequence of actual radial modes. -/

open Filter Topology Set
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialSpectralMode_canonical_kernel_sequence
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
    (F : SpectralPenaltyFamily R (radialShootingR (profileMatchingParameter z₀)))
    (lam₀ : ℂ) (hhalf₀ : -(1/32 : ℝ) ≤ lam₀.re)
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell
        (radialShootingB (profileMatchingParameter z₀)) lam₀ R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell
        (radialShootingB (profileMatchingParameter z₀)) lam₀ R)) ≠ 0)
    (hw : ∀ i, (F.weight i).density=radialMatchedMassFunction (s i) (z i))
    (hp : ∀ i, F.pressure i=fun r =>
      ‖radialMatchedProfile (s i) (z i) r‖^(2*(s i+radialInnerShootingThreshold)))
    (ha : ∀ i, F.scale i=radialShootingA (s i))
    (N : ℕ) (hN : 7 ≤ N) (x : ℕ → ℂ) (hx : Tendsto x atTop (𝓝 lam₀))
    (hhalf : ∀ i, -(1/32 : ℝ) ≤ (x i).re)
    (mode : ∀ i, RadialSpectralMode (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold) N
      (radialMatchedProfile (s i) (z i)) ((ell : ℂ)*(ell+10)) (x i)) :
    let hR₀ : 0 < R := (by linarith [innerBoundaryRadius_bounds.1])
    ∃ v : ℕ → SpectralRadialObservationSpace R, ∀ᶠ i in atTop,
      F.compactPencil ell hR₀ i
        (radialMatchedWeakOperator (s i) ell (z i) (hX i) (hm i) R hR₀ (x i)
          (radialMatchedCanonicalFlux (s i) (z i) R (Y i) (Z i) (x i))) (v i)=v i ∧ v i ≠ 0 := by
  dsimp only
  have hR₀ : 0 < R := by linarith [innerBoundaryRadius_bounds.1]
  have hj := radialMatchedCanonicalValueDet_joint_tendsto s hs z z₀ hz ell Y Z hY hZ
    R hR lam₀ hhalf₀
  have hd := (hj.comp (tendsto_id.prodMk hx)).eventually (eventually_ne_nhds hdet)
  let P := fun i => F.compactPencil ell hR₀ i
    (radialMatchedWeakOperator (s i) ell (z i) (hX i) (hm i) R hR₀ (x i)
      (radialMatchedCanonicalFlux (s i) (z i) R (Y i) (Z i) (x i)))
  refine Filter.Eventually.choice (r := fun i v => P i v=v ∧ v ≠ 0) ?_
  filter_upwards [hd] with i hi
  obtain ⟨v,hv,hfix⟩ := radialSpectralMode_canonical_kernel (s i) ell i N hN (z i)
    (hX i) (hm i) R _ hR F (hw i) (hp i) (ha i) (x i) (hhalf i) (mode i)
    (Y i) (Z i) (hY i) (hZ i) hi
  exact ⟨v,hfix,hv⟩

end DefocusingNLS

end OAI
