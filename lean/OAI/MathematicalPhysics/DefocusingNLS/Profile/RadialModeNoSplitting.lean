import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCanonicalNoSplitting
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralCanonicalKernelSequence
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSymmetrySpectralMode

namespace OAI

/-! Actual extra radial eigenvalues cannot converge to a symmetry eigenvalue. -/

open Filter Topology Set
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialMatchedMode_no_extra_sequence (hRou : RectangleRouche)
    (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hz₁ : z₀.val.1=0) (hz₀ : diskProfile (profileMatchingParameter z₀)=0)
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
    (hmass : F.limitWeight.density=radialMatchedFreeMassFunction z₀)
    (lam₀ : ℂ) (hsym : (ell=0 ∧ (lam₀=0 ∨ lam₀=1)) ∨ (ell=1 ∧ lam₀=1/2))
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
    (hne : ∀ᶠ i in atTop, x i ≠ lam₀)
    (hhalf : ∀ i, -(1/32 : ℝ) ≤ (x i).re)
    (mode : ∀ i, RadialSpectralMode (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold) N
      (radialMatchedProfile (s i) (z i)) ((ell : ℂ)*(ell+10)) (x i)) : False := by
  have hhalf₀ : -(1/32 : ℝ) ≤ lam₀.re := by
    rcases hsym with ⟨_,rfl | rfl⟩ | ⟨_,rfl⟩ <;> norm_num
  obtain ⟨u,hu⟩ := radialSpectralMode_canonical_kernel_sequence s hs z z₀ hz hX hm ell
    Y Z hY hZ R hR F lam₀ hhalf₀ hdet hw hp ha N hN x hx hhalf mode
  obtain ⟨v,hv⟩ := radialSpectralMode_canonical_kernel_sequence s hs z z₀ hz hX hm ell
    Y Z hY hZ R hR F lam₀ hhalf₀ hdet hw hp ha N hN (fun _ => lam₀) tendsto_const_nhds
    (fun _ => hhalf₀) (fun i => radialMatchedSymmetryMode (s i) ell N hN (z i) (hX i) (hm i) lam₀ hsym)
  exact radialMatchedCanonicalPencil_no_splitting hRou s hs z z₀ hz hz₁ hz₀ hX hm ell
    Y Z hY hZ R hR hLR F hmass lam₀ hsym hdet x (fun _ => lam₀) hx tendsto_const_nhds hne u v hu hv

end DefocusingNLS

end OAI
