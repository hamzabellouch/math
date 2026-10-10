import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCanonicalPencilLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCanonicalNeighborhood
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedPencilAnalytic
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedFreePencilNoChain
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSimpleLimitNoJordan

namespace OAI

/-! The actual finite-power canonical pencils have no persisting first chain near a symmetry root. -/

open Filter Topology Set
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable local instance canonicalNoJordanNormed (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R) := by
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem radialMatchedCanonicalPencil_no_jordan (hRou : RectangleRouche)
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
    (x : ℕ → ℂ) (hx : Tendsto x atTop (𝓝 lam₀)) :
    let hR₀ := (radialMatchedCore_radius_pos z₀).trans hLR
    let P := fun i lam => F.compactPencil ell hR₀ i
      (radialMatchedWeakOperator (s i) ell (z i) (hX i) (hm i) R hR₀ lam
        (radialMatchedCanonicalFlux (s i) (z i) R (Y i) (Z i) lam))
    ∀ u v : ℕ → SpectralRadialObservationSpace R,
      (∀ᶠ i in atTop, P i (x i) (u i)=u i ∧ u i ≠ 0) →
      (∀ᶠ i in atTop, v i-P i (x i) (v i)=deriv (P i) (x i) (u i)) → False := by
  intro hR₀ P u v hu hv
  let hc := radialMatchedFreeMassFunction_continuous s hs z z₀ hz hX hm
  let f := radialMatchedFreePencil ell z₀ hc R hLR F
  have hhalf : -(1/32 : ℝ) < lam₀.re := by
    rcases hsym with ⟨_,rfl | rfl⟩ | ⟨_,rfl⟩ <;> norm_num
  obtain ⟨U,hU,hlam,hfree,hBA⟩ := radialMatchedCanonical_analytic_neighborhood
    s hs z z₀ hz ell Y Z hY hZ R hR hLR lam₀ hhalf hdet
  have hP : TendstoLocallyUniformlyOn P f atTop U :=
    radialMatchedCanonicalPencil_locallyUniform s hs z z₀ hz hX hm ell Y Z hY hZ
      R hR hLR F U hU (fun w hw => (hfree w hw).1) (fun w hw => (hfree w hw).2)
  have hPd : ∀ᶠ i in atTop, DifferentiableOn ℂ (P i) U := by
    filter_upwards [hBA] with i hi w hw
    exact (radialMatchedPencil_analyticAt (s i) ell i (z i) (hX i) (hm i) R
      (radialShootingR (profileMatchingParameter z₀)) hR₀ F
      (radialMatchedCanonicalFlux (s i) (z i) R (Y i) (Z i)) w (hi w hw)).differentiableAt.differentiableWithinAt
  have hcomp : IsCompactOperator (f lam₀) :=
    F.limitPencil_compact ell (radialMatchedCore_radius_pos z₀) hLR _
  apply spectral_simple_limit_no_jordan P f U hU hP hPd lam₀ hlam hcomp
    x hx u v hu hv
  · intro u₀ hne₀ hfix w hw
    exact radialMatchedFreePencil_kernel_line ell z₀ hz₁ hz₀ hc R hLR F hmass
      lam₀ hhalf.le hdet u₀ w hne₀ hfix hw
  · intro u₀ hne₀ hfix w
    exact radialMatchedFreePencil_no_chain hRou ell z₀ hz₁ hz₀ hc R hLR F hmass
      lam₀ hsym hdet u₀ w hne₀ hfix

end DefocusingNLS

end OAI
