import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCompactJointLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralJointUniformLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLowerOrderAnalytic

namespace OAI

/-! Locally uniform convergence of the actual finite-power compact pencil
from locally uniform convergence of its outgoing boundary matrices. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

noncomputable local instance compactUniformNormed (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R) := by
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem radialMatchedPencil_tendstoLocallyUniformlyOn (ell : ℕ) (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0) (R : ℝ) (hLR : radialShootingR (profileMatchingParameter z₀)<R)
    (F : SpectralPenaltyFamily R (radialShootingR (profileMatchingParameter z₀)))
    (U : Set ℂ) (hU : IsOpen U)
    (B : ℕ → ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (B₀ : ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hB : TendstoLocallyUniformlyOn B B₀ atTop U)
    (hB₀ : AnalyticOnNhd ℂ B₀ U) :
    let hL := radialMatchedCore_radius_pos z₀
    let hR := hL.trans hLR
    TendstoLocallyUniformlyOn (fun i lam => F.compactPencil ell hR i
      (radialMatchedWeakOperator (s i) ell (z i) (hX i) (hm i) R hR lam (B i lam)))
      (fun lam => F.limitPencil ell hL hLR (radialMatchedLimitWeakOperator ell z₀
        (radialMatchedFreeMassFunction_continuous s hs z z₀ hz hX hm) R hR lam (B₀ lam)))
      atTop U := by
  let hL := radialMatchedCore_radius_pos z₀
  let hR := hL.trans hLR
  let hc := radialMatchedFreeMassFunction_continuous s hs z z₀ hz hX hm
  let P₀ := fun lam => F.limitPencil ell hL hLR
    (radialMatchedLimitWeakOperator ell z₀ hc R hR lam (B₀ lam))
  have hP₀ (lam : ℂ) (hlam : lam ∈ U) : AnalyticAt ℂ P₀ lam := by
    apply F.limitPencil_analyticAt ell hL hLR
    unfold radialMatchedLimitWeakOperator
    exact spectralLowerOrderOperator_analyticAt ell R hR _ _ 6 B₀ lam (hB₀ lam hlam)
  apply spectral_locallyUniform_of_joint _ P₀ U hU
  · intro lam hlam
    exact (hP₀ lam hlam).differentiableAt.continuousAt.continuousWithinAt
  · intro lam hlam
    have hBj := spectral_locallyUniform_joint_tendsto B B₀ U hU hB lam hlam
      (hB₀ lam hlam).differentiableAt.continuousAt
    exact radialMatchedPencil_joint_tendsto ell s hs z z₀ hz hX hm R hLR F lam B (B₀ lam) hBj

end DefocusingNLS

end OAI
