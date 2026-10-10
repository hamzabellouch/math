import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakParameterLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeakJointLimit

namespace OAI

/-! The actual finite-power weak operator converges jointly with its spectral
parameter, once the outgoing Robin family has the corresponding joint limit. -/

open Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedWeakOperator_joint_tendsto (ell : ℕ) (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0) (R : ℝ) (hR : 0 < R)
    (ζ₀ : ℂ) (B : ℕ → ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (B₀ : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hB : Tendsto (fun p : ℕ × ℂ => B p.1 p.2) (atTop ×ˢ 𝓝 ζ₀) (𝓝 B₀)) :
    Tendsto (fun p : ℕ × ℂ => radialMatchedWeakOperator (s p.1) ell (z p.1)
      (hX p.1) (hm p.1) R hR p.2 (B p.1 p.2)) (atTop ×ˢ 𝓝 ζ₀)
      (𝓝 (radialMatchedLimitWeakOperator ell z₀
        (radialMatchedFreeMassFunction_continuous s hs z z₀ hz hX hm) R hR ζ₀ B₀)) := by
  have hr : Tendsto (fun i => 6-2*radialShootingA (s i)) atTop (𝓝 (6 : ℝ)) := by
    simpa only [Function.comp_def,mul_zero,sub_zero] using
      tendsto_const_nhds.sub ((radialShootingA_tendsto_zero.comp hs.tendsto_atTop).const_mul 2)
  have hc : Tendsto (fun i => ((6-2*radialShootingA (s i) : ℝ) : ℂ)) atTop (𝓝 (6 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  unfold radialMatchedWeakOperator radialMatchedLimitWeakOperator
  apply spectralLowerOrderOperator_tendsto_filter
  · exact (radialMatched_massMultiplier_tendsto s hs z z₀ hz hX hm R).comp tendsto_fst
  · exact (radialMatched_transportMultiplier_tendsto s hs z z₀ hz hX hm R hR.le).comp tendsto_fst
  · exact hc.comp tendsto_fst
  · exact tendsto_snd
  · exact hB

end DefocusingNLS

end OAI
