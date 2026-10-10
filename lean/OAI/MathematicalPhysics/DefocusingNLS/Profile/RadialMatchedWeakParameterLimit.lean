import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakOperator

namespace OAI

/-! The actual weak operators converge when the spectral parameter also varies. -/

open Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedWeakOperator_parameter_tendsto (ell : ℕ) (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0) (R : ℝ) (hR : 0 < R)
    (ζ : ℕ → ℂ) (ζ₀ : ℂ) (hζ : Tendsto ζ atTop (𝓝 ζ₀)) (B : ℕ → ℂ × ℂ →L[ℂ] ℂ × ℂ) (B₀ : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hB : Tendsto B atTop (𝓝 B₀)) :
    Tendsto (fun i => radialMatchedWeakOperator (s i) ell (z i) (hX i) (hm i) R hR (ζ i) (B i))
      atTop (𝓝 (radialMatchedLimitWeakOperator ell z₀
        (radialMatchedFreeMassFunction_continuous s hs z z₀ hz hX hm) R hR ζ₀ B₀)) := by
  have hr : Tendsto (fun i => 6-2*radialShootingA (s i)) atTop (𝓝 (6 : ℝ)) := by
    simpa only [Function.comp_def,mul_zero,sub_zero] using
      tendsto_const_nhds.sub ((radialShootingA_tendsto_zero.comp hs.tendsto_atTop).const_mul 2)
  have hc : Tendsto (fun i => ((6-2*radialShootingA (s i) : ℝ) : ℂ)) atTop (𝓝 (6 : ℂ)) := by
    exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  unfold radialMatchedWeakOperator radialMatchedLimitWeakOperator
  apply spectralLowerOrderOperator_tendsto
  · exact radialMatched_massMultiplier_tendsto s hs z z₀ hz hX hm R
  · exact radialMatched_transportMultiplier_tendsto s hs z z₀ hz hX hm R hR.le
  · exact hc
  · exact hζ
  · exact hB

end DefocusingNLS

end OAI
