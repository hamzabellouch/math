import OAI.Geometry.RCD.Sobolev.GammaL2Stability

namespace OAI

/-! # Energy-density continuity along bounded-gradient Sobolev paths -/

open Filter MeasureTheory
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem gammaL2_continuousAt {F : ℝ → SobolevSpace μ hQ} {t : ℝ}
    (L : ℝ≥0) (hL : ∀ s, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (F s) x≤L)
    (hF : ContinuousAt F t) :
    ContinuousAt (fun s => (localGamma_memLp_of_bounded_gradient μ hQ (F s) (F s)
      L (hL s)).toLp (localGamma μ hQ (F s) (F s))) t := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun s => gammaL2_sub_norm_le μ hQ (F s) (F t) L L (hL s) (hL t) _ _)
  simpa only [sub_self,norm_zero,mul_zero] using
    (hF.tendsto.sub_const (F t)).norm.const_mul ((L:ℝ)+L)

end RegularPointCoordinates

end

end OAI
