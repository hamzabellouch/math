import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessianTransport
open Set Filter MeasureTheory
open scoped Topology

lemma deriv_le_of_eventually_upper_right_slope {f : ℝ → ℝ} {t I : ℝ}
    (hf : DifferentiableAt ℝ f t)
    (hu : ∀ r : ℝ,I < r → ∀ᶠ s in 𝓝[>] t,slope f t s < r) : deriv f t ≤ I := by
  have hd : HasDerivWithinAt f (deriv f t) (Ioi t) t := hf.hasDerivAt.hasDerivWithinAt
  have hl : Tendsto (slope f t) (𝓝[>] t) (𝓝 (deriv f t)) :=
    (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).mp hd
  apply le_of_forall_pos_le_add
  intro ε hε
  exact le_of_tendsto hl ((hu (I+ε) (lt_add_of_pos_right I hε)).mono fun s hs => hs.le)

lemma sub_le_integral_of_upper_right_slope {f I : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b) (hI : IntervalIntegrable I volume a b)
    (hu : ∀ᵐ t ∂volume.restrict (Icc a b),
      ∀ r : ℝ,I t < r → ∀ᶠ s in 𝓝[>] t,slope f t s < r) :
    f b-f a ≤ ∫ t in a..b,I t := by
  rw [← hf.integral_deriv_eq_sub]
  apply intervalIntegral.integral_mono_ae_restrict hab hf.intervalIntegrable_deriv hI
  have hdiff : ∀ᵐ t ∂volume.restrict (Icc a b), DifferentiableAt ℝ f t := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hf.ae_differentiableAt] with t ht htI
    exact ht (by rwa [uIcc_of_le hab])
  filter_upwards [hdiff,hu] with t ht hu
  exact deriv_le_of_eventually_upper_right_slope ht hu
end WeakHessianTransport
end
end InlinedFile0

end OAI
