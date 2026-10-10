import OAI.Geometry.RCD.Heat.CanonicalKernelConstruction
import OAI.Geometry.RCD.Sobolev.CompactRestrictedLaw
import OAI.Geometry.RCD.Heat.CompactHeatFactors

namespace OAI

/-! # Passing a uniform-law heat factor through the actual kernel semigroup -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonical_uniform_bridge {S : Set X} [CompactSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν]
    (hν : ν.map Subtype.val = uniformOn (hausdorff n X) S)
    (hS0 : 0 < (hausdorff n X).real S)
    {s t M : ℝ} (hs : 0 < s) (ht : 0 < t) (x y : X)
    (hbound : ∀ q ∈ S, M ≤ hX.canonicalHeatKernel hn p t q y) :
    M*(hausdorff n X).real S*hX.compactHeatFactor hn p ν 1 s hs x ≤
      hX.canonicalHeatKernel hn p (s+t) x y := by
  let μ := hausdorff n X
  have hS : IsCompact S := isCompact_iff_compactSpace.mpr inferInstance
  have hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  have hi := hX.canonicalHeatKernel_integrable hn p s hs x
  have hm : Measurable (hX.canonicalHeatKernel hn p s x) :=
    (hX.canonicalHeatKernel_continuous_joint hn p s hs).comp
      (continuous_const.prodMk continuous_id) |>.measurable
  have he : μ.real S*hX.compactHeatFactor hn p ν 1 s hs x =
      ∫ q in S, hX.canonicalHeatKernel hn p s x q ∂μ := by
    have hh := restricted_law_integral μ ν hν _ hm
    change (∫ a : S, hX.canonicalHeatKernel hn p s x a ∂ν) = _ at hh
    change μ.real S*(∫ a : S, hX.canonicalHeatKernel hn p s x a*1 ∂ν) = _
    simp only [mul_one]
    rw [hh,← mul_assoc,mul_inv_cancel₀ hS0.ne',one_mul]
  rw [mul_assoc,he]
  rw [← hk.convolution s t hs ht x y,← integral_const_mul]
  calc
    _ ≤ ∫ q in S, hX.canonicalHeatKernel hn p s x q*hX.canonicalHeatKernel hn p t q y ∂μ := by
      apply setIntegral_mono_on (hi.integrableOn.const_mul M)
        (hk.convolution_integrable s t hs ht x y).integrableOn hS.isClosed.measurableSet
      intro q hq
      simpa only [mul_comm M] using
        mul_le_mul_of_nonneg_left (hbound q hq) (hk.nonneg s hs x q)
    _ ≤ _ := setIntegral_le_integral (hk.convolution_integrable s t hs ht x y)
      (Eventually.of_forall fun q => mul_nonneg (hk.nonneg s hs x q) (hk.nonneg t ht q y))

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
