import OAI.Geometry.RCD.Metric.CompactFactorL2

namespace OAI

/-! # Time derivatives of the actual compact endpoint heat factors -/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_factor_derivative {S : Set X} [CompactSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (ρ : X → ℝ)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {C : ℝ≥0}
    (hC : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ C)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : C(S, ℝ)) :
    ∃ f : Lp ℝ 2 (hausdorff n X), HasBoundedAmplitude f ∧
      (∀ (t : ℝ) (ht : 0 < t) (x : X), hX.compactHeatFactor hn p ν F t ht x =
        kernelHeat (hausdorff n X) hX.quadratic (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) t f x) ∧
      ∀ (t : ℝ), 0 < t → ∀ x : X,
        HasDerivAt (fun s => ∫ a, hX.canonicalHeatKernel hn p s x a*F a ∂ν)
          (kernelHeatGeneratorSource (hausdorff n X) hX.quadratic
            (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) t f x) t := by
  obtain ⟨f,hf,he⟩ := hX.compact_heat_factor_L2 hn p ν ρ hρ hρ0 hC hν F
  refine ⟨f,hf,he,?_⟩
  intro t ht x
  apply (kernelHeat_generator_hasDerivAt (hausdorff n X) hX.quadratic
    (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) f ht x).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact he s hs x

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
