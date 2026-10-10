import OAI.Geometry.RCD.Heat.CompactHeatFactors
import OAI.Geometry.RCD.Metric.CompactWeightedDensityIntegral
import OAI.Geometry.RCD.Metric.CompactWeightedDensityL2
import OAI.Geometry.RCD.Heat.KernelHeatGeneratorDerivative

namespace OAI

/-! # The constructed compact heat factor is the actual L² heat flow

The initial datum is the endpoint density multiplied by the zero-extended
continuous scaling factor. Its L² class and bounded amplitude are proved.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_factor_L2 {S : Set X} [CompactSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (ρ : X → ℝ)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {C : ℝ≥0}
    (hC : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ C)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : C(S, ℝ)) :
    ∃ f : Lp ℝ 2 (hausdorff n X), HasBoundedAmplitude f ∧
      ∀ (t : ℝ) (ht : 0 < t) (x : X), hX.compactHeatFactor hn p ν F t ht x =
        kernelHeat (hausdorff n X) hX.quadratic (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) t f x := by
  let μ := hausdorff n X
  have hS : IsCompact S := isCompact_iff_compactSpace.mpr inferInstance
  let f₀ := fun x => ρ x*compactFactorExtension F x
  have hm : MemLp f₀ 2 μ := compact_weighted_density_memLp hS F μ hρ hC
  let f := hm.toLp f₀
  have hf : f =ᵐ[μ] f₀ := hm.coeFn_toLp
  obtain ⟨D,hD⟩ := compact_weighted_density_bounded hS F μ hC
  have hbound : HasBoundedAmplitude f := by
    refine ⟨D,?_⟩
    filter_upwards [hf,hD] with x hx hDx
    rw [hx]
    exact hDx
  refine ⟨f,hbound,?_⟩
  intro t ht x
  change (∫ a, hX.canonicalHeatKernel hn p t x a*F a ∂ν) = _
  calc
    _ = ∫ y, hX.canonicalHeatKernel hn p t x y*f₀ y ∂μ :=
      compact_weighted_density_integral hS.isClosed.measurableSet μ ν ρ hρ hρ0 hν F _
    _ = ∫ y, hX.canonicalHeatKernel hn p t x y*f y ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf] with y hy
      rw [hy]
    _ = _ := (kernelHeat_eq_integral μ hX.quadratic
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) ht f x).symm

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
