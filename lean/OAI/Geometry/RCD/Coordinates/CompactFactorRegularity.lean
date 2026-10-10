import OAI.Geometry.RCD.Metric.CompactFactorL2
import OAI.Geometry.RCD.Coordinates.KernelHeatBoundedRegularity
import OAI.Geometry.RCD.Heat.KernelHeatSpatialSource

namespace OAI

/-! # Bounded Lipschitz and weak-Laplacian data for the actual heat factors -/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_factor_regularity {S : Set X} [CompactSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (ρ : X → ℝ)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {C : ℝ≥0}
    (hC : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ C)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : C(S, ℝ)) :
    ∃ D : ℝ≥0, ∀ (t : ℝ) (ht : 0 < t),
      LipschitzWith ⟨Real.sqrt ((D:ℝ)^2/(2*t*Real.exp (-2 * |K| * t))),Real.sqrt_nonneg _⟩
        (hX.compactHeatFactor hn p ν F t ht) ∧
      (∀ x, |hX.compactHeatFactor hn p ν F t ht x| ≤ D) ∧
      ∃ (u : SobolevSpace (hausdorff n X) hX.quadratic) (d : Lp ℝ 2 (hausdorff n X)),
        (hX.compactHeatFactor hn p ν F t ht =ᵐ[hausdorff n X]
          SobolevSpace.toLp (hausdorff n X) hX.quadratic u) ∧
        IsWeakLaplacian (hausdorff n X) hX.quadratic u d := by
  obtain ⟨f,hf,he⟩ := hX.compact_heat_factor_L2 hn p ν ρ hρ hρ0 hC hν F
  obtain ⟨D,hD⟩ := hf
  refine ⟨D,?_⟩
  intro t ht
  have hfun : hX.compactHeatFactor hn p ν F t ht =
      kernelHeat (hausdorff n X) hX.quadratic
        (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) t f := funext (he t ht)
  rw [hfun]
  obtain ⟨hl,hb⟩ := hX.kernelHeat_bounded_regularity hn p
    (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) f D hD t ht
  obtain ⟨u,d,hu,hd,_⟩ := kernelHeat_spatial_source (hausdorff n X) hX.quadratic
    (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) f ht
  exact ⟨hl,hb,u,d,hu,hd⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
