import OAI.Geometry.SurfaceImmersion.Whitney.DoubleLocusImmersion
import OAI.Geometry.SurfaceImmersion.Geometry.PairedMapDerivatives

namespace OAI

/-! Both source projections, and the common image curve, are immersions
at any double pair consisting of two regular surface points. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3}

theorem doubleLocus_regular_projections
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (p : surfaceDoublePairs f)
    (hA : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p.val.1))
    (hB : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p.val.2)) :
    let := doubleLocusChartedSpace hf hreg
    Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun q : surfaceDoublePairs f => q.val.1) p) ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun q : surfaceDoublePairs f => q.val.2) p) ∧
      Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ,ProjectionTarget 3)
        (fun q : surfaceDoublePairs f => f q.val.1) p) := by
  let := doubleLocusChartedSpace hf hreg
  let := doubleLocus_isManifold hf hreg
  obtain ⟨hleft,hright⟩ := doubleLocus_projections_smooth hf hreg
  have hpair := doubleLocus_inclusion_immersion hf hreg p
  dsimp only
  exact regular_paired_map_derivatives hf hleft hright (fun q => q.property.2) p hpair hA hB

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
