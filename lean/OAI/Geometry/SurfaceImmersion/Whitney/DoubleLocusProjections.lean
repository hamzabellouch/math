import OAI.Geometry.SurfaceImmersion.Whitney.DoubleLocusSmoothStructure

namespace OAI

/-! The actual two projections from the smooth double locus to the surface
are smooth; their combined derivative is injective. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3}

theorem doubleLocus_projections_smooth
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y)) :
    let :=  doubleLocusChartedSpace hf hreg
    ContMDiff 𝓘(ℝ) planeModel ∞ (fun p : surfaceDoublePairs f => p.val.1) ∧
      ContMDiff 𝓘(ℝ) planeModel ∞ (fun p : surfaceDoublePairs f => p.val.2) := by
  let :=  doubleLocusChartedSpace hf hreg
  let :=  doubleLocus_isManifold hf hreg
  constructor
  · intro p
    let c := transverseDoubleChart hf hreg p
    have hp : p ∈ c.coord.source := transverseDoubleChart_mem hf hreg p
    have hcp : c.coord p ∈ c.coord.target := c.coord.map_source hp
    have hc : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ c.coord p :=
      contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hp
    have hA := c.inverse_left_smooth.contMDiffAt (c.coord.open_target.mem_nhds hcp)
    apply (hA.comp p hc).congr_of_eventuallyEq
    filter_upwards [c.coord.open_source.mem_nhds hp] with q hq
    change q.val.1 = (c.coord.symm (c.coord q)).val.1
    rw [c.coord.left_inv hq]
  · intro p
    let c := transverseDoubleChart hf hreg p
    have hp : p ∈ c.coord.source := transverseDoubleChart_mem hf hreg p
    have hcp : c.coord p ∈ c.coord.target := c.coord.map_source hp
    have hc : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ c.coord p :=
      contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hp
    have hA := c.inverse_right_smooth.contMDiffAt (c.coord.open_target.mem_nhds hcp)
    apply (hA.comp p hc).congr_of_eventuallyEq
    filter_upwards [c.coord.open_source.mem_nhds hp] with q hq
    change q.val.2 = (c.coord.symm (c.coord q)).val.2
    rw [c.coord.left_inv hq]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
