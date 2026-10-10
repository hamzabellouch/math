import OAI.Geometry.SurfaceImmersion.Whitney.SmoothDoubleTransitions

namespace OAI

/-! The transverse ordered double locus carries its actual smooth
one-dimensional manifold structure, built from the proved submersion charts. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3}

def transverseDoubleChart
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (p : surfaceDoublePairs f) : SmoothDoubleChart f :=
  (exists_smooth_double_chart hf p (hreg _ _ p.property.1 p.property.2)).choose

lemma transverseDoubleChart_mem
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (p : surfaceDoublePairs f) : p ∈ (transverseDoubleChart hf hreg p).coord.source :=
  (exists_smooth_double_chart hf p (hreg _ _ p.property.1 p.property.2)).choose_spec

@[instance_reducible]
def doubleLocusChartedSpace
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y)) :
    ChartedSpace ℝ (surfaceDoublePairs f) where
  atlas := range fun p => (transverseDoubleChart hf hreg p).coord
  chartAt := fun p => (transverseDoubleChart hf hreg p).coord
  mem_chart_source := transverseDoubleChart_mem hf hreg
  chart_mem_atlas := fun p => ⟨p,rfl⟩

theorem doubleLocus_isManifold
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y)) :
    let :=  doubleLocusChartedSpace hf hreg
    IsManifold 𝓘(ℝ) ∞ (surfaceDoublePairs f) := by
  let :=  doubleLocusChartedSpace hf hreg
  apply isManifold_of_contDiffOn 𝓘(ℝ) ∞ (surfaceDoublePairs f)
  intro e e' he he'
  obtain ⟨p,rfl⟩ := he
  obtain ⟨q,rfl⟩ := he'
  have h := (transverseDoubleChart hf hreg q).transition_smooth (transverseDoubleChart hf hreg p)
  simpa [SmoothDoubleChart.transition,SmoothDoubleChart.overlap,OpenPartialHomeomorph.trans_source]
    using h

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
