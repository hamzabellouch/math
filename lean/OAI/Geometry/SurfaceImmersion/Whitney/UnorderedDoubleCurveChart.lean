import OAI.Geometry.SurfaceImmersion.Whitney.SurfaceDoublePairChart
import OAI.Geometry.SurfaceImmersion.Whitney.DoubleCurveMembership
import OAI.Geometry.SurfaceImmersion.Atlas.UnorderedPairChart

namespace OAI

/-! The regular unordered double curve has genuine open line charts in
its actual quotient-subspace topology. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem unordered_double_curve_chart {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (x y : M) (hxy : x ≠ y) (heq : f x = f y)
    (hreg : Function.Surjective (surfacePairDerivative f x y)) :
    ∃ c : OpenPartialHomeomorph (compactifiedDoubleCurve f) ℝ,
      (⟨unorderedPair (x,y),⟨(x,y),subset_closure ⟨hxy,heq⟩,rfl⟩⟩ : compactifiedDoubleCurve f) ∈ c.source := by
  obtain ⟨e,hpe,he,hne⟩ := unordered_pair_local_chart x y hxy
  obtain ⟨a,hpa,_,_,haf,_⟩ := matched_subset_chart e
    (surfaceDoublePairs f) (compactifiedDoubleCurve f) (x,y) hpe ⟨hxy,heq⟩
    (fun z hz => by rw [he z]; exact (compactifiedDoubleCurve_off_diagonal hf (hne z hz)).symm)
  obtain ⟨b,hpb⟩ := surface_double_pair_chart hf x y hxy heq hreg
  let p : surfaceDoublePairs f := ⟨(x,y),hxy,heq⟩
  let q : compactifiedDoubleCurve f := ⟨unorderedPair (x,y),⟨(x,y),subset_closure ⟨hxy,heq⟩,rfl⟩⟩
  have haq : a p = q := by
    apply Subtype.ext
    exact (haf p hpa).trans (he (x,y))
  refine ⟨a.symm.trans b,?_⟩
  change q ∈ a.target ∧ a.symm q ∈ b.source
  refine ⟨?_,?_⟩
  · rw [← haq]
    exact a.map_source hpa
  · rw [← haq,a.left_inv hpa]
    exact hpb

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
