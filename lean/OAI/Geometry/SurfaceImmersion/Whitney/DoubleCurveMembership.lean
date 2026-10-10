import OAI.Geometry.SurfaceImmersion.Whitney.CompactifiedDoubleCurve

namespace OAI

/-! Off the diagonal, membership in the compactified curve is exactly
membership in the actual double-pair locus. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem compactifiedDoubleCurve_pair_equality {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) {z : M × M}
    (hz : unorderedPair z ∈ compactifiedDoubleCurve f) : f z.1 = f z.2 := by
  obtain ⟨w,hw,he⟩ := hz
  have hwf := doublePairs_closure_equal hf.continuous hw
  change f w.1 = f w.2 at hwf
  rcases unorderedPair_eq.mp he with he | he
  · simpa only [he] using hwf
  · rw [he] at hwf
    exact hwf.symm

theorem compactifiedDoubleCurve_off_diagonal {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) {z : M × M}
    (hne : z.1 ≠ z.2) :
    unorderedPair z ∈ compactifiedDoubleCurve f ↔ z ∈ surfaceDoublePairs f := by
  constructor
  · intro hz
    exact ⟨hne,compactifiedDoubleCurve_pair_equality hf hz⟩
  · intro hz
    exact ⟨z,subset_closure hz,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
