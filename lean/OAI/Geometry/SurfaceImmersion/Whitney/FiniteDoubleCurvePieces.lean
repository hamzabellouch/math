import OAI.Geometry.SurfaceImmersion.Geometry.CompactCurvePieces
import OAI.Geometry.SurfaceImmersion.Atlas.TransverseCompactCurveCharts

namespace OAI

/-! The actual compactified surface double curve has a finite vertex/
open-edge decomposition; no graph decomposition is assumed. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem exists_finite_double_curve_pieces :
    ∃ f : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f ∧
      ∃ (V : Set (compactifiedDoubleCurve f)) (P : Finset (Set (compactifiedDoubleCurve f))),
        V.Finite ∧ doubleCurveBoundary f ⊆ V ∧
        (∀ E ∈ P, IsOpen E ∧ IsConnected E ∧ Disjoint E V ∧ closure E \ E ⊆ V) ∧
        (∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F) ∧ Vᶜ = ⋃ E ∈ P, E ∧ (∀ E ∈ P, Nonempty (CurveEdgeWitness V E)) := by
  obtain ⟨f,hf,hK,hD,hline,hhalf⟩ := exists_compact_double_curve_charts (M := M)
  have : CompactSpace (compactifiedDoubleCurve f) := isCompact_iff_compactSpace.mp hK
  obtain ⟨V,P,hV,hDV,hP,hd,hc,hE⟩ := compact_curve_pieces (doubleCurveBoundary f) hD
    (fun x => by
      by_cases hx : x ∈ doubleCurveBoundary f
      · exact Or.inr (hhalf x hx)
      · exact Or.inl (hline x hx))
  exact ⟨f,hf,V,P,hV,hDV,hP,hd,hc,hE⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
