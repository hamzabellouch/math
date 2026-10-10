import OAI.Geometry.CylinderCovering.Caps.TrapezoidGeometryDefinitions
import OAI.Geometry.CylinderCovering.Caps.FiniteShape
import OAI.Geometry.CylinderCovering.Caps.Geometry
import OAI.Geometry.CylinderCovering.Caps.FiniteTheorem

namespace OAI

open Set Filter
open scoped Topology
noncomputable section
namespace CylinderCovering.HalfheightFinite

theorem trapezoid_pair {δ : ℝ} (hδ : 0 < δ) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1 : ℝ) 1))
    (hR0 : ∀ r ∈ Icc (-1 : ℝ) 1, 0 ≤ R r) {N : ℕ} (i : Fin N) :
    NondegenerateTrapezoid (firstBase δ R N i) ∧
      NondegenerateTrapezoid (secondBase δ R N i) := by
  have hM := RadialRiemann.capMax_nonneg (by norm_num : (-1 : ℝ) < 1) hR hR0 i
  obtain ⟨hU, hL, hiU, hiL⟩ := Shape.projected_shape i hδ hM
  obtain ⟨hnU, hnL⟩ := Shape.projected_nondegenerate i hδ hM
  obtain ⟨ha, hb, vU, vL, hvU, hvL, hU0, hU1, hL0, hL1⟩ :=
    Shape.projected_parallel_sides i hδ hM
  constructor
  · exact ⟨Shape.firstVertices δ R N i, hU, hiU, hnU,
      2 * halfwidth N * collar δ N,
      2 * halfwidth N * (maxCap R N i + 3 * collar δ N),
      ha, hb, vU, hvU, hU0, hU1⟩
  · exact ⟨Shape.secondVertices δ R N i, hL, hiL, hnL,
      2 * halfwidth N * collar δ N,
      2 * halfwidth N * (maxCap R N i + 3 * collar δ N),
      ha, hb, vL, hvL, hL0, hL1⟩

theorem source_trapezoids (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (i : Fin N) :
    NondegenerateTrapezoid (firstBase δ (cubicCap δ) N i) ∧
    NondegenerateTrapezoid (secondBase δ (cubicCap δ) N i) ∧
    NondegenerateTrapezoid (firstBase δ (fractionalCap δ) N i) ∧
    NondegenerateTrapezoid (secondBase δ (fractionalCap δ) N i) := by
  obtain ⟨hcU, hcL⟩ := trapezoid_pair hδ (cubicCap_continuous δ).continuousOn
    (fun r _ => (cubicCap_positive hδ.le r).le) i
  obtain ⟨hfU, hfL⟩ := trapezoid_pair hδ (fractionalCap_continuous δ).continuousOn
    (fun r _ => (fractionalCap_positive hδ.le r).le) i
  exact ⟨hcU, hcL, hfU, hfL⟩

theorem eventual_half_minimum : ∀ᶠ δ : ℝ in 𝓝[>] 0,
    (∀ᶠ N in atTop, 0 < N ∧
      totalArea δ (cubicCap δ) N < Similarity.minimumArea tetrahedron / 2) ∧
    (∀ᶠ N in atTop, 0 < N ∧
      totalArea δ (fractionalCap δ) N < Similarity.minimumArea tetrahedron / 2) := by
  have hthreshold : Similarity.minimumArea tetrahedron / 2 = height / 4 := by
    rw [minimum_area]
    ring
  simpa only [hthreshold] using full_halfheight.2.2.2.2

theorem full_halfheight_geometry : GeometryStatement :=
  ⟨unit_edge_geometry, minimum_area, source_trapezoids, eventual_half_minimum⟩

end CylinderCovering.HalfheightFinite

end

end OAI
