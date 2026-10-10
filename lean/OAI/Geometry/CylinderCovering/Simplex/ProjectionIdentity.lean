import OAI.Geometry.CylinderCovering.Simplex.MetricNormalizationDefinitions
import OAI.Geometry.CylinderCovering.Simplex.Projection
import OAI.Geometry.CylinderCovering.Convexity.CylinderSimilarity
import OAI.Geometry.CylinderCovering.Convexity.RegularSimplexSimilarity
import OAI.Geometry.TriangularCovering.Main

namespace OAI

noncomputable section
open Set MeasureTheory

namespace CylinderCovering

theorem regular_minimum_shadow_area :
    ∀ v : Fin 4 → Space, AffineIndependent ℝ v →
      ∀ edge : ℝ, 0 < edge →
      (∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = edge) →
      minimumShadowArea (convexHull ℝ (range v)) = edge ^ 2 / (2 * Real.sqrt 2) := by
  intro v hv edge hedge hdist
  obtain ⟨L, t, hsim⟩ := RegularSimplexSimilarity.regular_simplex_similarity
    TriangularCovering.tetraVertices v TriangularCovering.tetra_affineIndependent hv
    (show (0 : ℝ) < 2 by norm_num) hedge
    (fun _ _ h => TriangularCovering.tetra_edge_length h) hdist
  rw [← TriangularCovering.K_eq_convexHull] at hsim
  rw [hsim]
  have hr : edge / 2 ≠ 0 := ne_of_gt (div_pos hedge (by norm_num : (0 : ℝ) < 2))
  change Similarity.minimumArea (Similarity.map t (edge / 2) L '' TriangularCovering.K) = _
  rw [Similarity.minimumArea_map _ _ hr L]
  change (edge / 2) ^ 2 * TriangularCovering.A_min = _
  rw [TriangularCovering.projection_minimum]
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  change (edge / 2) ^ 2 * Real.sqrt 2 = _
  field_simp [hs]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem regular_tetrahedron_volume (v : Fin 4 → Space)
    (hv : AffineIndependent ℝ v) {edge : ℝ} (hedge : 0 < edge)
    (hdist : ∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = edge) :
    volume.real (convexHull ℝ (range v)) = edge ^ 3 / (6 * Real.sqrt 2) := by
  have hmin := (simplex_chord_projection 3 (by omega) v hv).2.2
  change minimumShadowArea (convexHull ℝ (range v)) =
    3 * volume.real (convexHull ℝ (range v)) / Metric.diam (convexHull ℝ (range v)) at hmin
  rw [regular_minimum_shadow_area v hv edge hedge hdist,
    SimplexDiameter.regular_convexHull_diameter v hedge.le hdist] at hmin
  have hm := (eq_div_iff hedge.ne').mp hmin
  calc
    volume.real (convexHull ℝ (range v)) =
        (edge ^ 2 / (2 * Real.sqrt 2)) * edge / 3 := by linarith only [hm]
    _ = edge ^ 3 / (6 * Real.sqrt 2) := by ring

theorem regular_edge_shadow_minimum (v : Fin 4 → Space)
    (hv : AffineIndependent ℝ v) {edge : ℝ} (hedge : 0 < edge)
    (hdist : ∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = edge)
    (i j : Fin 4) (hij : i ≠ j) :
    shadowArea (convexHull ℝ (range v)) (‖v j - v i‖⁻¹ • (v j - v i)) =
      minimumShadowArea (convexHull ℝ (range v)) := by
  exact regular_edge_shadow_eq_minimum_of_simplexChordProjection
    simplex_chord_projection v hv hedge hdist hij

theorem regular_edge_shadow_area (v : Fin 4 → Space)
    (hv : AffineIndependent ℝ v) {edge : ℝ} (hedge : 0 < edge)
    (hdist : ∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = edge)
    (i j : Fin 4) (hij : i ≠ j) :
    shadowArea (convexHull ℝ (range v)) (‖v j - v i‖⁻¹ • (v j - v i)) =
      edge ^ 2 / (2 * Real.sqrt 2) :=
  (regular_edge_shadow_minimum v hv hedge hdist i j hij).trans
    (regular_minimum_shadow_area v hv edge hedge hdist)

theorem regularMetricNormalization_result : RegularMetricNormalizationStatement := by
  intro v hv edge hedge hdist
  refine ⟨SimplexDiameter.regular_convexHull_diameter v hedge.le hdist,
    regular_tetrahedron_volume v hv hedge hdist, ?_⟩
  rw [regular_minimum_shadow_area v hv edge hedge hdist]
  ring

theorem regularProjectionNormalization_result : RegularProjectionNormalizationStatement :=
  regularProjectionNormalization_of_minimum simplex_chord_projection regular_minimum_shadow_area

theorem simplexProjectionIdentity_result : SimplexProjectionIdentityStatement :=
  ⟨simplex_chord_projection, tetrahedron_edge_minimizer,
    regularProjectionNormalization_result⟩

end CylinderCovering

end

end OAI
