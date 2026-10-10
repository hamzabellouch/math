import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions
import OAI.Geometry.CylinderCovering.Angular.SharpArea
import OAI.Geometry.CylinderCovering.Convexity.TriangularSimilarity
import OAI.Geometry.CylinderCovering.Convexity.RegularSimplexSimilarity

namespace OAI

open Set MeasureTheory

noncomputable section
namespace CylinderCovering

theorem regular_minimum_shadow_formula (v : Fin 4 → Space)
    (hv : AffineIndependent ℝ v) {edge : ℝ} (hedge : 0 < edge)
    (hdist : ∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = edge) :
    minimumShadowArea (convexHull ℝ (range v)) = edge ^ 2 / (2 * Real.sqrt 2) := by
  obtain ⟨L, t, hsim⟩ := RegularSimplexSimilarity.regular_simplex_similarity
    TriangularCovering.tetraVertices v TriangularCovering.tetra_affineIndependent hv
    (show (0 : ℝ) < 2 by norm_num) hedge
    (fun _ _ h => TriangularCovering.tetra_edge_length h) hdist
  rw [← TriangularCovering.K_eq_convexHull] at hsim
  change Similarity.minimumArea (convexHull ℝ (range v)) = _
  rw [hsim, Similarity.minimumArea_map _ _
    (ne_of_gt (div_pos hedge (by norm_num : (0 : ℝ) < 2)))]
  change (edge / 2) ^ 2 * TriangularCovering.A_min = _
  rw [TriangularCovering.projection_minimum]
  change (edge / 2) ^ 2 * Real.sqrt 2 = _
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith [sq_nonneg edge]

theorem regularTriangularCounterexample_result : RegularTriangularCounterexampleStatement := by
  intro K hK
  rcases hK with ⟨v, hv, edge, hedge, hdist, rfl⟩
  obtain ⟨L, t, hsim⟩ := RegularSimplexSimilarity.regular_simplex_similarity
    TriangularCovering.tetraVertices v TriangularCovering.tetra_affineIndependent hv
    (show (0 : ℝ) < 2 by norm_num) hedge
    (fun _ _ h => TriangularCovering.tetra_edge_length h) hdist
  rw [← TriangularCovering.K_eq_convexHull] at hsim
  rw [hsim]
  have he : (0 : ℝ) < 1 / 2000 := by norm_num
  have hs : (1 / 2000 : ℝ) ≤ 1 / 2000 := le_rfl
  let C := TriangularCovering.finiteFamily (1 / 2000) he
  have hc : TriangularCovering.Covers C :=
    TriangularCovering.finiteFamily_covers he (by norm_num [TriangularCovering.η])
  obtain ⟨D, hcover, harea, hrelative⟩ := TriangularCovering.triangle_cover_similarity
    C hc (TriangularCovering.finiteFamily_strict_closed he hs)
    (TriangularCovering.finiteFamily_relative_lt_closed he hs)
    t (ne_of_gt (div_pos hedge (by norm_num : (0 : ℝ) < 2))) L
  exact ⟨_, D, hcover, harea, hrelative⟩

theorem regular_explicit_angular {K : Set Space} (hK : IsRegularTetrahedron K)
    {ε : ℝ} (he : 0 < ε) (hsmall : ε ≤ 1 / 2000) :
    ∃ C : Fin (2 * TriangularCovering.n ε) → TriangularCovering.TriCylinder,
      triangularCovers K C ∧
      |TriangularCovering.totalArea C / minimumShadowArea K -
        (1 / 2 - (13 / 6000 : ℝ) * ε ^ 2)| ≤ 2 * ε ^ 4 ∧
      TriangularCovering.totalArea C < minimumShadowArea K / 2 ∧
      triangularRelativeCost K C < 1 / 2 := by
  rcases hK with ⟨v, hv, edge, hedge, hdist, rfl⟩
  obtain ⟨L, t, hsim⟩ := RegularSimplexSimilarity.regular_simplex_similarity
    TriangularCovering.tetraVertices v TriangularCovering.tetra_affineIndependent hv
    (show (0 : ℝ) < 2 by norm_num) hedge
    (fun _ _ h => TriangularCovering.tetra_edge_length h) hdist
  rw [← TriangularCovering.K_eq_convexHull] at hsim
  rw [hsim]
  have hr : edge / 2 ≠ 0 := ne_of_gt (div_pos hedge (by norm_num : (0 : ℝ) < 2))
  let C := TriangularCovering.finiteFamily ε he
  let D := fun i => (C i).similarity t hr L
  have hc : TriangularCovering.Covers C :=
    TriangularCovering.finiteFamily_covers he (by norm_num [TriangularCovering.η]; exact hsmall)
  have hmin : minimumShadowArea (Similarity.map t (edge / 2) L '' TriangularCovering.K) =
      (edge / 2) ^ 2 * TriangularCovering.H := by
    change Similarity.minimumArea (Similarity.map t (edge / 2) L '' TriangularCovering.K) = _
    rw [Similarity.minimumArea_map _ _ hr L]
    change (edge / 2) ^ 2 * TriangularCovering.A_min = _
    rw [TriangularCovering.projection_minimum]
  refine ⟨D, TriangularCovering.similarity_covers C hc t hr L, ?_, ?_, ?_⟩
  · rw [show TriangularCovering.totalArea D =
        (edge / 2) ^ 2 * TriangularCovering.totalArea C from
        TriangularCovering.similarity_totalArea C t hr L, hmin,
      mul_div_mul_left _ _ (pow_ne_zero 2 hr)]
    exact TriangularCovering.finiteFamily_expansion_sharp he (by linarith only [hsmall])
  · rw [show TriangularCovering.totalArea D =
        (edge / 2) ^ 2 * TriangularCovering.totalArea C from
        TriangularCovering.similarity_totalArea C t hr L, hmin]
    have hh := TriangularCovering.finiteFamily_strict_closed he hsmall
    rw [TriangularCovering.projection_minimum] at hh
    exact (mul_lt_mul_of_pos_left hh (sq_pos_of_ne_zero hr)).trans_eq (by ring)
  · change (∑ i, TriangularCovering.area (D i).base /
      Similarity.shadowArea (Similarity.map t (edge / 2) L '' TriangularCovering.K)
        (D i).axis) < 1 / 2
    rw [TriangularCovering.similarity_relativeCost]
    exact TriangularCovering.finiteFamily_relative_lt_closed he hsmall

end CylinderCovering

end

end OAI
