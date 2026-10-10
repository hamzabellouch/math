import OAI.Geometry.CylinderCovering.Simplex.ProjectionDefinitions
import OAI.Geometry.CylinderCovering.Simplex.Diameter

namespace OAI

open Set Metric MeasureTheory

namespace CylinderCovering

lemma longestChord_eq_maxChord {d : ℕ} (S : Set (Euclidean d)) (u : Euclidean d) :
    longestChord S u = SimplexDiameter.maxChord S u := rfl

lemma simplexMinimumShadowArea_of_product {d : ℕ} (hd : 2 ≤ d)
    (v : Fin (d + 1) → Euclidean d) (hv : AffineIndependent ℝ v)
    (hprod : ∀ u, ‖u‖ = 1 → simplexShadowArea v u * longestChord (simplexCarrier v) u =
      (d : ℝ) * volume.real (simplexCarrier v)) :
    simplexMinimumShadowArea v =
      (d : ℝ) * volume.real (simplexCarrier v) / diam (simplexCarrier v) := by
  have : Nontrivial (Fin (d + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hleast := SimplexDiameter.projection_minimum_of_chord_identity
    ((finite_range v).isCompact_convexHull ℝ)
    ((range_nonempty v).mono (subset_convexHull ℝ _))
    (SimplexDiameter.affineIndependent_diameter_pos hv)
    (simplexShadowArea v) ((d : ℝ) * volume.real (simplexCarrier v))
    (fun _ _ => ENNReal.toReal_nonneg) hprod
  unfold simplexMinimumShadowArea
  convert hleast.csInf_eq using 1 <;> congr 1
  ext a
  simp only [eq_comm]

lemma tetrahedronEdgeMinimizer_of_simplexChordProjection
    (h : SimplexChordProjectionStatement) : TetrahedronEdgeMinimizerStatement := by
  intro v hv
  obtain ⟨hdir, _, hmin⟩ := h 3 (by omega) v hv
  have hprod := fun u hu => (hdir u hu).2.2
  obtain ⟨i, j, hij, hu, hval, _⟩ := SimplexDiameter.finite_edge_projection_minimizer v
    (SimplexDiameter.affineIndependent_diameter_pos hv)
    (simplexShadowArea v) ((3 : ℝ) * volume.real (simplexCarrier v))
    (fun _ _ => ENNReal.toReal_nonneg) hprod
  refine ⟨i, j, hij, ?_⟩
  change simplexShadowArea v (NormedSpace.normalize (v j - v i)) =
    simplexMinimumShadowArea v
  exact hval.trans hmin.symm

lemma simplexCarrier_isCompact {d : ℕ} (v : Fin (d + 1) → Euclidean d) :
    IsCompact (simplexCarrier v) := (finite_range v).isCompact_convexHull ℝ

lemma simplexCarrier_interior_nonempty {d : ℕ}
    (v : Fin (d + 1) → Euclidean d) (hv : AffineIndependent ℝ v) :
    (interior (simplexCarrier v)).Nonempty := by
  apply (convex_convexHull ℝ (range v)).interior_nonempty_iff_affineSpan_eq_top.mpr
  rw [affineSpan_convexHull]
  apply hv.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  simp

lemma simplexCarrier_volume_pos {d : ℕ}
    (v : Fin (d + 1) → Euclidean d) (hv : AffineIndependent ℝ v) :
    0 < volume.real (simplexCarrier v) := by
  apply ENNReal.toReal_pos
  · exact (Measure.measure_pos_of_nonempty_interior volume
      (simplexCarrier_interior_nonempty v hv)).ne'
  · exact (simplexCarrier_isCompact v).measure_ne_top

lemma simplex_longestChord_pos {d : ℕ}
    (v : Fin (d + 1) → Euclidean d) (hv : AffineIndependent ℝ v)
    {u : Euclidean d} (hu : ‖u‖ = 1) :
    0 < longestChord (simplexCarrier v) u :=
  SimplexDiameter.maxChord_pos_of_interior (simplexCarrier_isCompact v)
    (simplexCarrier_interior_nonempty v hv) hu

lemma simplexMinimumShadowArea_attained_of_product {d : ℕ} (hd : 2 ≤ d)
    (v : Fin (d + 1) → Euclidean d) (hv : AffineIndependent ℝ v)
    (hprod : ∀ u, ‖u‖ = 1 → simplexShadowArea v u * longestChord (simplexCarrier v) u =
      (d : ℝ) * volume.real (simplexCarrier v)) :
    ∃ u, ‖u‖ = 1 ∧ simplexShadowArea v u = simplexMinimumShadowArea v := by
  have : Nontrivial (Fin (d + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨u, hu, hmax⟩ := SimplexDiameter.exists_maxChord_eq_diam
    (simplexCarrier_isCompact v) ((range_nonempty v).mono (subset_convexHull ℝ _))
    (SimplexDiameter.affineIndependent_diameter_pos hv)
  simp only [simplexCarrier] at hmax
  refine ⟨u, hu, ?_⟩
  rw [simplexMinimumShadowArea_of_product hd v hv hprod]
  apply (eq_div_iff (SimplexDiameter.affineIndependent_diameter_pos hv).ne').mpr
  simpa only [longestChord_eq_maxChord, simplexCarrier, hmax] using hprod u hu

lemma simplexChordProjection_of_products
    (hprod : ∀ d : ℕ, 2 ≤ d → ∀ v : Fin (d + 1) → Euclidean d,
      AffineIndependent ℝ v → ∀ u, ‖u‖ = 1 →
      simplexShadowArea v u * longestChord (simplexCarrier v) u =
        (d : ℝ) * volume.real (simplexCarrier v)) :
    SimplexChordProjectionStatement := by
  intro d hd v hv
  refine ⟨?_, simplexMinimumShadowArea_attained_of_product hd v hv (hprod d hd v hv),
    simplexMinimumShadowArea_of_product hd v hv (hprod d hd v hv)⟩
  intro u hu
  exact ⟨simplex_longestChord_pos v hv hu,
    (SimplexDiameter.maxChord_attained (simplexCarrier_isCompact v)
      ((range_nonempty v).mono (subset_convexHull ℝ _)) hu).2,
    hprod d hd v hv u hu⟩

lemma regular_edge_shadow_eq_minimum_of_simplexChordProjection
    (h : SimplexChordProjectionStatement)
    (v : Fin 4 → Space) (hv : AffineIndependent ℝ v)
    {edge : ℝ} (he : 0 < edge)
    (hvEdge : ∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = edge)
    {i j : Fin 4} (hij : i ≠ j) :
    shadowArea (convexHull ℝ (range v)) (‖v j - v i‖⁻¹ • (v j - v i)) =
      minimumShadowArea (convexHull ℝ (range v)) := by
  obtain ⟨hu, hchord⟩ := SimplexDiameter.regular_edge_maxChord v he hvEdge hij
  obtain ⟨hdir, _, hmin⟩ := h 3 (by omega) v hv
  change simplexShadowArea v (NormedSpace.normalize (v j - v i)) =
    simplexMinimumShadowArea v
  have hprod := (hdir _ hu).2.2
  have hd : diam (simplexCarrier v) = edge :=
    SimplexDiameter.regular_convexHull_diameter v he.le hvEdge
  rw [hmin, hd]
  apply (eq_div_iff he.ne').mpr
  simpa only [longestChord_eq_maxChord, simplexCarrier, hchord] using hprod

lemma regularProjectionNormalization_of_minimum
    (h : SimplexChordProjectionStatement)
    (hmin : ∀ v : Fin 4 → Space, AffineIndependent ℝ v →
      ∀ edge : ℝ, 0 < edge →
      (∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = edge) →
      minimumShadowArea (convexHull ℝ (range v)) = edge ^ 2 / (2 * Real.sqrt 2)) :
    RegularProjectionNormalizationStatement := by
  intro v hv edge he hvEdge
  refine ⟨hmin v hv edge he hvEdge, ?_⟩
  intro i j hij
  exact (regular_edge_shadow_eq_minimum_of_simplexChordProjection h v hv he hvEdge hij).trans
    (hmin v hv edge he hvEdge)

end CylinderCovering

end OAI
