import OAI.Geometry.CylinderCovering.Convexity.FinitePlaneHausdorff
import OAI.Geometry.CylinderCovering.Convexity.RelativeCostComparison
import OAI.Geometry.CylinderCovering.Convexity.CylinderSimilarity
import OAI.Geometry.TriangularCovering.Main

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace

namespace CylinderCovering.ConvexBodyShadowBounds

theorem compact_shadow_measure_ne_top {K : Set Space} (hK : IsCompact K)
    {u : Space} (hu : ‖u‖ = 1) :
    Measure.euclideanHausdorffMeasure 2 (TriangularCovering.projection u '' K) ≠ ⊤ := by
  have hc : Continuous (TriangularCovering.projection u) := by
    unfold TriangularCovering.projection
    fun_prop
  have hp : ∀ x ∈ TriangularCovering.projection u '' K, inner ℝ u x = 0 := by
    rintro x ⟨y, hy, rfl⟩
    exact Similarity.project_perpendicular hu y
  simpa using (FinitePlaneHausdorff.compact_perpendicular_measure_lt_top
    hu (hK.image hc) hp).ne

theorem shadowArea_mono {A B : Set Space} (hAB : A ⊆ B) (hB : IsCompact B)
    {u : Space} (hu : ‖u‖ = 1) : shadowArea A u ≤ shadowArea B u := by
  exact ENNReal.toReal_mono (compact_shadow_measure_ne_top hB hu)
    (measure_mono (Set.image_mono hAB))

theorem minimumShadowArea_mono {A B : Set Space} (hAB : A ⊆ B)
    (hB : IsCompact B) : minimumShadowArea A ≤ minimumShadowArea B := by
  obtain ⟨u, hu⟩ := exists_norm_eq Space (show (0 : ℝ) ≤ 1 by norm_num)
  apply le_csInf (show {a : ℝ | ∃ v : Space, ‖v‖ = 1 ∧ a = shadowArea B v}.Nonempty
    from ⟨shadowArea B u, u, hu, rfl⟩)
  rintro a ⟨v, hv, rfl⟩
  exact (CostComparison.minimumShadowArea_le_shadowArea A v hv).trans
    (shadowArea_mono hAB hB hv)

theorem exists_inscribed_tetrahedron {K : Set Space} (hK : (interior K).Nonempty) :
    ∃ t : Space, ∃ r : ℝ, 0 < r ∧
      Similarity.map t r (LinearIsometryEquiv.refl ℝ Space) '' TriangularCovering.K ⊆ K := by
  obtain ⟨t, ht⟩ := hK
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ht)
  obtain ⟨R, hR, hbound⟩ := TriangularCovering.K_compact.isBounded.exists_pos_norm_lt
  refine ⟨t, ε / R, div_pos hε hR, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  apply hball
  rw [Metric.mem_ball]
  change dist (t + (ε / R) • y) t < ε
  rw [dist_eq_norm]
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hε hR)]
  calc
    ε / R * ‖y‖ < ε / R * R := mul_lt_mul_of_pos_left (hbound y hy) (div_pos hε hR)
    _ = ε := div_mul_cancel₀ ε hR.ne'

theorem minimumShadowArea_pos {K : Set Space} (hK : IsCompact K)
    (hinterior : (interior K).Nonempty) : 0 < minimumShadowArea K := by
  obtain ⟨t, r, hr, hsub⟩ := exists_inscribed_tetrahedron hinterior
  have hpos : 0 < minimumShadowArea
      (Similarity.map t r (LinearIsometryEquiv.refl ℝ Space) '' TriangularCovering.K) := by
    change 0 < Similarity.minimumArea
      (Similarity.map t r (LinearIsometryEquiv.refl ℝ Space) '' TriangularCovering.K)
    rw [Similarity.minimumArea_map TriangularCovering.K t hr.ne']
    change 0 < r ^ 2 * TriangularCovering.A_min
    rw [TriangularCovering.projection_minimum]
    exact mul_pos (sq_pos_of_pos hr) (Real.sqrt_pos.2 (by norm_num))
  exact hpos.trans_le (minimumShadowArea_mono hsub hK)

theorem exists_uniform_positive_shadow_bound {K : Set Space} (hK : IsCompact K)
    (hinterior : (interior K).Nonempty) :
    ∃ a : ℝ, 0 < a ∧ ∀ u : Space, ‖u‖ = 1 → a ≤ shadowArea K u :=
  ⟨minimumShadowArea K, minimumShadowArea_pos hK hinterior,
    CostComparison.minimumShadowArea_le_shadowArea K⟩

theorem shadow_measure_pos_and_lt_top {K : Set Space} (hK : IsCompact K)
    (hinterior : (interior K).Nonempty) {u : Space} (hu : ‖u‖ = 1) :
    0 < Measure.euclideanHausdorffMeasure 2 (TriangularCovering.projection u '' K) ∧
      Measure.euclideanHausdorffMeasure 2 (TriangularCovering.projection u '' K) < ⊤ := by
  apply ENNReal.toReal_pos_iff.mp
  exact (minimumShadowArea_pos hK hinterior).trans_le
    (CostComparison.minimumShadowArea_le_shadowArea K u hu)

theorem relativeCost_le_familyArea_div_minimum {K : Set Space} (hK : IsCompact K)
    (hinterior : (interior K).Nonempty) {n : ℕ} (C : Fin n → RuledApproximation.Cylinder) :
    relativeCost K C ≤ RuledApproximation.familyArea C / minimumShadowArea K :=
  CostComparison.relativeCost_le_familyArea_div_minimum K C (minimumShadowArea_pos hK hinterior)

theorem relativeCost_lt_half_of_familyArea_lt_half {K : Set Space} (hK : IsCompact K)
    (hinterior : (interior K).Nonempty) {n : ℕ} (C : Fin n → RuledApproximation.Cylinder)
    (hC : RuledApproximation.familyArea C < minimumShadowArea K / 2) :
    relativeCost K C < 1 / 2 :=
  CostComparison.relativeCost_lt_half_of_familyArea_lt_half K C
    (minimumShadowArea_pos hK hinterior) hC

theorem triangularRelativeCost_le_totalArea_div_minimum {K : Set Space} (hK : IsCompact K)
    (hinterior : (interior K).Nonempty) {n : ℕ} (C : Fin n → TriangularCovering.TriCylinder) :
    triangularRelativeCost K C ≤ TriangularCovering.totalArea C / minimumShadowArea K :=
  CostComparison.triangularRelativeCost_le_totalArea_div_minimum K C
    (minimumShadowArea_pos hK hinterior)

theorem triangularRelativeCost_lt_half_of_totalArea_lt_half {K : Set Space}
    (hK : IsCompact K) (hinterior : (interior K).Nonempty) {n : ℕ}
    (C : Fin n → TriangularCovering.TriCylinder)
    (hC : TriangularCovering.totalArea C < minimumShadowArea K / 2) :
    triangularRelativeCost K C < 1 / 2 :=
  CostComparison.triangularRelativeCost_lt_half_of_totalArea_lt_half K C
    (minimumShadowArea_pos hK hinterior) hC

end CylinderCovering.ConvexBodyShadowBounds

end

end OAI
