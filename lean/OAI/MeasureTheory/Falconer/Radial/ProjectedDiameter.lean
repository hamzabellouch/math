import OAI.MeasureTheory.Falconer.Radial.ProjectionDensity

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem sourceProjection_dist_le (θ : ℝ) (x y : Plane) :
    dist (sourceProjection θ x) (sourceProjection θ y) ≤ dist x y := by
  rw [Real.dist_eq,← sourceProjection_sub,dist_eq_norm]
  by_cases h : x-y = 0
  · simp [h,sourceProjection]
  · rw [abs_sourceProjection θ h]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_sin_le_one _)

theorem projectedMeasure_diameter (β : Measure Plane) [IsFiniteMeasure β]
    {D : ℝ} (hD : ∀ᵐ z : Plane × Plane ∂β.prod β, dist z.1 z.2 ≤ D) (θ : ℝ) :
    ∀ᵐ z : ℝ × ℝ ∂(projectedMeasure β θ).prod (projectedMeasure β θ),
      dist z.1 z.2 ≤ D := by
  have hm : Measurable (sourceProjection θ) := by unfold sourceProjection; fun_prop
  rw [projectedMeasure,Measure.map_prod_map β β hm hm,
    ae_map_iff (hm.prodMap hm).aemeasurable (by measurability)]
  filter_upwards [hD] with z hz
  exact (sourceProjection_dist_le θ z.1 z.2).trans hz

theorem sourceRealProjection_support (a : Plane → ℝ) (hc : HasCompactSupport a)
    (θ : ℝ) : tsupport (projectedDensity (fun x => ENNReal.ofReal (a x)) θ) ⊆
      sourceProjection θ '' tsupport a := by
  have hP : Continuous (sourceProjection θ) := by unfold sourceProjection; fun_prop
  apply closure_minimal _ (hc.image hP).isClosed
  intro z hz
  by_contra hn
  apply hz
  have hzero (r : ℝ) : a (sourceFrame θ (z,r)) = 0 := by
    by_contra h
    exact hn ⟨sourceFrame θ (z,r),subset_tsupport a h,sourceProjection_frame θ z r⟩
  simp [projectedDensity,hzero]

end PlanarFalconer

end OAI
