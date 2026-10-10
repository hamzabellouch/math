import OAI.MeasureTheory.Falconer.Radial.RadialZoom

namespace OAI

/-! # Original radial laws and source balls under positive affine rescaling -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem originalRadialSphereLaw_zoom (w₀ : Sphere d) (ν : Measure (Space d))
    {a : ℝ} (ha : 0 < a) (c z : Space d)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G) :
    originalRadialSphereLaw w₀ (Measure.map (radialZoom a ha.ne' c) ν)
      (zoomPairSet (radialZoom a ha.ne' c) G) (radialZoom a ha.ne' c z) =
      originalRadialSphereLaw w₀ ν G z := by
  let e := radialZoom a ha.ne' c
  apply Measure.ext
  intro B hB
  rw [originalRadialSphereLaw_apply w₀ _ _ _ B hB,
    originalRadialSphereLaw_apply w₀ ν G z B hB]
  have hsection : MeasurableSet {x : Space d | (e z,x) ∈ zoomPairSet e G ∧
      normalizeToSphere w₀ (x-e z) ∈ B} :=
    ((zoomPairSet_measurable e hG).preimage (measurable_const.prodMk measurable_id)).inter
      (hB.preimage ((normalizeToSphere_measurable w₀).comp (measurable_id.sub measurable_const)))
  rw [Measure.map_apply e.measurable hsection]
  congr 1
  ext x
  dsimp only [e]
  simp only [mem_preimage,mem_ofPred_eq,mem_zoomPairSet,radialZoom_direction w₀ ha]

theorem radialZoom_preimage_ball {a : ℝ} (ha : 0 < a) (c x : Space d) (r : ℝ) :
    radialZoom a ha.ne' c ⁻¹' Metric.ball x r = Metric.ball (c+a⁻¹ • x) (r/a) := by
  ext z
  have he : a • (z-c)-x = a • (z-(c+a⁻¹ • x)) := by
    simp only [smul_sub,smul_add,smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
    abel
  simp only [mem_preimage,Metric.mem_ball,dist_eq_norm,radialZoom_apply]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos ha,lt_div_iff₀ ha]
  rw [mul_comm a]

theorem radialZoom_ball_apply (μ : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c x : Space d) (r : ℝ) :
    Measure.map (radialZoom a ha.ne' c) μ (Metric.ball x r) =
      μ (Metric.ball (c+a⁻¹ • x) (r/a)) := by
  rw [Measure.map_apply (radialZoom a ha.ne' c).measurable Metric.isOpen_ball.measurableSet,
    radialZoom_preimage_ball ha]

end Falconer

end OAI
