import OAI.Geometry.CylinderCovering.Angular.GeneralGeometry
import OAI.Geometry.CylinderCovering.Angular.GeneralCoverage
import OAI.Geometry.CylinderCovering.Convexity.CylinderSimilarity
import OAI.Geometry.CylinderCovering.Beams.ProjectionFactorDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace

namespace ShortenedBeam.ProjectionFactor

open RuledApproximation
open CylinderCovering

lemma cycle_direction (β : ℝ) (v : Plane) :
    cycleCoordinates (physicalDirection 1 (β • v)) = direction β v := by
  ext i
  fin_cases i <;> simp [cycleCoordinates, physicalDirection, direction, vec3]

lemma cycle_axis (β : ℝ) (v : Plane) :
    cycleCoordinates (physicalUnit 1 (β • v)) = axis β v := by
  rw [axis, ← cycle_direction, cycleCoordinates.norm_map, physicalUnit, map_smul]

lemma axis_unit (β : ℝ) (v : Plane) : ‖axis β v‖ = 1 := by
  rw [← cycle_axis, cycleCoordinates.norm_map, physicalUnit_norm]

lemma direction_ne_zero (β : ℝ) (v : Plane) : direction β v ≠ 0 := by
  rw [← cycle_direction]
  simpa using cycleCoordinates.injective.ne (physicalDirection_ne_zero 1 (β • v))

lemma horizontal_eq_map (β : ℝ) (p : Plane) :
    horizontal β p = Similarity.map 0 β cycleCoordinates (planeEmbedding 1 p) := by
  ext i
  fin_cases i <;> simp [horizontal, Similarity.map, cycleCoordinates, planeEmbedding, vec3]

lemma base_eq_map (β : ℝ) (v : Plane) (S : Set Plane) :
    base β v S = Similarity.map 0 β cycleCoordinates '' (rawProjection 1 (β • v) '' S) := by
  simp only [base, image_image]
  apply image_congr
  intro p hp
  rw [horizontal_eq_map, ← cycle_axis]
  change Similarity.project (cycleCoordinates (physicalUnit 1 (β • v)))
      (Similarity.map 0 β cycleCoordinates (planeEmbedding 1 p)) = _
  rw [Similarity.project_map]
  have hpj := AngularGeneral.projection_physicalUnit 1 (β • v) p
  change Similarity.project (physicalUnit 1 (β • v)) (planeEmbedding 1 p) =
    rawProjection 1 (β • v) p at hpj
  rw [hpj]
  simp [Similarity.project, Similarity.map]

lemma physicalDirection_norm (β : ℝ) (v : Plane) :
    ‖physicalDirection 1 (β • v)‖ = Real.sqrt (1 + β ^ 2 * ‖v‖ ^ 2) := by
  have hs : ‖physicalDirection 1 (β • v)‖ ^ 2 = 1 + β ^ 2 * ‖v‖ ^ 2 := by
    rw [physicalDirection_norm_sq, norm_plane_sq]
    simp only [PiLp.smul_apply, smul_eq_mul, one_pow, one_mul]
    ring
  rw [← hs, Real.sqrt_sq_eq_abs, abs_norm]

lemma raw_projection_area (β : ℝ) (v : Plane) (S : Set Plane) :
    TriangularCovering.area (rawProjection 1 (β • v) '' S) =
      volume.real S / Real.sqrt (1 + β ^ 2 * ‖v‖ ^ 2) := by
  have hm := (rawProjection 1 (β • v)).euclideanHausdorffMeasure_image_eq_normDet_mul_volume S
  simp only [finrank_euclideanSpace_fin] at hm
  unfold TriangularCovering.area
  rw [hm, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (rawProjection 1 (β • v)).normDet_nonneg,
    rawProjection_normDet (by norm_num : (0 : ℝ) < 1), physicalDirection_norm]
  change (1 / Real.sqrt (1 + β ^ 2 * ‖v‖ ^ 2)) * volume.real S = _
  ring

theorem area {β : ℝ} (hβ : β ≠ 0) (v : Plane) (S : Set Plane) :
    TriangularCovering.area (base β v S) =
      β ^ 2 * volume.real S / Real.sqrt (1 + β ^ 2 * ‖v‖ ^ 2) := by
  rw [base_eq_map]
  have h := Similarity.area_map (0 : Space) hβ cycleCoordinates
    (rawProjection 1 (β • v) '' S)
  change TriangularCovering.area _ = β ^ 2 * TriangularCovering.area _ at h
  rw [h, raw_projection_area]
  ring

theorem base_compact (β : ℝ) (v : Plane) {S : Set Plane} (hS : IsCompact S) :
    IsCompact (base β v S) := by
  rw [base_eq_map, image_image]
  apply hS.image
  exact (Similarity.map_continuous 0 β cycleCoordinates).comp
    (rawProjection 1 (β • v)).continuous_of_finiteDimensional

theorem base_perpendicular (β : ℝ) (v : Plane) (S : Set Plane) :
    ∀ z ∈ base β v S, inner ℝ (axis β v) z = 0 :=
  AngularGeneral.projected_base_perpendicular (axis_unit β v) _

theorem base_finite {β : ℝ} (hβ : β ≠ 0) (v : Plane) {S : Set Plane}
    (hS : IsCompact S) : Measure.euclideanHausdorffMeasure 2 (base β v S) ≠ ⊤ := by
  rw [base_eq_map, Similarity.euclideanHausdorffMeasure_map 0 hβ]
  have hm := (rawProjection 1 (β • v)).euclideanHausdorffMeasure_image_eq_normDet_mul_volume S
  simp only [finrank_euclideanSpace_fin] at hm
  rw [hm]
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS.measure_lt_top.ne)

lemma horizontal_physical (p : Plane) :
    horizontal (1 / Real.sqrt 2) p = ShortenedBeam.point (p 0) (p 1) 0 := by
  ext i
  fin_cases i <;> simp [horizontal, ShortenedBeam.point, vec3] <;> ring

theorem carrier_eq (β : ℝ) (v : Plane) (S : Set Plane) :
    AngularGeneral.carrier (axis β v) (base β v S) =
      {z | ∃ p ∈ S, ∃ t : ℝ, z = horizontal β p + t • direction β v} := by
  change AngularGeneral.carrier (AngularGeneral.unitDirection (direction β v))
    (TriangularCovering.projection (AngularGeneral.unitDirection (direction β v)) ''
      (horizontal β '' S)) = _
  rw [AngularGeneral.carrier_projected_eq (direction_ne_zero β v)]
  ext z
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, t, hz⟩
    exact ⟨p, hp, t, hz⟩
  · rintro ⟨p, hp, t, hz⟩
    exact ⟨horizontal β p, ⟨p, hp, rfl⟩, t, hz⟩

theorem normalized_area (v : Plane) (S : Set Plane) :
    TriangularCovering.area (base (1 / Real.sqrt 2) v S) /
        ((1 / Real.sqrt 2) ^ 2 / Real.sqrt 2) =
      volume.real S * Real.sqrt 2 / Real.sqrt (1 + ‖v‖ ^ 2 / 2) := by
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hβ : (1 / Real.sqrt 2 : ℝ) ≠ 0 := one_div_ne_zero hs
  have hβsq : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [area hβ, hβsq]
  rw [show 1 + (1 / 2 : ℝ) * ‖v‖ ^ 2 = 1 + ‖v‖ ^ 2 / 2 by ring]
  field_simp

theorem statement : Statement := by
  intro v S hS
  refine ⟨axis_unit _ _, base_compact _ _ hS, ?_, base_perpendicular _ _ _,
    carrier_eq _ _ _, normalized_area _ _⟩
  exact base_finite (by positivity) v hS

end ShortenedBeam.ProjectionFactor

end

end OAI
