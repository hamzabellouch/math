import OAI.Geometry.CylinderCovering.Rational.EqualityCoverDefinitions
import OAI.Geometry.CylinderCovering.Rational.Normalization
import OAI.Geometry.CylinderCovering.Convexity.TriangularSimilarity

namespace OAI

noncomputable section
open Set
open scoped InnerProductSpace

namespace SlopeRational.EqualityCover
open TriangularCovering

private def tip : Space := RuledApproximation.vec3 0 0 (physicalScale / 2)
private def left : Space := RuledApproximation.vec3 0 (-1 / 4) 0
private def right : Space := RuledApproximation.vec3 0 (1 / 4) 0

lemma firstAxis_unit : ‖firstAxis‖ = 1 := by
  have hsq : ‖firstAxis‖ ^ 2 = 1 := by
    simp [EuclideanSpace.norm_sq_eq, firstAxis, RuledApproximation.vec3,
      Fin.sum_univ_succ]
  nlinarith [norm_nonneg firstAxis]

private lemma first_triple :
    inner ℝ firstAxis (cross3 (left - tip) (right - tip)) = physicalScale / 4 := by
  simp only [inner_coord, cross3_coord]
  dsimp [firstAxis, left, right, tip, RuledApproximation.vec3]
  ring

private lemma first_triple_ne :
    inner ℝ firstAxis (cross3 (left - tip) (right - tip)) ≠ 0 := by
  rw [first_triple]
  exact ne_of_gt (div_pos physicalScale_pos (by norm_num))

def firstCylinder : TriCylinder :=
  projectedCylinder firstAxis firstAxis_unit tip left right first_triple_ne

def secondCylinder : TriCylinder :=
  firstCylinder.similarity 0 (r := 1) (by norm_num) reflectionIsometry

private lemma triangle_mem_iff (z : Space) :
    z ∈ triangle tip left right ↔ z ∈ firstBase := by
  rw [mem_triangle_iff]
  constructor
  · rintro ⟨r, s, hr, hs, hrs, rfl⟩
    refine ⟨!₂[(s-r)/4, (1-r-s)/2], ?_, ?_⟩
    · change 0 ≤ (1-r-s)/2 ∧ (1-r-s)/2 ≤ 1/2 ∧
        2 * |(s-r)/4| ≤ 1/2 - (1-r-s)/2
      refine ⟨by linarith, by linarith, ?_⟩
      have habs : |(s-r)/4| ≤ (r+s)/4 := by
        rw [abs_le]
        constructor <;> linarith
      linarith
    · ext i
      fin_cases i <;> simp [tip, left, right, RuledApproximation.vec3] <;> ring
  · rintro ⟨p, ⟨hp0, hp1, hp2⟩, rfl⟩
    have habs : |p 0| ≤ (1/2 - p 1)/2 := by linarith
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    refine ⟨1/2-p 1-2*p 0, 1/2-p 1+2*p 0,
      by linarith, by linarith, by linarith, ?_⟩
    ext i
    fin_cases i <;> simp [tip, left, right, RuledApproximation.vec3] <;> ring

lemma firstBase_perpendicular {z : Space} (hz : z ∈ firstBase) :
    inner ℝ firstAxis z = 0 := by
  rcases hz with ⟨p, hp, rfl⟩
  simp [inner_coord, firstAxis, RuledApproximation.vec3]

lemma firstCylinder_axis : firstCylinder.axis = firstAxis := rfl

lemma firstCylinder_base : firstCylinder.base = firstBase := by
  change projection firstAxis '' triangle tip left right = firstBase
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' := (triangle_mem_iff w).mp hw
    simpa [projection, firstBase_perpendicular hw'] using hw'
  · intro hz
    refine ⟨z, (triangle_mem_iff z).mpr hz, ?_⟩
    simp [projection, firstBase_perpendicular hz]

lemma secondCylinder_axis : secondCylinder.axis = secondAxis := by
  change reflection firstAxis = secondAxis
  simp [reflection, firstAxis, secondAxis, RuledApproximation.vec3]

lemma secondCylinder_base : secondCylinder.base = secondBase := by
  change CylinderCovering.Similarity.transportedBase firstCylinder.base firstCylinder.axis
    0 1 reflectionIsometry = reflection '' firstBase
  rw [firstCylinder_base]
  unfold CylinderCovering.Similarity.transportedBase
  congr 1
  funext x
  simp [CylinderCovering.Similarity.baseMap, CylinderCovering.Similarity.project,
    reflectionIsometry]

lemma secondBase_eq_label_image : secondBase =
    (fun p : RuledApproximation.Plane =>
      RuledApproximation.vec3 (p 0) 0 (-physicalScale * p 1)) '' labelTriangle := by
  rw [secondBase, firstBase, Set.image_image]
  congr 1
  funext p
  ext i
  fin_cases i <;> simp [reflection, RuledApproximation.vec3]

lemma firstCylinder_area : area firstCylinder.base = physicalScale / 8 := by
  rw [firstCylinder, projectedCylinder_area, first_triple,
    abs_of_pos (div_pos physicalScale_pos (by norm_num))]
  ring

lemma secondCylinder_area : area secondCylinder.base = physicalScale / 8 := by
  rw [secondCylinder, TriCylinder.similarity_area, firstCylinder_area]
  norm_num

lemma firstCylinder_covers_nonnegative {z : Space}
    (hz : z ∈ referenceTetrahedron) (hlevel : 0 ≤ z 2) :
    z ∈ firstCylinder.carrier := by
  rcases hz with ⟨t, htlo, hthi, hx, hy, hz⟩
  have ht : 0 ≤ t := by nlinarith [physicalScale_pos]
  refine ⟨RuledApproximation.vec3 0 (z 1) (physicalScale*t), ?_, z 0, ?_⟩
  · rw [firstCylinder_base]
    refine ⟨!₂[z 1,t], ?_, rfl⟩
    exact ⟨ht, hthi, by change 2 * |z 1| ≤ 1/2-t; linarith⟩
  · ext i
    fin_cases i
    · simp [firstCylinder_axis, firstAxis, RuledApproximation.vec3]
    · simp [firstCylinder_axis, firstAxis, RuledApproximation.vec3]
    · simpa [firstCylinder_axis, firstAxis, RuledApproximation.vec3] using hz

lemma reflection_mem_reference {z : Space} (hz : z ∈ referenceTetrahedron) :
    reflection z ∈ referenceTetrahedron := by
  rcases hz with ⟨t, htlo, hthi, hx, hy, hz⟩
  refine ⟨-t, by linarith, by linarith, ?_, ?_, ?_⟩
  · change |z 1| ≤ (1/2 + -t)/2
    simpa [sub_eq_add_neg] using hy
  · change |z 0| ≤ (1/2 - -t)/2
    simpa using hx
  · change -z 2 = physicalScale * -t
    rw [hz]
    ring

lemma secondCylinder_covers_nonpositive {z : Space}
    (hz : z ∈ referenceTetrahedron) (hlevel : z 2 ≤ 0) :
    z ∈ secondCylinder.carrier := by
  have hm := firstCylinder_covers_nonnegative (reflection_mem_reference hz)
    (show 0 ≤ (reflection z) 2 by change 0 ≤ -z 2; linarith)
  rw [secondCylinder, TriCylinder.similarity_carrier]
  refine ⟨reflection z, hm, ?_⟩
  change (0 : Space) + (1 : ℝ) • reflection (reflection z) = z
  ext i
  fin_cases i <;> simp [reflection, RuledApproximation.vec3]

def cylinders : Fin 2 → TriCylinder := ![firstCylinder, secondCylinder]

lemma cylinders_covers : CylinderCovering.triangularCovers referenceTetrahedron cylinders := by
  intro z hz
  rcases le_total 0 (z 2) with h | h
  · exact ⟨0, firstCylinder_covers_nonnegative hz h⟩
  · exact ⟨1, secondCylinder_covers_nonpositive hz h⟩

lemma cylinders_area_each (i : Fin 2) : area (cylinders i).base = physicalScale / 8 := by
  fin_cases i
  · exact firstCylinder_area
  · exact secondCylinder_area

lemma cylinders_totalArea : totalArea cylinders = physicalScale / 4 := by
  simp only [totalArea, cylinders_area_each, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

lemma secondAxis_unit : ‖secondAxis‖ = 1 := by
  rw [← secondCylinder_axis]
  exact secondCylinder.unit_axis

private lemma centered_shadow (u : Space) :
    CylinderCovering.shadowArea referenceTetrahedron (centeringIsometry u) =
      (1 / 2 : ℝ)^2 * TriangularCovering.shadowArea u := by
  rw [referenceTetrahedron_eq_similarity]
  exact CylinderCovering.Similarity.shadowArea_map K centeringTranslation
    (by norm_num : (1 / 2 : ℝ) ≠ 0) centeringIsometry u

lemma firstAxis_shadow :
    CylinderCovering.shadowArea referenceTetrahedron firstAxis = physicalScale / 2 := by
  change CylinderCovering.shadowArea referenceTetrahedron (centeringIsometry secondAxis) = _
  rw [centered_shadow, TriangularCovering.shadowArea_formula secondAxis_unit]
  change (1 / 2 : ℝ)^2 * (max (H * |0|) |0| + max (H * |1|) |0|) = _
  norm_num [H_pos.le]
  rw [← twice_physicalScale]
  ring

lemma secondAxis_shadow :
    CylinderCovering.shadowArea referenceTetrahedron secondAxis = physicalScale / 2 := by
  change CylinderCovering.shadowArea referenceTetrahedron (centeringIsometry firstAxis) = _
  rw [centered_shadow, TriangularCovering.shadowArea_formula firstAxis_unit]
  change (1 / 2 : ℝ)^2 * (max (H * |1|) |0| + max (H * |0|) |0|) = _
  norm_num [H_pos.le]
  rw [← twice_physicalScale]
  ring

lemma cylinders_shadow_each (i : Fin 2) :
    CylinderCovering.shadowArea referenceTetrahedron (cylinders i).axis =
      physicalScale / 2 := by
  fin_cases i
  · exact firstAxis_shadow
  · change CylinderCovering.shadowArea referenceTetrahedron secondCylinder.axis = _
    rw [secondCylinder_axis]
    exact secondAxis_shadow

lemma cylinders_relativeCost :
    CylinderCovering.triangularRelativeCost referenceTetrahedron cylinders = 1 / 2 := by
  simp only [CylinderCovering.triangularRelativeCost, cylinders_area_each,
    cylinders_shadow_each, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp [physicalScale_pos.ne']
  ring

theorem equality_cover : Statement := by
  refine ⟨cylinders, firstCylinder_axis, secondCylinder_axis,
    firstCylinder_base, secondCylinder_base, cylinders_covers,
    cylinders_area_each, cylinders_totalArea, ?_, cylinders_shadow_each,
    cylinders_relativeCost⟩
  rw [cylinders_totalArea, referenceTetrahedron_minimumShadowArea]
  ring

end SlopeRational.EqualityCover

end

end OAI
