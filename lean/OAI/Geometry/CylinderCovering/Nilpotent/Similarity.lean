import OAI.Geometry.CylinderCovering.Nilpotent.SimilarityDefinitions

namespace OAI

open Set MeasureTheory RuledApproximation
open scoped Pointwise

noncomputable section
namespace CylinderCovering.Nilpotent

private theorem sqrtTwo_ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
private theorem sqrtTwo_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem centerMap_normalized (x y z : ℝ) :
    centerMap (vec3 x y (Real.sqrt 2 * z)) =
      vec3 (x / 2) (y / 2) ((1 / 2 - z) / Real.sqrt 2) := by
  ext i
  fin_cases i <;> simp [centerMap, vec3]
  field_simp [sqrtTwo_ne]
  rw [sqrtTwo_sq]

theorem centerMap_uncenterMap (z : Space) : centerMap (uncenterMap z) = z := by
  ext i
  fin_cases i <;> simp [centerMap, uncenterMap, vec3]
  ring

theorem uncenterMap_centerMap (z : Space) : uncenterMap (centerMap z) = z := by
  ext i
  fin_cases i <;> simp [centerMap, uncenterMap, vec3] <;> ring

theorem centerMap_dist (x y : Space) : dist (centerMap x) (centerMap y) = dist x y / 2 := by
  rw [dist_eq_norm, dist_eq_norm]
  have hsq : ‖centerMap x - centerMap y‖ ^ 2 = ‖x - y‖ ^ 2 / 4 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, centerMap, vec3]
    ring
  nlinarith [norm_nonneg (centerMap x - centerMap y), norm_nonneg (x - y)]

theorem centerMap_mem_iff (z : Space) :
    centerMap z ∈ SlopeRational.referenceTetrahedron ↔ z ∈ tetrahedron := by
  constructor
  · rintro ⟨t, ht0, ht1, hx, hy, hz⟩
    refine ⟨1 / 2 - t, by linarith, by linarith, ?_, ?_, ?_⟩
    · change |z 0 / 2| ≤ (1 / 2 + t) / 2 at hx
      rw [abs_div] at hx
      norm_num at hx
      linarith
    · change |z 1 / 2| ≤ (1 / 2 - t) / 2 at hy
      rw [abs_div] at hy
      norm_num at hy
      linarith
    · change 1 / (2 * Real.sqrt 2) - z 2 / 2 = (1 / Real.sqrt 2) * t at hz
      field_simp [sqrtTwo_ne] at hz
      apply (mul_left_cancel₀ sqrtTwo_ne)
      have hid : Real.sqrt 2 * (Real.sqrt 2 * (1 / 2 - t)) = 1 - 2 * t := by
        rw [← mul_assoc, ← pow_two, sqrtTwo_sq]
        ring
      rw [hid]
      linarith
  · rintro ⟨t, ht0, ht1, hx, hy, hz⟩
    refine ⟨1 / 2 - t, by linarith, by linarith, ?_, ?_, ?_⟩
    · change |z 0 / 2| ≤ (1 / 2 + (1 / 2 - t)) / 2
      rw [abs_div]
      norm_num
      linarith
    · change |z 1 / 2| ≤ (1 / 2 - (1 / 2 - t)) / 2
      rw [abs_div]
      norm_num
      linarith
    · change 1 / (2 * Real.sqrt 2) - z 2 / 2 = (1 / Real.sqrt 2) * (1 / 2 - t)
      rw [hz]
      field_simp [sqrtTwo_ne]
      nlinarith [sqrtTwo_sq]

theorem centerMap_tetrahedron : centerMap '' tetrahedron = SlopeRational.referenceTetrahedron := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (centerMap_mem_iff x).2 hx
  · intro hz
    refine ⟨uncenterMap z, ?_, centerMap_uncenterMap z⟩
    exact (centerMap_mem_iff _).1 (by simpa only [centerMap_uncenterMap] using hz)

theorem centerMap_area (S : Set Space) :
    (Measure.euclideanHausdorffMeasure 2 (centerMap '' S)).toReal =
      (Measure.euclideanHausdorffMeasure 2 S).toReal / 4 := by
  have hiso : Isometry (fun z : Space => (2 : ℝ) • centerMap z) := by
    apply isometry_iff_dist_eq.mpr
    intro x y
    rw [dist_smul₀, centerMap_dist]
    norm_num
    ring
  have himage : centerMap '' S =
      (1 / 2 : ℝ) • ((fun z : Space => (2 : ℝ) • centerMap z) '' S) := by
    rw [← image_smul, image_image]
    congr 1
    funext z
    simp [smul_smul]
  rw [himage, Measure.euclideanHausdorffMeasure_smul₀ 2 (by norm_num : (1 / 2 : ℝ) ≠ 0),
    ENNReal.toReal_smul, hiso.euclideanHausdorffMeasure_image]
  norm_num
  change (1 / 4 : ℝ) * _ = _
  ring

theorem centerMap_volume (S : Set Space) :
    volume.real (centerMap '' S) = volume.real S / 8 := by
  have hiso : Isometry (fun z : Space => (2 : ℝ) • centerMap z) := by
    apply isometry_iff_dist_eq.mpr
    intro x y
    rw [dist_smul₀, centerMap_dist]
    norm_num
    ring
  have himage : centerMap '' S =
      (1 / 2 : ℝ) • ((fun z : Space => (2 : ℝ) • centerMap z) '' S) := by
    rw [← image_smul, image_image]
    congr 1
    funext z
    simp [smul_smul]
  have hm : (Measure.euclideanHausdorffMeasure 3 : Measure Space) = volume := by
    simpa using (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Space))
  change (volume (centerMap '' S)).toReal = (volume S).toReal / 8
  rw [← hm, himage,
    Measure.euclideanHausdorffMeasure_smul₀ 3 (by norm_num : (1 / 2 : ℝ) ≠ 0),
    ENNReal.toReal_smul, hiso.euclideanHausdorffMeasure_image]
  norm_num
  change (1 / 8 : ℝ) * _ = _
  ring

end CylinderCovering.Nilpotent

end

end OAI
