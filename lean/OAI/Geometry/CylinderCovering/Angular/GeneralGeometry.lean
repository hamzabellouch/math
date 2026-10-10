import OAI.Geometry.CylinderCovering.Angular.GeneralGeometryDefinitions
import OAI.Geometry.CylinderCovering.Angular.Geometry
import OAI.Geometry.CylinderCovering.Angular.Caps

namespace OAI

open Set MeasureTheory
open RuledApproximation
open scoped InnerProductSpace
noncomputable section
namespace CylinderCovering.AngularGeneral

lemma planarSector_eq_image (D : Data) (j : ℕ) :
    planarSector D j = (fun p : ℝ × ℝ => vec2 (p.1 * p.2) p.2) ''
      AngularCaps.radialParameterSet (D.node j) (D.node (j+1)) (D.radius j) := by
  ext p
  constructor
  · rintro ⟨q, hq, s, hs, rfl⟩
    exact ⟨(q, s), ⟨hq, hs⟩, rfl⟩
  · rintro ⟨⟨q, s⟩, ⟨hq, hs⟩, rfl⟩
    exact ⟨q, hq, s, hs, rfl⟩

lemma planarSector_compact {D : Data} {j : ℕ}
    (hc : ContinuousOn (D.radius j) (interval D j))
    (hn : ∀ q ∈ interval D j, 0 ≤ D.radius j q) : IsCompact (planarSector D j) := by
  rw [planarSector_eq_image]
  apply (AngularCaps.isCompact_radialParameterSet hc hn).image
  unfold vec2
  fun_prop

lemma lowerAxis_eq_physicalUnit (τ : ℝ) (D : Data) (j : ℕ) :
    lowerAxis τ D j = physicalUnit TriangularCovering.H
      (vec2 (τ * D.alpha j) (τ * D.beta j)) := rfl

lemma lowerAxis_norm (τ : ℝ) (D : Data) (j : ℕ) : ‖lowerAxis τ D j‖ = 1 := by
  rw [lowerAxis_eq_physicalUnit]
  exact physicalUnit_norm _ _

lemma lowerIntercept_eq_image (D : Data) (j : ℕ) :
    lowerIntercept D j = planeEmbedding TriangularCovering.H '' planarSector D j := by
  ext z
  constructor
  · rintro ⟨q, hq, s, hs, rfl⟩
    exact ⟨vec2 (q*s) s, ⟨q, hq, s, hs, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨q, hq, s, hs, rfl⟩, rfl⟩
    exact ⟨q, hq, s, hs, rfl⟩

lemma projection_physicalUnit (h : ℝ) (g p : Plane) :
    TriangularCovering.projection (physicalUnit h g) (planeEmbedding h p) =
      rawProjection h g p := by
  unfold TriangularCovering.projection physicalUnit rawProjection
  simp only [LinearMap.coe_mk, AddHom.coe_mk, inner_smul_left, RCLike.conj_to_real,
    smul_smul]
  congr 1
  congr 1
  ring

lemma lowerBase_eq_rawImage (τ : ℝ) (D : Data) (j : ℕ) :
    lowerBase τ D j = rawProjection TriangularCovering.H
      (vec2 (τ * D.alpha j) (τ * D.beta j)) '' planarSector D j := by
  rw [lowerBase, lowerIntercept_eq_image, image_image]
  apply image_congr
  intro p hp
  rw [lowerAxis_eq_physicalUnit, projection_physicalUnit]

lemma ambient_area_of_intrinsic (C : Cylinder) :
    TriangularCovering.area ((Subtype.val :
      ((Submodule.span ℝ ({C.axis} : Set Space))ᗮ) → Space) '' C.base) = C.area := by
  unfold TriangularCovering.area Cylinder.area
  rw [isometry_subtype_coe.euclideanHausdorffMeasure_image]
  have hm : (Measure.euclideanHausdorffMeasure 2 :
      Measure ((Submodule.span ℝ ({C.axis} : Set Space))ᗮ)) = volume := by
    simpa only [perpendicularPlane_finrank _ C.unit_axis] using
      (InnerProductSpace.euclideanHausdorffMeasure_eq_volume
        (V := ((Submodule.span ℝ ({C.axis} : Set Space))ᗮ)))
  rw [hm]
  rfl

lemma lowerBase_area (τ : ℝ) (D : Data) (j : ℕ) :
    TriangularCovering.area (lowerBase τ D j) =
      AngularGeometry.areaFactor TriangularCovering.H τ (D.alpha j) (D.beta j) *
        volume.real (planarSector D j) := by
  have hbase : lowerBase τ D j = (Subtype.val :
      ((Submodule.span ℝ ({(AngularGeometry.lowerCylinder TriangularCovering.H τ
        (D.alpha j) (D.beta j) (planarSector D j)).axis} : Set Space))ᗮ) → Space) ''
      (AngularGeometry.lowerCylinder TriangularCovering.H τ
        (D.alpha j) (D.beta j) (planarSector D j)).base := by
    rw [lowerBase_eq_rawImage]
    change _ = Subtype.val '' (perpendicularProjection TriangularCovering.H
      (vec2 (τ * D.alpha j) (τ * D.beta j)) '' planarSector D j)
    rw [image_image]
    rfl
  rw [hbase, ambient_area_of_intrinsic]
  exact AngularGeometry.lowerCylinder_area (Real.sqrt_pos.mpr (by norm_num)) τ
    (D.alpha j) (D.beta j) (planarSector D j)

lemma lowerBase_compact {D : Data} {j : ℕ} (τ : ℝ)
    (hc : ContinuousOn (D.radius j) (interval D j))
    (hn : ∀ q ∈ interval D j, 0 ≤ D.radius j q) : IsCompact (lowerBase τ D j) := by
  rw [lowerBase_eq_rawImage]
  exact (planarSector_compact hc hn).image (rawProjection _ _).continuous_of_finiteDimensional

lemma lowerBase_finite {D : Data} {j : ℕ} (τ : ℝ)
    (hc : ContinuousOn (D.radius j) (interval D j))
    (hn : ∀ q ∈ interval D j, 0 ≤ D.radius j q) :
    Measure.euclideanHausdorffMeasure 2 (lowerBase τ D j) ≠ ⊤ := by
  rw [lowerBase_eq_rawImage]
  have he := (rawProjection TriangularCovering.H
    (vec2 (τ * D.alpha j) (τ * D.beta j))).euclideanHausdorffMeasure_image_eq_normDet_mul_volume
      (planarSector D j)
  rw [show Module.finrank ℝ Plane = 2 by simp] at he
  rw [he]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (planarSector_compact hc hn).measure_lt_top.ne

lemma projection_add (u x y : Space) :
    TriangularCovering.projection u (x+y) =
      TriangularCovering.projection u x + TriangularCovering.projection u y := by
  unfold TriangularCovering.projection
  rw [inner_add_right, add_smul]
  abel

lemma projection_rotate (R : Space ≃ₗᵢ[ℝ] Space) (u z : Space) :
    TriangularCovering.projection (R u) (R z) = R (TriangularCovering.projection u z) := by
  unfold TriangularCovering.projection
  rw [R.inner_map_map, map_sub, map_smul]

lemma upperDirection_eq_rotate (τ : ℝ) (D : Data) (j : ℕ) :
    upperDirection τ D j = swapReflect (lowerDirection (-τ) D j) := by
  ext i
  fin_cases i <;> simp [upperDirection, lowerDirection, TriangularCovering.point,
    swapReflect, vec3]

lemma upperAxis_eq_rotate (τ : ℝ) (D : Data) (j : ℕ) :
    upperAxis τ D j = swapReflect (lowerAxis (-τ) D j) := by
  unfold upperAxis lowerAxis unitDirection
  rw [upperDirection_eq_rotate, swapReflect.norm_map, map_smul]

lemma upperAxis_norm (τ : ℝ) (D : Data) (j : ℕ) : ‖upperAxis τ D j‖ = 1 := by
  rw [upperAxis_eq_rotate, swapReflect.norm_map, lowerAxis_norm]

lemma upperIntercept_eq_image (D : Data) (j : ℕ) :
    upperIntercept D j = (fun z => vec3 0 0 TriangularCovering.H + swapReflect z) ''
      lowerIntercept D j := by
  ext z
  constructor
  · rintro ⟨q, hq, t, ht, rfl⟩
    refine ⟨TriangularCovering.point 0 (q*t) t, ⟨q, hq, t, ht, rfl⟩, ?_⟩
    ext i
    fin_cases i <;> simp [TriangularCovering.point, swapReflect, vec3]; ring
  · rintro ⟨_, ⟨q, hq, t, ht, rfl⟩, rfl⟩
    refine ⟨q, hq, t, ht, ?_⟩
    ext i
    fin_cases i <;> simp [TriangularCovering.point, swapReflect, vec3]; ring

lemma upperBase_eq_image (τ : ℝ) (D : Data) (j : ℕ) :
    upperBase τ D j =
      (fun z => TriangularCovering.projection (upperAxis τ D j)
        (vec3 0 0 TriangularCovering.H) + swapReflect z) '' lowerBase (-τ) D j := by
  rw [upperBase, upperIntercept_eq_image, image_image, lowerBase, image_image]
  apply image_congr
  intro z hz
  rw [projection_add, upperAxis_eq_rotate, projection_rotate]

lemma upperBase_area_eq_lower (τ : ℝ) (D : Data) (j : ℕ) :
    TriangularCovering.area (upperBase τ D j) =
      TriangularCovering.area (lowerBase (-τ) D j) := by
  have hi : Isometry (fun z : Space => TriangularCovering.projection (upperAxis τ D j)
      (vec3 0 0 TriangularCovering.H) + swapReflect z) :=
    (isometry_add_left _).comp swapReflect.isometry
  unfold TriangularCovering.area
  rw [upperBase_eq_image, hi.euclideanHausdorffMeasure_image]

lemma upperBase_area (τ : ℝ) (D : Data) (j : ℕ) :
    TriangularCovering.area (upperBase τ D j) =
      AngularGeometry.areaFactor TriangularCovering.H τ (D.alpha j) (D.beta j) *
        volume.real (planarSector D j) := by
  rw [upperBase_area_eq_lower, lowerBase_area]
  simp [AngularGeometry.areaFactor]

lemma upperBase_compact {D : Data} {j : ℕ} (τ : ℝ)
    (hc : ContinuousOn (D.radius j) (interval D j))
    (hn : ∀ q ∈ interval D j, 0 ≤ D.radius j q) : IsCompact (upperBase τ D j) := by
  rw [upperBase_eq_image]
  exact (lowerBase_compact (-τ) hc hn).image (continuous_const.add swapReflect.continuous)

lemma upperBase_finite {D : Data} {j : ℕ} (τ : ℝ)
    (hc : ContinuousOn (D.radius j) (interval D j))
    (hn : ∀ q ∈ interval D j, 0 ≤ D.radius j q) :
    Measure.euclideanHausdorffMeasure 2 (upperBase τ D j) ≠ ⊤ := by
  have hi : Isometry (fun z : Space => TriangularCovering.projection (upperAxis τ D j)
      (vec3 0 0 TriangularCovering.H) + swapReflect z) :=
    (isometry_add_left _).comp swapReflect.isometry
  rw [upperBase_eq_image, hi.euclideanHausdorffMeasure_image]
  exact lowerBase_finite (-τ) hc hn

lemma projected_base_perpendicular {u : Space} (hu : ‖u‖ = 1) (P : Set Space) :
    ∀ z ∈ TriangularCovering.projection u '' P, inner ℝ u z = 0 := by
  rintro _ ⟨x, hx, rfl⟩
  simp [TriangularCovering.projection, inner_sub_right, inner_smul_right,
    hu]

lemma base_properties {D : Data} {j : ℕ} (τ : ℝ)
    (hc : ContinuousOn (D.radius j) (interval D j))
    (hn : ∀ q ∈ interval D j, 0 ≤ D.radius j q) :
    BaseProperties (lowerAxis τ D j) (lowerBase τ D j) ∧
      BaseProperties (upperAxis τ D j) (upperBase τ D j) := by
  constructor
  · have hcomp := lowerBase_compact τ hc hn
    exact ⟨lowerAxis_norm τ D j, projected_base_perpendicular (lowerAxis_norm τ D j) _,
      hcomp, hcomp.measurableSet, lowerBase_finite τ hc hn⟩
  · have hcomp := upperBase_compact τ hc hn
    exact ⟨upperAxis_norm τ D j, projected_base_perpendicular (upperAxis_norm τ D j) _,
      hcomp, hcomp.measurableSet, upperBase_finite τ hc hn⟩

lemma totalArea_eq_planar_sum (τ : ℝ) (D : Data) :
    totalArea τ D = 2 * ∑ j : Fin D.count,
      AngularGeometry.areaFactor TriangularCovering.H τ (D.alpha j) (D.beta j) *
        volume.real (planarSector D j) := by
  unfold totalArea
  simp only [lowerBase_area, upperBase_area, ← two_mul, Finset.mul_sum]

lemma cell_cost_of_planar_volume (τ : ℝ) (D : Data) (j : ℕ)
    (hvol : volume.real (planarSector D j) =
      ∫ q in D.node j..D.node (j+1), (D.radius j q)^2 / 2) :
    (TriangularCovering.area (lowerBase τ D j) +
      TriangularCovering.area (upperBase τ D j)) / TriangularCovering.H =
      ∫ q in D.node j..D.node (j+1),
        (D.radius j q)^2 / Real.sqrt (1+τ^2*((D.alpha j)^2+2*(D.beta j)^2)) := by
  rw [lowerBase_area, upperBase_area, hvol]
  unfold TriangularCovering.H
  rw [AngularGeometry.areaFactor_sqrt_two]
  simp only [intervalIntegral.integral_div]
  have hH : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hden : Real.sqrt (1+τ^2*((D.alpha j)^2+2*(D.beta j)^2)) ≠ 0 :=
    (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp
  ring

lemma integral_cost_of_planar_volumes (τ : ℝ) (D : Data)
    (hvol : ∀ j < D.count, volume.real (planarSector D j) =
      ∫ q in D.node j..D.node (j+1), (D.radius j q)^2 / 2) :
    totalArea τ D / TriangularCovering.H = integralCost τ D := by
  unfold totalArea integralCost
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  exact cell_cost_of_planar_volume τ D j (hvol j j.isLt)

end CylinderCovering.AngularGeneral

end

end OAI
