import OAI.Geometry.CylinderCovering.Radial.Projection
import OAI.Geometry.RuledCovering.Main

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace

namespace RadialProjection
open TriangularCovering

def coordinateLinear2 (a b : Space) : RuledApproximation.Plane →ₗ[ℝ] Space where
  toFun z := z 0 • a + z 1 • b
  map_add' z q := by simp only [PiLp.add_apply, add_smul]; module
  map_smul' c z := by
    simp only [PiLp.smul_apply, smul_add, smul_smul, RingHom.id_apply]
    rfl

def projectedCoordinateLinear (u a b : Space) : RuledApproximation.Plane →ₗ[ℝ] Space :=
  (projLinear u).comp (coordinateLinear2 a b)

@[simp] lemma projectedCoordinateLinear_apply (u a b : Space)
    (z : RuledApproximation.Plane) :
    projectedCoordinateLinear u a b z = projection u (z 0 • a + z 1 • b) := rfl

lemma projectedCoordinateLinear_normDet {u : Space} (hu : ‖u‖ = 1) (a b : Space) :
    (projectedCoordinateLinear u a b).normDet = |inner ℝ u (cross3 a b)| := by
  let f := projectedCoordinateLinear u a b
  have h0 : f (EuclideanSpace.basisFun (Fin 2) ℝ 0) = projection u a := by
    simp [f, EuclideanSpace.basisFun_apply]
  have h1 : f (EuclideanSpace.basisFun (Fin 2) ℝ 1) = projection u b := by
    simp [f, EuclideanSpace.basisFun_apply]
  have hd := f.normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin 2) ℝ)
  simp only [RCLike.ofReal_real_eq_id, id_eq, Matrix.det_fin_two, Matrix.gram_apply,
    h0, h1] at hd
  rw [real_inner_comm (projection u a) (projection u b)] at hd
  have hs : f.normDet ^ 2 = (inner ℝ u (cross3 a b)) ^ 2 := by
    rw [← projected_gram hu]
    simpa only [pow_two] using hd
  have hn := f.normDet_nonneg
  have ha := abs_nonneg (inner ℝ u (cross3 a b))
  have hab := sq_abs (inner ℝ u (cross3 a b))
  change f.normDet = _
  nlinarith

lemma affine_projected_image (p₀ u a b : Space) (S : Set (ℝ × ℝ)) :
    projection u '' (coordinateAffine p₀ a b '' S) =
      (fun x : Space => projection u p₀ + x) ''
        (projectedCoordinateLinear u a b '' (RuledApproximation.pairPlaneEquiv '' S)) := by
  simp only [image_image]
  congr 1
  funext z
  change projection u (p₀ + z.1 • a + z.2 • b) =
    projection u p₀ + projection u (z.1 • a + z.2 • b)
  simpa only [projLinear_apply, add_assoc] using (projLinear u).map_add p₀ (z.1 • a + z.2 • b)

theorem affine_projection_measure (p₀ u a b : Space) (hu : ‖u‖ = 1)
    (S : Set (ℝ × ℝ)) :
    Measure.euclideanHausdorffMeasure 2 (projection u '' (coordinateAffine p₀ a b '' S)) =
      ENNReal.ofReal |inner ℝ u (cross3 a b)| * volume S := by
  rw [affine_projected_image,
    (isometry_add_left (projection u p₀)).euclideanHausdorffMeasure_image]
  have hm := (projectedCoordinateLinear u a b).euclideanHausdorffMeasure_image_eq_normDet_mul_volume
    (RuledApproximation.pairPlaneEquiv '' S)
  simp only [finrank_euclideanSpace_fin] at hm
  rw [hm, projectedCoordinateLinear_normDet hu,
    measurePreserving_image RuledApproximation.pairPlane_measurePreserving
      RuledApproximation.pairPlaneEquiv.measurableEmbedding]

theorem affine_projection_area (p₀ u a b : Space) (hu : ‖u‖ = 1)
    (S : Set (ℝ × ℝ)) :
    area (projection u '' (coordinateAffine p₀ a b '' S)) =
      |inner ℝ u (cross3 a b)| * volume.real S := by
  unfold area
  rw [affine_projection_measure p₀ u a b hu S, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]
  rfl

theorem radial_affine_projection_area (p₀ e a b w : Space)
    (he : ‖e‖ = 1) (ha : inner ℝ e a = 0) (hb : inner ℝ e b = 0)
    (hw : inner ℝ e w = 0) (S : Set (ℝ × ℝ)) :
    area (projection (unit (e + w)) '' (coordinateAffine p₀ a b '' S)) =
      Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2) /
        Real.sqrt (1 + ‖w‖ ^ 2) * volume.real S := by
  rw [affine_projection_area p₀ (unit (e + w)) a b
    (unit_norm (sideways_ne_zero he hw)), normal_projection_factor he ha hb hw]

theorem affine_projection_finite (p₀ u a b : Space) (hu : ‖u‖ = 1)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S) :
    Measure.euclideanHausdorffMeasure 2 (projection u '' (coordinateAffine p₀ a b '' S)) ≠ ⊤ := by
  rw [affine_projection_measure p₀ u a b hu S]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS.measure_ne_top

theorem affine_projection_isCompact (p₀ u a b : Space)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S) :
    IsCompact (projection u '' (coordinateAffine p₀ a b '' S)) := by
  have hc : Continuous (coordinateAffine p₀ a b) := by
    change Continuous (fun z : ℝ × ℝ => p₀ + z.1 • a + z.2 • b)
    fun_prop
  exact (hS.image hc).image (projLinear u).continuous_of_finiteDimensional

end RadialProjection

end

end OAI
