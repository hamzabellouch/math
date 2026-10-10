import OAI.Geometry.CylinderCovering.Convexity.SimilarityDefinitions

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace Pointwise

noncomputable section
namespace CylinderCovering.Similarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma map_injective (t : E) {r : ℝ} (hr : r ≠ 0) (L : E ≃ₗᵢ[ℝ] E) :
    Function.Injective (map t r L) := by
  intro x y h
  apply L.injective
  exact (smul_right_injective E hr) (add_left_cancel h)

lemma map_surjective (t : E) {r : ℝ} (hr : r ≠ 0) (L : E ≃ₗᵢ[ℝ] E) :
    Function.Surjective (map t r L) := by
  intro y
  refine ⟨L.symm (r⁻¹ • (y - t)), ?_⟩
  simp [map, hr]

lemma map_continuous (t : E) (r : ℝ) (L : E ≃ₗᵢ[ℝ] E) :
    Continuous (map t r L) := by
  exact continuous_const.add (L.continuous.const_smul r)

lemma project_map (u t x : E) (r : ℝ) (L : E ≃ₗᵢ[ℝ] E) :
    project (L u) (map t r L x) =
      project (L u) t + r • L (project u x) := by
  simp only [project, map, inner_add_right, inner_smul_right,
    L.inner_map_map, map_sub, map_smul]
  module

lemma project_perpendicular {u : E} (hu : ‖u‖ = 1) (x : E) :
    inner ℝ u (project u x) = 0 := by
  have huu : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq, hu]
    norm_num
  simp only [project, inner_sub_right, inner_smul_right, huu, mul_one, sub_self]

lemma transportedBase_perpendicular {u : E} {B : Set E}
    (hu : ‖u‖ = 1) (hB : ∀ x ∈ B, inner ℝ u x = 0)
    (t : E) (r : ℝ) (L : E ≃ₗᵢ[ℝ] E) :
    ∀ x ∈ transportedBase B u t r L, inner ℝ (L u) x = 0 := by
  rintro x ⟨b, hb, rfl⟩
  simp only [baseMap, inner_add_right, inner_smul_right, L.inner_map_map]
  rw [project_perpendicular (by simpa using hu), hB b hb]
  simp

lemma carrier_image (B : Set E) (u t : E) {r : ℝ} (hr : r ≠ 0)
    (L : E ≃ₗᵢ[ℝ] E) :
    map t r L '' carrier B u = carrier (transportedBase B u t r L) (L u) := by
  ext z
  constructor
  · rintro ⟨x, ⟨b, hb, s, rfl⟩, rfl⟩
    refine ⟨baseMap u t r L b, ⟨b, hb, rfl⟩,
      inner ℝ (L u) t + r * s, ?_⟩
    simp only [map, baseMap, project, map_add, map_smul]
    module
  · rintro ⟨b', ⟨b, hb, rfl⟩, s, rfl⟩
    refine ⟨b + ((s - inner ℝ (L u) t) / r) • u,
      ⟨b, hb, (s - inner ℝ (L u) t) / r, rfl⟩, ?_⟩
    simp only [map, baseMap, project, map_add, map_smul, smul_add, smul_smul]
    rw [mul_div_cancel₀ _ hr]
    module

lemma covers_image {ι : Type*} (K : Set E) (B : ι → Set E) (u : ι → E)
    (h : ∀ x ∈ K, ∃ i, x ∈ carrier (B i) (u i))
    (t : E) {r : ℝ} (hr : r ≠ 0) (L : E ≃ₗᵢ[ℝ] E) :
    ∀ x ∈ map t r L '' K, ∃ i,
      x ∈ carrier (transportedBase (B i) (u i) t r L) (L (u i)) := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨i, hi⟩ := h y hy
  refine ⟨i, ?_⟩
  rw [← carrier_image (B i) (u i) t hr L]
  exact ⟨y, hi, rfl⟩

lemma affineMap_apply (t : E) (r : ℝ) (L : E ≃ₗᵢ[ℝ] E) (x : E) :
    affineMap t r L x = map t r L x := rfl

lemma transportedBase_convex {B : Set E} (hB : Convex ℝ B)
    (u t : E) (r : ℝ) (L : E ≃ₗᵢ[ℝ] E) :
    Convex ℝ (transportedBase B u t r L) :=
  hB.affine_image (affineMap (project (L u) t) r L)

lemma transportedBase_triangular {B : Set E}
    (hB : ∃ v : Fin 3 → E, AffineIndependent ℝ v ∧
      B = convexHull ℝ (range v))
    (u t : E) {r : ℝ} (hr : r ≠ 0) (L : E ≃ₗᵢ[ℝ] E) :
    ∃ v : Fin 3 → E, AffineIndependent ℝ v ∧
      transportedBase B u t r L = convexHull ℝ (range v) := by
  rcases hB with ⟨v, hv, rfl⟩
  let f := affineMap (project (L u) t) r L
  refine ⟨f ∘ v, hv.map' f (map_injective _ hr L), ?_⟩
  change f '' convexHull ℝ (range v) = convexHull ℝ (range (f ∘ v))
  rw [f.image_convexHull, range_comp]

variable [MeasurableSpace E] [BorelSpace E]

lemma euclideanHausdorffMeasure_map (t : E) {r : ℝ} (hr : r ≠ 0)
    (L : E ≃ₗᵢ[ℝ] E) (B : Set E) (d : ℕ) :
    Measure.euclideanHausdorffMeasure d (map t r L '' B) =
      ‖r‖₊ ^ d • Measure.euclideanHausdorffMeasure d B := by
  have himage : map t r L '' B =
      (fun x : E => t + x) '' (r • (L '' B)) := by
    change (fun x => t + r • L x) '' B =
      (fun x : E => t + x) '' ((fun x : E => r • x) '' (L '' B))
    rw [image_image, image_image]
  have ht : Isometry (fun x : E => t + x) :=
    Isometry.of_dist_eq fun x y => by simp
  rw [himage, ht.euclideanHausdorffMeasure_image (r • (L '' B)),
    Measure.euclideanHausdorffMeasure_smul₀ d hr,
    L.isometry.euclideanHausdorffMeasure_image B]

lemma area_map (t : E) {r : ℝ} (hr : r ≠ 0)
    (L : E ≃ₗᵢ[ℝ] E) (B : Set E) :
    area (map t r L '' B) = r ^ 2 * area B := by
  unfold area
  rw [euclideanHausdorffMeasure_map t hr L B 2]
  simp [ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul,
    Real.norm_eq_abs]

lemma area_transportedBase (B : Set E) (u t : E) {r : ℝ} (hr : r ≠ 0)
    (L : E ≃ₗᵢ[ℝ] E) :
    area (transportedBase B u t r L) = r ^ 2 * area B :=
  area_map (project (L u) t) hr L B

omit [MeasurableSpace E] [BorelSpace E] in
lemma transportedBase_compact {B : Set E} (hB : IsCompact B)
    (u t : E) (r : ℝ) (L : E ≃ₗᵢ[ℝ] E) :
    IsCompact (transportedBase B u t r L) :=
  hB.image (map_continuous (project (L u) t) r L)

lemma transportedBase_finite {B : Set E}
    (hB : Measure.euclideanHausdorffMeasure 2 B ≠ ⊤)
    (u t : E) {r : ℝ} (hr : r ≠ 0) (L : E ≃ₗᵢ[ℝ] E) :
    Measure.euclideanHausdorffMeasure 2 (transportedBase B u t r L) ≠ ⊤ := by
  change Measure.euclideanHausdorffMeasure 2
    (map (project (L u) t) r L '' B) ≠ ⊤
  rw [euclideanHausdorffMeasure_map (project (L u) t) hr L B 2]
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top hB

lemma shadowArea_map (K : Set E) (t : E) {r : ℝ} (hr : r ≠ 0)
    (L : E ≃ₗᵢ[ℝ] E) (u : E) :
    shadowArea (map t r L '' K) (L u) = r ^ 2 * shadowArea K u := by
  unfold shadowArea
  have himage : project (L u) '' (map t r L '' K) =
      map (project (L u) t) r L '' (project u '' K) := by
    simp only [image_image]
    congr 1
    funext x
    exact project_map u t x r L
  rw [himage, area_map _ hr L]

lemma shadowArea_range_map (K : Set E) (t : E) {r : ℝ} (hr : r ≠ 0)
    (L : E ≃ₗᵢ[ℝ] E) :
    {a : ℝ | ∃ u : E, ‖u‖ = 1 ∧ a = shadowArea (map t r L '' K) u} =
    (fun a : ℝ => r ^ 2 * a) '' {a : ℝ | ∃ u : E, ‖u‖ = 1 ∧ a = shadowArea K u} := by
  ext a
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨shadowArea K (L.symm u), ⟨L.symm u, by simpa using hu, rfl⟩, ?_⟩
    simpa using (shadowArea_map K t hr L (L.symm u)).symm
  · rintro ⟨b, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨L u, by simpa using hu, (shadowArea_map K t hr L u).symm⟩

lemma minimumArea_le_shadowArea (K : Set E) {u : E} (hu : ‖u‖ = 1) :
    minimumArea K ≤ shadowArea K u := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro a ⟨v, hv, rfl⟩
    exact ENNReal.toReal_nonneg
  · exact ⟨u, hu, rfl⟩

lemma minimumArea_map [Nontrivial E] (K : Set E) (t : E) {r : ℝ} (hr : r ≠ 0)
    (L : E ≃ₗᵢ[ℝ] E) :
    minimumArea (map t r L '' K) = r ^ 2 * minimumArea K := by
  have hne : {a : ℝ | ∃ u : E, ‖u‖ = 1 ∧ a = shadowArea K u}.Nonempty := by
    obtain ⟨u, hu⟩ := exists_norm_eq E (show (0:ℝ) ≤ 1 by norm_num)
    exact ⟨shadowArea K u, u, hu, rfl⟩
  have hbdd : BddBelow {a : ℝ | ∃ u : E, ‖u‖ = 1 ∧ a = shadowArea K u} := by
    refine ⟨0, ?_⟩
    rintro a ⟨u, hu, rfl⟩
    exact ENNReal.toReal_nonneg
  unfold minimumArea
  rw [shadowArea_range_map K t hr L]
  exact ((OrderIso.mulLeft₀ (r ^ 2) (sq_pos_of_ne_zero hr)).map_csInf' hne hbdd).symm

lemma areaRatio_map (B K : Set E) (u t : E) {r : ℝ} (hr : r ≠ 0)
    (L : E ≃ₗᵢ[ℝ] E) :
    area (transportedBase B u t r L) / shadowArea (map t r L '' K) (L u) =
      area B / shadowArea K u := by
  rw [area_transportedBase B u t hr L, shadowArea_map K t hr L u]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hr)

end CylinderCovering.Similarity

end

end OAI
