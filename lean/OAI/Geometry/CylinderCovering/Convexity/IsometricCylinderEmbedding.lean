import OAI.Geometry.CylinderCovering.Convexity.IsometricCylinderEmbeddingDefinitions
import OAI.Geometry.CylinderCovering.Convexity.CylinderSimilarity

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

namespace CylinderCovering.IsometricEmbedding

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma map_isometry (t : F) (L : E →ₗᵢ[ℝ] F) : Isometry (map t L) := by
  apply Isometry.of_dist_eq
  intro x y
  simp [map]

lemma baseMap_isometry (u : E) (t : F) (L : E →ₗᵢ[ℝ] F) :
    Isometry (baseMap u t L) := map_isometry (Similarity.project (L u) t) L

lemma axis_unit {u : E} (hu : ‖u‖ = 1) (L : E →ₗᵢ[ℝ] F) : ‖L u‖ = 1 := by
  simpa using hu

lemma project_map (u : E) (t : F) (L : E →ₗᵢ[ℝ] F) (x : E) :
    Similarity.project (L u) (map t L x) =
      baseMap u t L (Similarity.project u x) := by
  simp only [Similarity.project, map, baseMap, inner_add_right,
    L.inner_map_map, map_sub, map_smul]
  module

lemma projected_image_eq (S : Set E) (u : E) (t : F) (L : E →ₗᵢ[ℝ] F) :
    Similarity.project (L u) '' (map t L '' S) =
      transportedBase (Similarity.project u '' S) u t L := by
  unfold transportedBase
  rw [image_image, image_image]
  congr 1
  funext x
  exact project_map u t L x

lemma carrier_image (B : Set E) (u : E) (t : F) (L : E →ₗᵢ[ℝ] F) :
    map t L '' Similarity.carrier B u =
      Similarity.carrier (transportedBase B u t L) (L u) := by
  ext z
  constructor
  · rintro ⟨x, ⟨b, hb, s, rfl⟩, rfl⟩
    refine ⟨baseMap u t L b, ⟨b, hb, rfl⟩, inner ℝ (L u) t + s, ?_⟩
    simp only [map, baseMap, Similarity.project, map_add, map_smul]
    module
  · rintro ⟨b', ⟨b, hb, rfl⟩, s, rfl⟩
    refine ⟨b + (s - inner ℝ (L u) t) • u,
      ⟨b, hb, s - inner ℝ (L u) t, rfl⟩, ?_⟩
    simp only [map, baseMap, Similarity.project, map_add, map_smul]
    module

lemma covers_image {ι : Type*} (K : Set E) (B : ι → Set E) (u : ι → E)
    (h : ∀ x ∈ K, ∃ i, x ∈ Similarity.carrier (B i) (u i))
    (t : F) (L : E →ₗᵢ[ℝ] F) :
    ∀ x ∈ map t L '' K, ∃ i,
      x ∈ Similarity.carrier (transportedBase (B i) (u i) t L) (L (u i)) := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨i, hi⟩ := h y hy
  refine ⟨i, ?_⟩
  rw [← carrier_image]
  exact ⟨y, hi, rfl⟩

lemma transportedBase_perpendicular {B : Set E} {u : E} (hu : ‖u‖ = 1)
    (hB : ∀ x ∈ B, inner ℝ u x = 0) (t : F) (L : E →ₗᵢ[ℝ] F) :
    ∀ z ∈ transportedBase B u t L, inner ℝ (L u) z = 0 := by
  rintro z ⟨b, hb, rfl⟩
  have huu : inner ℝ (L u) (L u) = 1 := by
    rw [L.inner_map_map, real_inner_self_eq_norm_sq, hu]
    norm_num
  simp only [baseMap, Similarity.project, inner_add_right, inner_sub_right,
    inner_smul_right, huu, mul_one, sub_self, L.inner_map_map, hB b hb, add_zero]

lemma transportedBase_compact {B : Set E} (hB : IsCompact B)
    (u : E) (t : F) (L : E →ₗᵢ[ℝ] F) :
    IsCompact (transportedBase B u t L) := hB.image (baseMap_isometry u t L).continuous

lemma projected_image_compact {S : Set E} (hS : IsCompact S)
    (u : E) (t : F) (L : E →ₗᵢ[ℝ] F) :
    IsCompact (Similarity.project (L u) '' (map t L '' S)) := by
  apply IsCompact.image (hS.image (map_isometry t L).continuous)
  unfold Similarity.project
  fun_prop

lemma projected_image_perpendicular (S : Set E) {u : E} (hu : ‖u‖ = 1)
    (t : F) (L : E →ₗᵢ[ℝ] F) :
    ∀ z ∈ Similarity.project (L u) '' (map t L '' S), inner ℝ (L u) z = 0 := by
  rintro z ⟨x, hx, rfl⟩
  have huu : inner ℝ (L u) (L u) = 1 := by
    rw [L.inner_map_map, real_inner_self_eq_norm_sq, hu]
    norm_num
  simp only [Similarity.project, inner_sub_right, inner_smul_right, huu,
    mul_one, sub_self]

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

lemma transportedBase_measure (B : Set E) (u : E) (t : F)
    (L : E →ₗᵢ[ℝ] F) (d : ℕ) :
    Measure.euclideanHausdorffMeasure d (transportedBase B u t L) =
      Measure.euclideanHausdorffMeasure d B :=
  (baseMap_isometry u t L).euclideanHausdorffMeasure_image B

lemma transportedBase_area (B : Set E) (u : E) (t : F) (L : E →ₗᵢ[ℝ] F) :
    Similarity.area (transportedBase B u t L) = Similarity.area B := by
  unfold Similarity.area
  rw [transportedBase_measure]

lemma projected_image_area (S : Set E) (u : E) (t : F) (L : E →ₗᵢ[ℝ] F) :
    Similarity.area (Similarity.project (L u) '' (map t L '' S)) =
      Similarity.area (Similarity.project u '' S) := by
  rw [projected_image_eq, transportedBase_area]

lemma transportedBase_finite {B : Set E}
    (hB : Measure.euclideanHausdorffMeasure 2 B ≠ ⊤)
    (u : E) (t : F) (L : E →ₗᵢ[ℝ] F) :
    Measure.euclideanHausdorffMeasure 2 (transportedBase B u t L) ≠ ⊤ := by
  rwa [transportedBase_measure]

lemma actual_total_area {ι : Type*} [Fintype ι] (S : ι → Set E) (u : ι → E)
    (t : F) (L : E →ₗᵢ[ℝ] F) :
    (∑ i, Similarity.area (Similarity.project (L (u i)) '' (map t L '' S i))) =
      ∑ i, Similarity.area (Similarity.project (u i) '' S i) := by
  apply Finset.sum_congr rfl
  intro i _
  exact projected_image_area (S i) (u i) t L

lemma actual_limsup_le {S : (N : ℕ) → Fin N → Set E} {u : (N : ℕ) → Fin N → E}
    (t : F) (L : E →ₗᵢ[ℝ] F) {A : ℝ}
    (h : Filter.limsup (fun N => ∑ i, Similarity.area
      (Similarity.project (u N i) '' S N i)) atTop ≤ A) :
    Filter.limsup (fun N => ∑ i, Similarity.area
      (Similarity.project (L (u N i)) '' (map t L '' S N i))) atTop ≤ A := by
  simpa only [actual_total_area] using h

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma scaled_map_image (S : Set E) (t : F) (r : ℝ) (L : E →ₗᵢ[ℝ] F) :
    scaledMap t r L '' S =
      Similarity.map t r (LinearIsometryEquiv.refl ℝ F) '' (L '' S) := by
  rw [image_image]
  rfl

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma scaled_project_map (u : E) (t : F) (r : ℝ) (L : E →ₗᵢ[ℝ] F) (x : E) :
    Similarity.project (L u) (scaledMap t r L x) =
      scaledBaseMap u t r L (Similarity.project u x) := by
  simp only [Similarity.project, scaledMap, scaledBaseMap, inner_add_right,
    inner_smul_right, L.inner_map_map, map_sub, map_smul]
  module

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma scaled_projected_image_eq (S : Set E) (u : E) (t : F) (r : ℝ)
    (L : E →ₗᵢ[ℝ] F) :
    Similarity.project (L u) '' (scaledMap t r L '' S) =
      scaledTransportedBase (Similarity.project u '' S) u t r L := by
  unfold scaledTransportedBase
  rw [image_image, image_image]
  congr 1
  funext x
  exact scaled_project_map u t r L x

lemma scaled_map_measure (B : Set E) (t : F) {r : ℝ} (hr : r ≠ 0)
    (L : E →ₗᵢ[ℝ] F) (d : ℕ) :
    Measure.euclideanHausdorffMeasure d (scaledMap t r L '' B) =
      ‖r‖₊ ^ d • Measure.euclideanHausdorffMeasure d B := by
  rw [scaled_map_image, Similarity.euclideanHausdorffMeasure_map t hr,
    L.isometry.euclideanHausdorffMeasure_image]

lemma scaled_map_area (B : Set E) (t : F) {r : ℝ} (hr : r ≠ 0)
    (L : E →ₗᵢ[ℝ] F) :
    Similarity.area (scaledMap t r L '' B) = r ^ 2 * Similarity.area B := by
  rw [scaled_map_image, Similarity.area_map t hr]
  congr 1
  unfold Similarity.area
  rw [L.isometry.euclideanHausdorffMeasure_image]

lemma scaled_transportedBase_area (B : Set E) (u : E) (t : F) {r : ℝ}
    (hr : r ≠ 0) (L : E →ₗᵢ[ℝ] F) :
    Similarity.area (scaledTransportedBase B u t r L) = r ^ 2 * Similarity.area B :=
  scaled_map_area B (Similarity.project (L u) t) hr L

lemma scaled_projected_image_area (S : Set E) (u : E) (t : F) {r : ℝ}
    (hr : r ≠ 0) (L : E →ₗᵢ[ℝ] F) :
    Similarity.area (Similarity.project (L u) '' (scaledMap t r L '' S)) =
      r ^ 2 * Similarity.area (Similarity.project u '' S) := by
  rw [scaled_projected_image_eq, scaled_transportedBase_area _ _ _ hr]

lemma scaled_transportedBase_finite {B : Set E}
    (hB : Measure.euclideanHausdorffMeasure 2 B ≠ ⊤) (u : E) (t : F)
    {r : ℝ} (hr : r ≠ 0) (L : E →ₗᵢ[ℝ] F) :
    Measure.euclideanHausdorffMeasure 2 (scaledTransportedBase B u t r L) ≠ ⊤ := by
  change Measure.euclideanHausdorffMeasure 2
    (scaledMap (Similarity.project (L u) t) r L '' B) ≠ ⊤
  rw [scaled_map_measure _ _ hr]
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top hB

lemma scaled_actual_total_area {ι : Type*} [Fintype ι]
    (S : ι → Set E) (u : ι → E) (t : F) {r : ℝ} (hr : r ≠ 0)
    (L : E →ₗᵢ[ℝ] F) :
    (∑ i, Similarity.area (Similarity.project (L (u i)) '' (scaledMap t r L '' S i))) =
      r ^ 2 * ∑ i, Similarity.area (Similarity.project (u i) '' S i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact scaled_projected_image_area (S i) (u i) t hr L

lemma scaled_actual_eventually_le
    {S : (N : ℕ) → Fin N → Set E} {u : (N : ℕ) → Fin N → E}
    (t : F) {r : ℝ} (hr : r ≠ 0) (L : E →ₗᵢ[ℝ] F) {A : ℝ}
    (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ N in atTop,
      (∑ i, Similarity.area (Similarity.project (u N i) '' S N i)) ≤ A + δ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ N in atTop,
      (∑ i, Similarity.area (Similarity.project (L (u N i)) ''
        (scaledMap t r L '' S N i))) ≤ r ^ 2 * A + δ := by
  intro δ hδ
  have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  filter_upwards [h (δ / r ^ 2) (div_pos hδ hr2)] with N hN
  rw [scaled_actual_total_area _ _ _ hr]
  calc
    _ ≤ r ^ 2 * (A + δ / r ^ 2) := mul_le_mul_of_nonneg_left hN hr2.le
    _ = r ^ 2 * A + δ := by field_simp

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma scaled_carrier_image (B : Set E) (u : E) (t : F) {r : ℝ}
    (hr : r ≠ 0) (L : E →ₗᵢ[ℝ] F) :
    scaledMap t r L '' Similarity.carrier B u =
      Similarity.carrier (scaledTransportedBase B u t r L) (L u) := by
  ext z
  constructor
  · rintro ⟨x, ⟨b, hb, s, rfl⟩, rfl⟩
    refine ⟨scaledBaseMap u t r L b, ⟨b, hb, rfl⟩,
      inner ℝ (L u) t + r * s, ?_⟩
    simp only [scaledMap, scaledBaseMap, Similarity.project, map_add, map_smul]
    module
  · rintro ⟨b', ⟨b, hb, rfl⟩, s, rfl⟩
    refine ⟨b + ((s - inner ℝ (L u) t) / r) • u,
      ⟨b, hb, (s - inner ℝ (L u) t) / r, rfl⟩, ?_⟩
    simp only [scaledMap, scaledBaseMap, Similarity.project, map_add, map_smul,
      smul_add, smul_smul]
    rw [mul_div_cancel₀ _ hr]
    module

lemma scaled_actual_limsup_le
    {S : (N : ℕ) → Fin N → Set E} {u : (N : ℕ) → Fin N → E}
    (t : F) {r : ℝ} (hr : r ≠ 0) (L : E →ₗᵢ[ℝ] F) {A : ℝ}
    (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ N in atTop,
      (∑ i, Similarity.area (Similarity.project (u N i) '' S N i)) ≤ A + δ) :
    Filter.limsup (fun N => ∑ i, Similarity.area
      (Similarity.project (L (u N i)) '' (scaledMap t r L '' S N i))) atTop ≤ r ^ 2 * A := by
  let f : ℕ → ℝ := fun N => ∑ i, Similarity.area
    (Similarity.project (L (u N i)) '' (scaledMap t r L '' S N i))
  have h0 : ∀ N, 0 ≤ f N := fun _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hevent := scaled_actual_eventually_le t hr L h
  change Filter.limsup f atTop ≤ r ^ 2 * A
  by_contra hnot
  have hlt : r ^ 2 * A < Filter.limsup f atTop := lt_of_not_ge hnot
  have hbound := Filter.limsup_le_of_le (isCoboundedUnder_le_of_le atTop h0)
    (hevent ((Filter.limsup f atTop - r ^ 2 * A) / 2) (by linarith))
  change Filter.limsup f atTop ≤ _ at hbound
  linarith

end CylinderCovering.IsometricEmbedding

end

end OAI
