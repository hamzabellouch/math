import OAI.Geometry.RuledCovering.Model
import OAI.Geometry.CylinderCovering.Convexity.CylinderSimilarity

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace RuledApproximation

abbrev AxisPlane (u : Space) := ((Submodule.span ℝ ({u} : Set Space))ᗮ)

def similarityPlaneEquiv (u : Space) (L : Space ≃ₗᵢ[ℝ] Space) :
    AxisPlane u ≃ₗᵢ[ℝ] AxisPlane (L u) where
  toFun x := ⟨L x, by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    rw [L.inner_map_map]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property⟩
  invFun y := ⟨L.symm y, by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    have h := Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.property
    rw [← L.inner_map_map u (L.symm y), L.apply_symm_apply]
    exact h⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp
  map_smul' r x := by ext; simp
  norm_map' x := by change ‖L (x : Space)‖ = ‖(x : Space)‖; simp

def similarityPlaneTranslation (u : Space) (hu : ‖u‖ = 1) (t : Space) : AxisPlane u :=
  ⟨CylinderCovering.Similarity.project u t,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      (CylinderCovering.Similarity.project_perpendicular hu t)⟩

def similarityPlaneMap (u : Space) (hu : ‖u‖ = 1) (t : Space)
    {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    AxisPlane u ≃ᵃ[ℝ] AxisPlane (L u) :=
  ((similarityPlaneEquiv u L).toLinearEquiv.toAffineEquiv.trans
    (LinearEquiv.smulOfNeZero ℝ (AxisPlane (L u)) r hr).toAffineEquiv).trans
    (AffineEquiv.constVAdd ℝ (AxisPlane (L u))
      (similarityPlaneTranslation (L u) (by simpa using hu) t))

lemma similarityPlaneMap_coe (u : Space) (hu : ‖u‖ = 1) (t : Space)
    {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) (x : AxisPlane u) :
    (similarityPlaneMap u hu t hr L x : Space) =
      CylinderCovering.Similarity.baseMap u t r L x := rfl

lemma similarityPlaneMap_image (u : Space) (hu : ‖u‖ = 1) (t : Space)
    {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) (B : Set (AxisPlane u)) :
    Subtype.val '' (similarityPlaneMap u hu t hr L '' B) =
      CylinderCovering.Similarity.transportedBase (Subtype.val '' B) u t r L := by
  simp only [CylinderCovering.Similarity.transportedBase, image_image]
  rfl

lemma similarityPlane_finrank (u : Space) (hu : ‖u‖ = 1) :
    Module.finrank ℝ (AxisPlane u) = 2 := by
  have hne : u ≠ 0 := by intro hz; simp [hz] at hu
  have hd := (Submodule.span ℝ ({u} : Set Space)).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hne, finrank_euclideanSpace_fin] at hd
  change 1 + Module.finrank ℝ (AxisPlane u) = 3 at hd
  omega

lemma similarityPlane_area (u : Space) (hu : ‖u‖ = 1) (B : Set (AxisPlane u)) :
    CylinderCovering.Similarity.area (Subtype.val '' B) = volume.real B := by
  unfold CylinderCovering.Similarity.area Measure.real
  rw [isometry_subtype_coe.euclideanHausdorffMeasure_image]
  have hm : (Measure.euclideanHausdorffMeasure 2 : Measure (AxisPlane u)) = volume := by
    simpa only [similarityPlane_finrank u hu] using
      (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := AxisPlane u))
  rw [hm]

lemma affineEquiv_combination {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (f : E ≃ᵃ[ℝ] F) (c u v : E) (s t : ℝ) :
    f (c + s • u + t • v) = f c + s • f.linear u + t • f.linear v := by
  have h := f.map_vadd c (s • u + t • v)
  simp only [vadd_eq_add, map_add, map_smul] at h
  convert h using 1 <;> abel_nf

lemma IsParallelogram.affineEquiv {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] {B : Set E} (hB : IsParallelogram B)
    (f : E ≃ᵃ[ℝ] F) : IsParallelogram (f '' B) := by
  rcases hB with ⟨c, u, v, huv, rfl⟩
  refine ⟨f c, f.linear u, f.linear v, ?_, ?_⟩
  · have heq : (![f.linear u, f.linear v] : Fin 2 → F) = f.linear ∘ ![u, v] := by
      ext i
      fin_cases i <;> rfl
    rw [heq]
    exact huv.map' f.linear.toLinearMap (LinearMap.ker_eq_bot.mpr f.linear.injective)
  · ext x
    constructor
    · rintro ⟨y, ⟨s, hs, t, ht, rfl⟩, rfl⟩
      exact ⟨s, hs, t, ht, affineEquiv_combination f c u v s t⟩
    · rintro ⟨s, hs, t, ht, rfl⟩
      exact ⟨c + s • u + t • v, ⟨s, hs, t, ht, rfl⟩,
        affineEquiv_combination f c u v s t⟩

lemma IsTriangle.affineEquiv {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] {B : Set E} (hB : IsTriangle B)
    (f : E ≃ᵃ[ℝ] F) : IsTriangle (f '' B) := by
  rcases hB with ⟨c, u, v, huv, rfl⟩
  refine ⟨f c, f.linear u, f.linear v, ?_, ?_⟩
  · have heq : (![f.linear u, f.linear v] : Fin 2 → F) = f.linear ∘ ![u, v] := by
      ext i
      fin_cases i <;> rfl
    rw [heq]
    exact huv.map' f.linear.toLinearMap (LinearMap.ker_eq_bot.mpr f.linear.injective)
  · ext x
    constructor
    · rintro ⟨y, ⟨s, t, hs, ht, hst, rfl⟩, rfl⟩
      exact ⟨s, t, hs, ht, hst, affineEquiv_combination f c u v s t⟩
    · rintro ⟨s, t, hs, ht, hst, rfl⟩
      exact ⟨c + s • u + t • v, ⟨s, t, hs, ht, hst, rfl⟩,
        affineEquiv_combination f c u v s t⟩

namespace Cylinder

def similarity (c : Cylinder) (t : Space) {r : ℝ} (hr : r ≠ 0)
    (L : Space ≃ₗᵢ[ℝ] Space) : Cylinder where
  axis := L c.axis
  unit_axis := by simpa using c.unit_axis
  base := similarityPlaneMap c.axis c.unit_axis t hr L '' c.base

lemma carrier_eq_ambient (c : Cylinder) :
    c.carrier = CylinderCovering.Similarity.carrier (Subtype.val '' c.base) c.axis := by
  ext x
  constructor
  · rintro ⟨b, hb, s, rfl⟩
    exact ⟨b, ⟨b, hb, rfl⟩, s, rfl⟩
  · rintro ⟨b, ⟨b', hb', rfl⟩, s, rfl⟩
    exact ⟨b', hb', s, rfl⟩

lemma similarity_carrier (c : Cylinder) (t : Space) {r : ℝ} (hr : r ≠ 0)
    (L : Space ≃ₗᵢ[ℝ] Space) :
    (c.similarity t hr L).carrier = CylinderCovering.Similarity.map t r L '' c.carrier := by
  rw [carrier_eq_ambient, carrier_eq_ambient]
  change CylinderCovering.Similarity.carrier
    (Subtype.val '' (similarityPlaneMap c.axis c.unit_axis t hr L '' c.base)) (L c.axis) = _
  rw [similarityPlaneMap_image, CylinderCovering.Similarity.carrier_image _ _ _ hr L]

lemma similarity_area (c : Cylinder) (t : Space) {r : ℝ} (hr : r ≠ 0)
    (L : Space ≃ₗᵢ[ℝ] Space) :
    (c.similarity t hr L).area = r ^ 2 * c.area := by
  unfold area
  rw [← similarityPlane_area _ (c.similarity t hr L).unit_axis,
    ← similarityPlane_area _ c.unit_axis]
  change CylinderCovering.Similarity.area
    (Subtype.val '' (similarityPlaneMap c.axis c.unit_axis t hr L '' c.base)) = _
  rw [similarityPlaneMap_image, CylinderCovering.Similarity.area_transportedBase _ _ _ hr L]

lemma similarity_parallelogram {c : Cylinder} (hc : c.parallelogram)
    (t : Space) {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    (c.similarity t hr L).parallelogram :=
  hc.affineEquiv (similarityPlaneMap c.axis c.unit_axis t hr L)

lemma similarity_triangle {c : Cylinder} (hc : c.triangle)
    (t : Space) {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    (c.similarity t hr L).triangle :=
  hc.affineEquiv (similarityPlaneMap c.axis c.unit_axis t hr L)

lemma similarity_openBounded {c : Cylinder} (hc : c.openBounded)
    (t : Space) {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    (c.similarity t hr L).openBounded := by
  let f := similarityPlaneMap c.axis c.unit_axis t hr L
  have hf : Continuous f := f.toAffineMap.continuous_of_finiteDimensional
  have hopen : IsOpen (f '' c.base) :=
    f.toContinuousAffineEquiv.toHomeomorph.isOpenMap _ hc.1
  refine ⟨hopen, ?_, hopen.measurableSet⟩
  exact ((hc.2.1.isCompact_closure.image hf).isBounded).subset
    (image_mono subset_closure)

end Cylinder
lemma similarity_familySet {n : ℕ} (C : Fin n → Cylinder) (t : Space)
    {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    familySet (fun i => (C i).similarity t hr L) =
      CylinderCovering.Similarity.map t r L '' familySet C := by
  simp only [familySet, Cylinder.similarity_carrier, image_iUnion]

lemma similarity_familyArea {n : ℕ} (C : Fin n → Cylinder) (t : Space)
    {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    familyArea (fun i => (C i).similarity t hr L) = r ^ 2 * familyArea C := by
  simp only [familyArea, Cylinder.similarity_area, Finset.mul_sum]

lemma similarity_cover {n : ℕ} (C : Fin n → Cylinder) (K : Set Space)
    (hcover : K ⊆ familySet C) (t : Space)
    {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    CylinderCovering.Similarity.map t r L '' K ⊆
      familySet (fun i => (C i).similarity t hr L) := by
  rw [similarity_familySet]
  exact image_mono hcover

lemma similarity_relativeCost {n : ℕ} (C : Fin n → Cylinder) (K : Set Space)
    (t : Space) {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    (∑ i, ((C i).similarity t hr L).area /
      CylinderCovering.Similarity.shadowArea
        (CylinderCovering.Similarity.map t r L '' K) ((C i).similarity t hr L).axis) =
      ∑ i, (C i).area / CylinderCovering.Similarity.shadowArea K (C i).axis := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [Cylinder.similarity_area]
  change r ^ 2 * (C i).area /
    CylinderCovering.Similarity.shadowArea (CylinderCovering.Similarity.map t r L '' K)
      (L (C i).axis) = _
  rw [CylinderCovering.Similarity.shadowArea_map K t hr L]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hr)

lemma HasFiniteCover.parallelogram_similarity {K : Set Space} {A : ℝ}
    (h : HasFiniteCover Cylinder.parallelogram K A)
    (t : Space) {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    HasFiniteCover Cylinder.parallelogram (CylinderCovering.Similarity.map t r L '' K)
      (r ^ 2 * A) := by
  rcases h with ⟨n, C, hshape, hcover, hcost⟩
  refine ⟨n, fun i => (C i).similarity t hr L,
    fun i => Cylinder.similarity_parallelogram (hshape i) t hr L,
    similarity_cover C K hcover t hr L, ?_⟩
  rw [similarity_familyArea]
  exact mul_le_mul_of_nonneg_left hcost (sq_nonneg r)

lemma HasFiniteCover.openBounded_similarity {K : Set Space} {A : ℝ}
    (h : HasFiniteCover Cylinder.openBounded K A)
    (t : Space) {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    HasFiniteCover Cylinder.openBounded (CylinderCovering.Similarity.map t r L '' K)
      (r ^ 2 * A) := by
  rcases h with ⟨n, C, hshape, hcover, hcost⟩
  refine ⟨n, fun i => (C i).similarity t hr L,
    fun i => Cylinder.similarity_openBounded (hshape i) t hr L,
    similarity_cover C K hcover t hr L, ?_⟩
  rw [similarity_familyArea]
  exact mul_le_mul_of_nonneg_left hcost (sq_nonneg r)

lemma relativeCost_le_familyArea_div_minimum (K : Set Space)
    (hK : 0 < CylinderCovering.Similarity.minimumArea K)
    {n : ℕ} (C : Fin n → Cylinder) :
    (∑ i, (C i).area / CylinderCovering.Similarity.shadowArea K (C i).axis) ≤
      familyArea C / CylinderCovering.Similarity.minimumArea K := by
  unfold familyArea
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  exact div_le_div_of_nonneg_left ENNReal.toReal_nonneg hK
    (CylinderCovering.Similarity.minimumArea_le_shadowArea K (C i).unit_axis)

lemma relativeCost_lt_half_of_familyArea_lt (K : Set Space)
    (hK : 0 < CylinderCovering.Similarity.minimumArea K)
    {n : ℕ} (C : Fin n → Cylinder)
    (hcost : familyArea C < CylinderCovering.Similarity.minimumArea K / 2) :
    (∑ i, (C i).area / CylinderCovering.Similarity.shadowArea K (C i).axis) < 1 / 2 := by
  apply (relativeCost_le_familyArea_div_minimum K hK C).trans_lt
  apply (div_lt_iff₀ hK).mpr
  linarith only [hcost]

lemma similarity_strict_total {n : ℕ} (C : Fin n → Cylinder) (K : Set Space)
    (hcost : familyArea C < CylinderCovering.Similarity.minimumArea K / 2)
    (t : Space) {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    familyArea (fun i => (C i).similarity t hr L) <
      CylinderCovering.Similarity.minimumArea
        (CylinderCovering.Similarity.map t r L '' K) / 2 := by
  rw [similarity_familyArea, CylinderCovering.Similarity.minimumArea_map K t hr L]
  nlinarith [mul_lt_mul_of_pos_left hcost (sq_pos_of_ne_zero hr)]

end RuledApproximation

end

end OAI
