import OAI.Geometry.TriangularCovering.Basic

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering.Planar

abbrev Coord := Fin 2 → ℝ

def standard : Set Coord := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1}

def vertices : Fin 3 → Coord := ![0, ![1, 0], ![0, 1] ]

lemma standard_convex : Convex ℝ standard := by
  intro x hx y hy a b ha hb hab
  simp only [standard, mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  exact ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),
    add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1), by
      nlinarith [mul_le_mul_of_nonneg_left hx.2.2 ha,
        mul_le_mul_of_nonneg_left hy.2.2 hb]⟩

lemma standard_eq_convexHull : standard = convexHull ℝ (range vertices) := by
  apply le_antisymm
  · intro x hx
    refine mem_convexHull_of_exists_fintype
      (![1 - x 0 - x 1, x 0, x 1] : Fin 3 → ℝ) vertices ?_ ?_ ?_ ?_
    · intro i; fin_cases i <;> dsimp <;>
        linarith [hx.1, hx.2.1, hx.2.2]
    · simp [Fin.sum_univ_succ]
    · exact fun i => mem_range_self i
    · ext i; fin_cases i <;> simp [vertices, Fin.sum_univ_succ]
  · refine convexHull_min ?_ standard_convex
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> norm_num [standard, vertices]

lemma standard_compact : IsCompact standard := by
  rw [standard_eq_convexHull]
  exact (finite_range vertices).isCompact_convexHull ℝ

lemma closed_region_volume (f g : ℝ → ℝ) (s : Set ℝ)
    (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    (volume.prod volume) {p : ℝ × ℝ | p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1)} =
      (volume.prod volume) (regionBetween f g s) := by
  rw [Measure.prod_apply (measurableSet_region_between_cc hf hg hs),
    Measure.prod_apply (measurableSet_regionBetween hf hg hs)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp only [regionBetween, preimage_ofPred_eq, hx, true_and]
    change volume (Icc (f x) (g x)) = volume (Ioo (f x) (g x))
    rw [Real.volume_Icc, Real.volume_Ioo]
  · simp [regionBetween, hx]

lemma standard_volume : volume standard = ENNReal.ofReal (1 / 2 : ℝ) := by
  let s : Set (ℝ × ℝ) := {p | p.1 ∈ Icc 0 1 ∧ p.2 ∈ Icc 0 (1 - p.1)}
  have heq : standard = (MeasurableEquiv.piFinTwo fun _ : Fin 2 => ℝ) ⁻¹' s := by
    ext x
    simp only [standard, mem_ofPred_eq, mem_preimage, s, MeasurableEquiv.piFinTwo_apply,
      mem_Icc]
    constructor
    · rintro ⟨h0, h1, h2⟩; exact ⟨⟨h0, by linarith⟩, h1, by linarith⟩
    · rintro ⟨⟨h0, _⟩, h1, h2⟩; exact ⟨h0, h1, by linarith⟩
  rw [heq, volume_pi,
    (measurePreserving_piFinTwo (fun _ : Fin 2 => (volume : Measure ℝ))).measure_preimage_equiv]
  change (volume.prod volume) s = _
  rw [closed_region_volume (fun _ => 0) (fun x => 1-x) (Icc 0 1)
    measurable_const (by fun_prop) measurableSet_Icc]
  have hf : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 1) :=
    continuous_const.integrableOn_Icc
  have hg : IntegrableOn (fun x : ℝ => 1 - x) (Icc 0 1) :=
    (continuous_const.sub continuous_id).integrableOn_Icc
  rw [volume_regionBetween_eq_integral hf hg measurableSet_Icc
    (by intro x hx; linarith [hx.2])]
  congr 1
  simp only [Pi.sub_apply, sub_zero]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun x : ℝ => x)
    (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _), integral_id]
  norm_num

end TriangularCovering.Planar

namespace TriangularCovering

section Triangles
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

def triangle (a b c : E) : Set E := convexHull ℝ (range (![a, b, c] : Fin 3 → E))

def twoSpan (b c : E) : Planar.Coord →ₗ[ℝ] E :=
  (LinearMap.proj 0).smulRight b + (LinearMap.proj 1).smulRight c

@[simp] lemma twoSpan_apply (b c : E) (x : Planar.Coord) :
    twoSpan b c x = x 0 • b + x 1 • c := rfl

lemma triangle_image_linear (L : E →ₗ[ℝ] F) (a b c : E) :
    L '' triangle a b c = triangle (L a) (L b) (L c) := by
  rw [triangle, L.image_convexHull, triangle]
  congr 1
  rw [← range_comp]
  congr 1
  funext i; fin_cases i <;> rfl

lemma triangle_image_affine (L : E →ᵃ[ℝ] F) (a b c : E) :
    L '' triangle a b c = triangle (L a) (L b) (L c) := by
  rw [triangle, L.image_convexHull, triangle]
  congr 1
  rw [← range_comp]
  congr 1
  funext i; fin_cases i <;> rfl

lemma triangle_zero_image (b c : E) : triangle 0 b c = twoSpan b c '' Planar.standard := by
  rw [Planar.standard_eq_convexHull, (twoSpan b c).image_convexHull, triangle]
  congr 1
  rw [← range_comp]
  congr 1
  funext i; fin_cases i <;> simp [Planar.vertices, twoSpan]

lemma triangle_translate (a b c : E) :
    triangle a b c = (fun x => a + x) '' triangle 0 (b-a) (c-a) := by
  have h := triangle_image_affine (AffineEquiv.constVAdd ℝ E a).toAffineMap 0 (b-a) (c-a)
  simpa using h.symm

lemma mem_triangle_iff (a b c x : E) : x ∈ triangle a b c ↔
    ∃ r s : ℝ, 0 ≤ r ∧ 0 ≤ s ∧ r+s ≤ 1 ∧ x = a + r • (b-a) + s • (c-a) := by
  rw [triangle_translate, triangle_zero_image]
  constructor
  · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v 0, v 1, hv.1, hv.2.1, hv.2.2, by simp [add_assoc]⟩
  · rintro ⟨r, s, hr, hs, hrs, rfl⟩
    refine ⟨r • (b-a) + s • (c-a), ?_, by simp [add_assoc]⟩
    exact ⟨![r,s], ⟨hr, hs, hrs⟩, by simp⟩

end Triangles

namespace Planar

def wedge (b c : Coord) : ℝ := b 0 * c 1 - b 1 * c 0

lemma twoSpan_det (b c : Coord) : LinearMap.det (twoSpan b c) = wedge b c := by
  have h : twoSpan b c = Matrix.toLin' (!![b 0, c 0; b 1, c 1]) := by
    apply LinearMap.ext
    intro x
    funext i
    fin_cases i <;> simp [twoSpan_apply, Matrix.toLin'_apply, Matrix.vecHead, Matrix.vecTail, mul_comm]
    all_goals ring
  rw [h, LinearMap.det_toLin', Matrix.det_fin_two]
  simp [wedge, mul_comm]

lemma triangle_volume (a b c : Coord) :
    volume (triangle a b c) = ENNReal.ofReal (|wedge (b-a) (c-a)| / 2) := by
  rw [triangle_translate, image_add_left, measure_preimage_add,
    triangle_zero_image, volume.addHaar_image_linearMap, twoSpan_det, standard_volume,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring

end Planar
end TriangularCovering

namespace TriangularCovering

lemma measurePreserving_image {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → Y} (hm : MeasurePreserving f μ ν)
    (hf : MeasurableEmbedding f) (s : Set X) : ν (f '' s) = μ s := by
  rw [← hm.measure_preimage_emb hf, hf.injective.preimage_image]

section InnerPlane
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def planeCoord (basis : OrthonormalBasis (Fin 2) ℝ E) : E ≃L[ℝ] Planar.Coord :=
  basis.repr.toContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin 2) ℝ)

lemma planeCoord_measurePreserving (basis : OrthonormalBasis (Fin 2) ℝ E) :
    MeasurePreserving (planeCoord basis) volume volume :=
  (PiLp.volume_preserving_ofLp (Fin 2)).comp basis.measurePreserving_repr

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma planeCoord_gram (basis : OrthonormalBasis (Fin 2) ℝ E) (b c : E) :
    (Planar.wedge (planeCoord basis b) (planeCoord basis c)) ^ 2 =
      inner ℝ b b * inner ℝ c c - (inner ℝ b c)^2 := by
  rw [← basis.repr.inner_map_map b b, ← basis.repr.inner_map_map c c,
    ← basis.repr.inner_map_map b c]
  change (((basis.repr b).ofLp 0 * (basis.repr c).ofLp 1 -
    (basis.repr b).ofLp 1 * (basis.repr c).ofLp 0)^2) = _
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
  ring

lemma volume_triangle_basis (basis : OrthonormalBasis (Fin 2) ℝ E) (a b c : E) :
    volume (triangle a b c) = ENNReal.ofReal
      (Real.sqrt (inner ℝ (b-a) (b-a) * inner ℝ (c-a) (c-a) -
        (inner ℝ (b-a) (c-a))^2) / 2) := by
  rw [← measurePreserving_image (planeCoord_measurePreserving basis)
    (planeCoord basis).toHomeomorph.measurableEmbedding]
  change volume ((planeCoord basis).toLinearMap '' triangle a b c) = _
  rw [triangle_image_linear, Planar.triangle_volume]
  rw [← map_sub, ← map_sub, ← planeCoord_gram basis, Real.sqrt_sq_eq_abs]
  rfl

end InnerPlane
end TriangularCovering

namespace TriangularCovering

section SubspaceMeasure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

lemma subspace_triangle_measure (P : Submodule ℝ E) (hp : Module.finrank ℝ P = 2)
    (a b c : P) :
    Measure.euclideanHausdorffMeasure 2 (triangle (a : E) (b : E) (c : E)) =
      ENNReal.ofReal (Real.sqrt (inner ℝ (b-a) (b-a) * inner ℝ (c-a) (c-a) -
        (inner ℝ (b-a) (c-a)) ^ 2) / 2) := by
  change Measure.euclideanHausdorffMeasure 2
    (triangle (P.subtype a) (P.subtype b) (P.subtype c)) = _
  rw [← triangle_image_linear P.subtype a b c]
  change Measure.euclideanHausdorffMeasure 2 ((Subtype.val : P → E) '' triangle a b c) = _
  rw [isometry_subtype_coe.euclideanHausdorffMeasure_image]
  have hm : (Measure.euclideanHausdorffMeasure 2 : Measure P) = volume := by
    rw [← hp, InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  rw [hm]
  exact volume_triangle_basis ((stdOrthonormalBasis ℝ P).reindex (finCongr hp)) a b c

lemma perpendicular_triangle_measure (hrank : Module.finrank ℝ E = 3)
    (u a b c : E) (hu : u ≠ 0) (ha : inner ℝ u a = 0)
    (hb : inner ℝ u b = 0) (hc : inner ℝ u c = 0) :
    Measure.euclideanHausdorffMeasure 2 (triangle a b c) =
      ENNReal.ofReal (Real.sqrt (inner ℝ (b-a) (b-a) * inner ℝ (c-a) (c-a) -
        (inner ℝ (b-a) (c-a)) ^ 2) / 2) := by
  let P := (ℝ ∙ u)ᗮ
  have hp : Module.finrank ℝ P = 2 := by
    have h := (ℝ ∙ u).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton hu, hrank] at h
    change 1 + Module.finrank ℝ P = 3 at h
    omega
  have ha' : a ∈ P := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr ha
  have hb' : b ∈ P := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hb
  have hc' : c ∈ P := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hc
  exact subspace_triangle_measure P hp ⟨a,ha'⟩ ⟨b,hb'⟩ ⟨c,hc'⟩

end SubspaceMeasure
end TriangularCovering

end

end OAI
