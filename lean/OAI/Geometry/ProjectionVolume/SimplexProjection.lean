import OAI.Geometry.ProjectionVolume.SimplexGeometry
import OAI.Geometry.ProjectionVolume.SimplexCoordinates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

namespace OAI

universe uι

open Set MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace Paper092

theorem projection_eq_iff_parallel {d : ℕ} (u x z : Euclidean d) :
    (normalHyperplane u).orthogonalProjectionOnto x =
      (normalHyperplane u).orthogonalProjectionOnto z ↔
        ∃ t : ℝ, x = z + t • u := by
  rw [← sub_eq_zero, ← map_sub, Submodule.orthogonalProjectionOnto_eq_zero_iff]
  rw [normalHyperplane, Submodule.orthogonal_orthogonal, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [ht]
    abel
  · rintro ⟨t, rfl⟩
    exact ⟨t, by abel⟩

theorem mem_projection_iff_line_meets {d : ℕ} (u : Euclidean d)
    (K : Set (Euclidean d)) (y : normalHyperplane u) :
    y ∈ (normalHyperplane u).orthogonalProjectionOnto '' K ↔
      ∃ t : ℝ, (y : Euclidean d) + t • u ∈ K := by
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hp : (normalHyperplane u).orthogonalProjectionOnto x =
        (normalHyperplane u).orthogonalProjectionOnto (y : Euclidean d) := by
      simpa using hxy
    obtain ⟨t, rfl⟩ := (projection_eq_iff_parallel u x y).mp hp
    exact ⟨t, hx⟩
  · rintro ⟨t, ht⟩
    refine ⟨(y : Euclidean d) + t • u, ht, ?_⟩
    have hp := (projection_eq_iff_parallel u ((y : Euclidean d) + t • u) y).mpr ⟨t, rfl⟩
    simpa using hp

theorem exists_step_to_boundary {ι : Type uι} [Fintype ι] (q v : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hv : ∃ i, v i < 0) :
    ∃ t : ℝ, 0 ≤ t ∧ (∀ i, 0 ≤ q i + t * v i) ∧
      ∃ i, v i < 0 ∧ q i + t * v i = 0 := by
  classical
  let s := Finset.univ.filter (fun i => v i < 0)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hv
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image s (fun j => q j / (-v j)) hs
  have hi0 : v i < 0 := (Finset.mem_filter.mp hi).2
  have hneg : 0 < -v i := neg_pos.mpr hi0
  have ht : 0 ≤ q i / (-v i) := div_nonneg (hq i) hneg.le
  have heq : q i + q i / (-v i) * v i = 0 := by
    have hmul := div_mul_cancel₀ (q i) (ne_of_gt hneg)
    linarith
  refine ⟨q i / (-v i), ht, ?_, i, hi0, heq⟩
  intro j
  by_cases hj : v j < 0
  · have hjmem : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
    have hle := (le_div_iff₀ (neg_pos.mpr hj)).mp (hmin j hjmem)
    linarith
  · exact add_nonneg (hq j) (mul_nonneg ht (le_of_not_gt hj))

def simplexCoordinates {d : ℕ} (x : Euclidean d) : Option (Fin d) → ℝ
  | none => 1 - ∑ i, x i
  | some i => x i

def simplexVelocity {d : ℕ} (u : Euclidean d) : Option (Fin d) → ℝ
  | none => -∑ i, u i
  | some i => u i

theorem simplexCoordinates_nonneg_iff {d : ℕ} (x : Euclidean d) :
    (∀ a, 0 ≤ simplexCoordinates x a) ↔
      (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1 := by
  constructor
  · intro h
    exact ⟨fun i => h (some i), sub_nonneg.mp (h none)⟩
  · rintro ⟨h0, h1⟩ a
    cases a with
    | none => exact sub_nonneg.mpr h1
    | some i => exact h0 i

theorem simplexCoordinates_add_smul {d : ℕ} (x u : Euclidean d) (t : ℝ)
    (a : Option (Fin d)) :
    simplexCoordinates (x + t • u) a =
      simplexCoordinates x a + t * simplexVelocity u a := by
  cases a with
  | none =>
    simp only [simplexCoordinates, simplexVelocity, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  | some i => rfl

theorem simplexVelocity_neg_exists {d : ℕ} (u : Euclidean d) (hu : u ≠ 0) :
    ∃ a, simplexVelocity u a < 0 := by
  by_contra h
  push Not at h
  have h0 : ∀ i, 0 ≤ u i := fun i => h (some i)
  have hsum : ∑ i, u i ≤ 0 := by
    simpa only [simplexVelocity, neg_nonneg] using h none
  apply hu
  ext i
  apply le_antisymm
  · exact (Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)).trans hsum
  · exact h0 i

theorem exists_simplex_front_point {d : ℕ} (x u : Euclidean d) (hu : u ≠ 0)
    (hx : ∀ a, 0 ≤ simplexCoordinates x a) :
    ∃ t : ℝ, 0 ≤ t ∧ (∀ a, 0 ≤ simplexCoordinates (x + t • u) a) ∧
      ∃ a, simplexVelocity u a < 0 ∧ simplexCoordinates (x + t • u) a = 0 := by
  obtain ⟨t, ht, hq, a, ha, hqa⟩ :=
    exists_step_to_boundary (simplexCoordinates x) (simplexVelocity u) hx
      (simplexVelocity_neg_exists u hu)
  refine ⟨t, ht, ?_, a, ha, ?_⟩
  · simpa only [simplexCoordinates_add_smul] using hq
  · simpa only [simplexCoordinates_add_smul] using hqa

theorem projection_injective_on_simplex_front {d : ℕ} (u x z : Euclidean d)
    (hx : ∀ a, 0 ≤ simplexCoordinates x a) (hz : ∀ a, 0 ≤ simplexCoordinates z a)
    (hxf : ∃ a, simplexVelocity u a < 0 ∧ simplexCoordinates x a = 0)
    (hzf : ∃ a, simplexVelocity u a < 0 ∧ simplexCoordinates z a = 0)
    (hp : (normalHyperplane u).orthogonalProjectionOnto x =
      (normalHyperplane u).orthogonalProjectionOnto z) : x = z := by
  obtain ⟨t, rfl⟩ := (projection_eq_iff_parallel u x z).mp hp
  obtain ⟨a, ha, hxa⟩ := hxf
  obtain ⟨b, hb, hzb⟩ := hzf
  rw [simplexCoordinates_add_smul] at hxa
  have ht0 : 0 ≤ t := by
    by_contra ht
    have hprod := mul_pos_of_neg_of_neg (lt_of_not_ge ht) ha
    linarith [hz a]
  have ht1 : t ≤ 0 := by
    by_contra ht
    have hprod := mul_neg_of_pos_of_neg (lt_of_not_ge ht) hb
    have hxb := hx b
    rw [simplexCoordinates_add_smul, hzb] at hxb
    linarith
  simp [le_antisymm ht1 ht0]

theorem mem_standardSimplex_iff_coordinates {d : ℕ} (x : Euclidean d) :
    x ∈ standardSimplex d ↔ ∀ a, 0 ≤ simplexCoordinates x a :=
  (mem_standardSimplex_iff x).trans (simplexCoordinates_nonneg_iff x).symm

theorem mem_simplex_projection_iff {d : ℕ} (u : Euclidean d) (y : normalHyperplane u) :
    y ∈ (normalHyperplane u).orthogonalProjectionOnto '' standardSimplex d ↔
      ∃ t : ℝ, (∀ i, 0 ≤ y.val i + t * u i) ∧
        (∑ i, y.val i) + t * (∑ i, u i) ≤ 1 := by
  rw [mem_projection_iff_line_meets]
  simp only [mem_standardSimplex_iff, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum]

def simplexFacet (d : ℕ) (a : Option (Fin d)) : Set (Euclidean d) :=
  {x | x ∈ standardSimplex d ∧ simplexCoordinates x a = 0}

theorem simplex_projection_eq_front_cover {d : ℕ} (u : Euclidean d) (hu : u ≠ 0) :
    (normalHyperplane u).orthogonalProjectionOnto '' standardSimplex d =
      ⋃ a : {a : Option (Fin d) // simplexVelocity u a < 0},
        (normalHyperplane u).orthogonalProjectionOnto '' simplexFacet d a.val := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, _, hq, a, ha, hqa⟩ :=
      exists_simplex_front_point x u hu ((mem_standardSimplex_iff_coordinates x).mp hx)
    refine mem_iUnion.mpr ⟨⟨a, ha⟩, x + t • u, ?_, ?_⟩
    · exact ⟨(mem_standardSimplex_iff_coordinates _).mpr hq, hqa⟩
    · exact (projection_eq_iff_parallel u (x + t • u) x).mpr ⟨t, rfl⟩
  · intro hy
    obtain ⟨a, x, hx, hpx⟩ := mem_iUnion.mp hy
    exact ⟨x, hx.1, hpx⟩

theorem front_facets_projection_inter_eq {d : ℕ} (u : Euclidean d)
    (a b : Option (Fin d)) (ha : simplexVelocity u a < 0)
    (hb : simplexVelocity u b < 0) :
    ((normalHyperplane u).orthogonalProjectionOnto '' simplexFacet d a) ∩
      ((normalHyperplane u).orthogonalProjectionOnto '' simplexFacet d b) =
        (normalHyperplane u).orthogonalProjectionOnto '' (simplexFacet d a ∩ simplexFacet d b) := by
  apply le_antisymm
  · rintro y ⟨⟨x, hx, hpx⟩, ⟨z, hz, hpz⟩⟩
    have heq : x = z := projection_injective_on_simplex_front u x z
      ((mem_standardSimplex_iff_coordinates x).mp hx.1)
      ((mem_standardSimplex_iff_coordinates z).mp hz.1)
      ⟨a, ha, hx.2⟩ ⟨b, hb, hz.2⟩ (hpx.trans hpz.symm)
    subst z
    exact ⟨x, ⟨hx, hz⟩, hpx⟩
  · exact image_inter_subset _ _ _

def simplexCoordinateAffine {d : ℕ} : Option (Fin d) → Euclidean d →ᵃ[ℝ] ℝ
  | none => AffineMap.const ℝ (Euclidean d) 1 -
      (∑ i : Fin d, (PiLp.projₗ 2 (fun _ : Fin d => ℝ) i : Euclidean d →ₗ[ℝ] ℝ)).toAffineMap
  | some i => (PiLp.projₗ 2 (fun _ : Fin d => ℝ) i : Euclidean d →ₗ[ℝ] ℝ).toAffineMap

theorem simplexCoordinateAffine_apply {d : ℕ} (a : Option (Fin d)) (x : Euclidean d) :
    simplexCoordinateAffine a x = simplexCoordinates x a := by
  cases a <;> simp [simplexCoordinateAffine, simplexCoordinates]

def simplexVertex {d : ℕ} : Option (Fin d) → Euclidean d
  | none => 0
  | some i => EuclideanSpace.single i 1

theorem simplexCoordinates_vertex {d : ℕ} (a b : Option (Fin d)) :
    simplexCoordinates (simplexVertex a) b = if a = b then 1 else 0 := by
  cases a <;> cases b <;> simp [simplexVertex, simplexCoordinates, PiLp.single_apply, eq_comm]

theorem facet_seam_projection_invariant {d : ℕ} (u x : Euclidean d)
    (a b : Option (Fin d)) :
    simplexVelocity u b * simplexCoordinates
        ((normalHyperplane u).orthogonalProjectionOnto x : Euclidean d) a -
      simplexVelocity u a * simplexCoordinates
        ((normalHyperplane u).orthogonalProjectionOnto x : Euclidean d) b =
      simplexVelocity u b * simplexCoordinates x a -
        simplexVelocity u a * simplexCoordinates x b := by
  obtain ⟨t, ht⟩ := (projection_eq_iff_parallel u x
    ((normalHyperplane u).orthogonalProjectionOnto x)).mp
      ((normalHyperplane u).orthogonalProjectionOnto_mem_subspace_eq_self
        ((normalHyperplane u).orthogonalProjectionOnto x)).symm
  conv_rhs => rw [ht, simplexCoordinates_add_smul, simplexCoordinates_add_smul]
  ring

theorem projected_facet_seam_null {d : ℕ} (u : Euclidean d) (a b : Option (Fin d))
    (hab : a ≠ b) (hb : simplexVelocity u b ≠ 0) :
    volume {y : normalHyperplane u |
      simplexVelocity u b * simplexCoordinates y.val a -
        simplexVelocity u a * simplexCoordinates y.val b = 0} = 0 := by
  let f : normalHyperplane u →ᵃ[ℝ] ℝ :=
    simplexVelocity u b • ((simplexCoordinateAffine a).comp
      (normalHyperplane u).subtype.toAffineMap) -
    simplexVelocity u a • ((simplexCoordinateAffine b).comp
      (normalHyperplane u).subtype.toAffineMap)
  let S : AffineSubspace ℝ (normalHyperplane u) :=
    (affineSpan ℝ ({0} : Set ℝ)).comap f
  have hmem (y : normalHyperplane u) : y ∈ S ↔
      simplexVelocity u b * simplexCoordinates y.val a -
        simplexVelocity u a * simplexCoordinates y.val b = 0 := by
    simp [S, f, simplexCoordinateAffine_apply, smul_eq_mul]
  have hproper : S ≠ ⊤ := by
    intro htop
    have hy : (normalHyperplane u).orthogonalProjectionOnto (simplexVertex a) ∈ S := by
      rw [htop]
      exact AffineSubspace.mem_top ℝ _ _
    have hz := (hmem _).mp hy
    rw [facet_seam_projection_invariant] at hz
    simp only [simplexCoordinates_vertex, ite_true, ite_eq_right hab, mul_one, mul_zero,
      sub_zero] at hz
    exact hb hz
  have hset : {y : normalHyperplane u |
      simplexVelocity u b * simplexCoordinates y.val a -
        simplexVelocity u a * simplexCoordinates y.val b = 0} = S := by
    ext y
    exact (hmem y).symm
  rw [hset]
  exact Measure.addHaar_affineSubspace volume S hproper

theorem projected_front_facets_aedisjoint {d : ℕ} (u : Euclidean d)
    (a b : Option (Fin d)) (hab : a ≠ b)
    (ha : simplexVelocity u a < 0) (hb : simplexVelocity u b < 0) :
    AEDisjoint volume
      ((normalHyperplane u).orthogonalProjectionOnto '' simplexFacet d a)
      ((normalHyperplane u).orthogonalProjectionOnto '' simplexFacet d b) := by
  rw [AEDisjoint, front_facets_projection_inter_eq u a b ha hb]
  apply measure_mono_null _ (projected_facet_seam_null u a b hab (ne_of_lt hb))
  rintro y ⟨x, hx, rfl⟩
  change simplexVelocity u b * simplexCoordinates
      ((normalHyperplane u).orthogonalProjectionOnto x : Euclidean d) a -
    simplexVelocity u a * simplexCoordinates
      ((normalHyperplane u).orthogonalProjectionOnto x : Euclidean d) b = 0
  rw [facet_seam_projection_invariant, hx.1.2, hx.2.2]
  simp

theorem simplexFacet_isCompact (d : ℕ) (a : Option (Fin d)) :
    IsCompact (simplexFacet d a) := by
  have hfun : (fun x : Euclidean d => simplexCoordinates x a) = simplexCoordinateAffine a := by
    funext x
    exact (simplexCoordinateAffine_apply a x).symm
  have hc : Continuous (fun x : Euclidean d => simplexCoordinates x a) := by
    rw [hfun]
    exact (simplexCoordinateAffine a).continuous_of_finiteDimensional
  exact (standardSimplex_isCompact d).inter_right (isClosed_eq hc continuous_const)

theorem projected_simplexFacet_isCompact {d : ℕ} (u : Euclidean d) (a : Option (Fin d)) :
    IsCompact ((normalHyperplane u).orthogonalProjectionOnto '' simplexFacet d a) :=
  (simplexFacet_isCompact d a).image (normalHyperplane u).orthogonalProjectionOnto.continuous

theorem projectionVolume_simplex_eq_front_sum {d : ℕ} (u : Euclidean d) (hu : u ≠ 0) :
    projectionVolume (standardSimplex d) u =
      ∑ a : {a : Option (Fin d) // simplexVelocity u a < 0},
        volume ((normalHyperplane u).orthogonalProjectionOnto '' simplexFacet d a.val) := by
  unfold projectionVolume
  rw [simplex_projection_eq_front_cover u hu]
  have hd : Pairwise (fun a b : {a : Option (Fin d) // simplexVelocity u a < 0} =>
      AEDisjoint volume
        ((normalHyperplane u).orthogonalProjectionOnto '' simplexFacet d a.val)
        ((normalHyperplane u).orthogonalProjectionOnto '' simplexFacet d b.val)) := by
    intro a b hab
    exact projected_front_facets_aedisjoint u a.val b.val (Subtype.coe_injective.ne hab)
      a.property b.property
  rw [measure_iUnion₀ hd (fun a =>
    (projected_simplexFacet_isCompact u a.val).measurableSet.nullMeasurableSet)]
  exact tsum_fintype _

theorem brightness_simplex_eq_front_sum {d : ℕ} (u : Euclidean d) (hu : u ≠ 0) :
    brightness (standardSimplex d) u = ‖u‖ *
      ∑ a : {a : Option (Fin d) // simplexVelocity u a < 0},
        (volume ((normalHyperplane u).orthogonalProjectionOnto '' simplexFacet d a.val)).toReal := by
  unfold brightness
  rw [projectionVolume_simplex_eq_front_sum u hu, ENNReal.toReal_sum]
  intro a _
  exact (projected_simplexFacet_isCompact u a.val).measure_lt_top.ne

end Paper092

end

end OAI
