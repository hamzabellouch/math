import OAI.Geometry.ProjectionVolume.Basic
import OAI.Geometry.ProjectionVolume.Translation
import OAI.Geometry.ProjectionVolume.Brightness
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

universe uι

open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

namespace Paper092

noncomputable def hyperplaneProjection {n : ℕ} (u v : Euclidean n) :
    normalHyperplane v →ₗ[ℝ] Euclidean n :=
  (normalHyperplane u).starProjection.toLinearMap.comp (normalHyperplane v).subtype

lemma normal_starProjection_unit {n : ℕ} (u x : Euclidean n) (hu : ‖u‖ = 1) :
    (normalHyperplane u).starProjection x = x - ⟪u, x⟫ • u := by
  simp only [normalHyperplane, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℝ hu]

lemma det_one_sub_outer {ι : Type uι} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) :
    (1 - Matrix.vecMulVec a a).det = 1 - ∑ i, a i ^ 2 := by
  rw [Matrix.vecMulVec_eq Unit,
    Matrix.det_one_sub_mul_comm, Matrix.det_unique]
  simp [Matrix.replicateRow_mul_replicateCol_apply, dotProduct, pow_two]
theorem hyperplaneProjection_normDet {n : ℕ} (u v : Euclidean n)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (hyperplaneProjection u v).normDet = |⟪u, v⟫| := by
  let b := stdOrthonormalBasis ℝ (normalHyperplane v)
  let a := fun i => ⟪u, (b i : Euclidean n)⟫
  have hgram : Matrix.gram ℝ (fun i => hyperplaneProjection u v (b i)) =
      1 - Matrix.vecMulVec a a := by
    ext i j
    change ⟪(normalHyperplane u).starProjection (b i),
      (normalHyperplane u).starProjection (b j)⟫ = _
    rw [normal_starProjection_unit _ _ hu, normal_starProjection_unit _ _ hu]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hu, one_pow, Matrix.sub_apply, Matrix.one_apply,
      Matrix.vecMulVec_apply]
    have hb : ⟪(b i : Euclidean n), (b j : Euclidean n)⟫ = if i = j then 1 else 0 :=
      b.inner_eq_ite i j
    rw [hb]
    dsimp [a]
    simp only [real_inner_comm (b i : Euclidean n) u]
    ring
  have hsum : (∑ i, a i ^ 2) = 1 - ⟪u, v⟫ ^ 2 := by
    have h := b.sum_sq_inner_left ((normalHyperplane v).orthogonalProjectionOnto u)
    simp only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right] at h
    change (∑ i, a i ^ 2) = ‖(normalHyperplane v).orthogonalProjectionOnto u‖ ^ 2 at h
    rw [h]
    change ‖(normalHyperplane v).starProjection u‖ ^ 2 = _
    rw [normal_starProjection_unit _ _ hv, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hu, one_pow]
    simp only [norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs]
    rw [real_inner_comm v u]
    ring
  have hsq := (hyperplaneProjection u v).normDet_sq_eq_det_gram b
  rw [hgram, det_one_sub_outer, hsum] at hsq
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hsq
  have hn := (hyperplaneProjection u v).normDet_nonneg
  have ha := abs_nonneg ⟪u, v⟫
  nlinarith [sq_abs ⟪u, v⟫]

theorem volume_project_hyperplane {n : ℕ} (u v : Euclidean n)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (S : Set (normalHyperplane v)) :
    (volume : Measure (normalHyperplane u))
      ((normalHyperplane u).orthogonalProjectionOnto ''
        ((fun x : normalHyperplane v => (x : Euclidean n)) '' S)) =
      ENNReal.ofReal |⟪u, v⟫| * (volume : Measure (normalHyperplane v)) S := by
  let f : normalHyperplane v →ₗ[ℝ] normalHyperplane u :=
    (normalHyperplane u).orthogonalProjectionOnto.toLinearMap.comp
      (normalHyperplane v).subtype
  have hf : f.normDet = (hyperplaneProjection u v).normDet := by
    have hp : ∀ x, hyperplaneProjection u v x ∈ normalHyperplane u := by
      intro x
      exact ((normalHyperplane u).orthogonalProjectionOnto (x : Euclidean n)).property
    have he : f = (hyperplaneProjection u v).codRestrict (normalHyperplane u) hp := by
      ext x
      rfl
    rw [he]
    exact LinearMap.normDet_codRestrict hp
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have hrank : Module.finrank ℝ (normalHyperplane v) =
      Module.finrank ℝ (normalHyperplane u) := by
    rw [normalHyperplane_finrank v hv0, normalHyperplane_finrank u hu0]
  have h := f.euclideanHausdorffMeasure_image_eq_normDet_mul_volume S
  rw [hrank, InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
    hf, hyperplaneProjection_normDet u v hu hv] at h
  have himage : f '' S = (normalHyperplane u).orthogonalProjectionOnto ''
      ((fun x : normalHyperplane v => (x : Euclidean n)) '' S) := by
    rw [Set.image_image]
    rfl
  rw [himage] at h
  exact h

theorem projectionVolume_of_subset_affine_hyperplane {n : ℕ} (u v : Euclidean n)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (c : ℝ) (S : Set (Euclidean n))
    (hS : ∀ x ∈ S, ⟪v, x⟫ = c) :
    projectionVolume S u = ENNReal.ofReal |⟪u, v⟫| * μHE[n - 1] S := by
  let T : Set (Euclidean n) := ((-c) • v) +ᵥ S
  have hT : T ⊆ (normalHyperplane v : Set (Euclidean n)) := by
    rintro x ⟨y, hy, rfl⟩
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    change ⟪v, (-c) • v + y⟫ = 0
    simp [inner_add_right, inner_smul_right, hv, hS y hy]
  let Q : Set (normalHyperplane v) := {x | (x : Euclidean n) ∈ T}
  have hQ : (fun x : normalHyperplane v => (x : Euclidean n)) '' Q = T := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hT hx⟩, hx, rfl⟩
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have hQV : (volume : Measure (normalHyperplane v)) Q = μHE[n - 1] S := by
    rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
      normalHyperplane_finrank v hv0]
    have h := (isometry_subtype_coe : Isometry
      (fun x : normalHyperplane v => (x : Euclidean n))).euclideanHausdorffMeasure_image
      (d := n - 1) Q
    have hQ' : (Subtype.val : normalHyperplane v → Euclidean n) '' Q = T := hQ
    calc
      (μHE[n - 1] : Measure (normalHyperplane v)) Q =
          (μHE[n - 1] : Measure (Euclidean n)) (Subtype.val '' Q) := h.symm
      _ = (μHE[n - 1] : Measure (Euclidean n)) T :=
        congrArg (fun A : Set (Euclidean n) => (μHE[n - 1] : Measure (Euclidean n)) A) hQ'
      _ = (μHE[n - 1] : Measure (Euclidean n)) S :=
        measure_vadd (μHE[n - 1] : Measure (Euclidean n)) ((-c) • v) S
  have h := volume_project_hyperplane u v hu hv Q
  rw [hQ, hQV] at h
  change projectionVolume T u = _ at h
  simpa only [T, projectionVolume_vadd] using h

theorem brightness_of_subset_affine_hyperplane {n : ℕ} (u v : Euclidean n)
    (hv : ‖v‖ = 1) (c : ℝ) (S : Set (Euclidean n))
    (hS : ∀ x ∈ S, ⟪v, x⟫ = c) :
    brightness S u = |⟪u, v⟫| * (μHE[n - 1] S).toReal := by
  by_cases hu : u = 0
  · simp [hu, brightness]
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hunit : ‖‖u‖⁻¹ • u‖ = 1 := by
    simp [norm_smul, hn.ne']
  have h := projectionVolume_of_subset_affine_hyperplane
    (‖u‖⁻¹ • u) v hunit hv c S hS
  rw [projectionVolume_smul S u (inv_ne_zero hn.ne')] at h
  rw [brightness, h, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  simp only [real_inner_smul_left, abs_mul, abs_inv, abs_of_pos hn]
  field_simp

end Paper092

end OAI
