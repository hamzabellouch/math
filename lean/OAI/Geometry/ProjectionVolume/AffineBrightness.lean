import OAI.Geometry.ProjectionVolume.Basic
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

namespace OAI

universe uι

open Set MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace Paper092

private def normalFrameVector {n : ℕ} {ι : Type uι} [Fintype ι]
    (u : Euclidean n) (b : OrthonormalBasis ι ℝ (normalHyperplane u)) :
    Unit ⊕ ι → Euclidean n
  | .inl _ => ‖u‖⁻¹ • u
  | .inr i => b i

private theorem normalFrameVector_orthonormal {n : ℕ} {ι : Type uι} [Fintype ι]
    (u : Euclidean n) (hu : u ≠ 0)
    (b : OrthonormalBasis ι ℝ (normalHyperplane u)) :
    Orthonormal ℝ (normalFrameVector u b) := by
  classical
  have hn : ‖‖u‖⁻¹ • u‖ = 1 := by simp [norm_smul, hu]
  have hb (i : ι) : ⟪u, (b i : Euclidean n)⟫ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b i).property
  rw [orthonormal_iff_ite]
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · simp [normalFrameVector, hn]
  · simp [normalFrameVector, real_inner_smul_left, hb]
  · have hbi : ⟪(b i : Euclidean n), u⟫ = 0 := by rw [real_inner_comm, hb]
    simp [normalFrameVector, real_inner_smul_right, hbi]
  · simpa only [normalFrameVector, Sum.inr.injEq, Submodule.coe_inner] using b.inner_eq_ite i j

private def normalFrame {n : ℕ} {ι : Type uι} [Fintype ι]
    (u : Euclidean n) (hu : u ≠ 0)
    (b : OrthonormalBasis ι ℝ (normalHyperplane u)) :
    OrthonormalBasis (Unit ⊕ ι) ℝ (Euclidean n) :=
  OrthonormalBasis.mk (normalFrameVector_orthonormal u hu b)
    ((normalFrameVector_orthonormal u hu b).linearIndependent.span_eq_top_of_card_eq_finrank'
      (by
        have h := (Submodule.span ℝ ({u} : Set (Euclidean n))).finrank_add_finrank_orthogonal
        rw [finrank_span_singleton hu] at h
        change 1 + Module.finrank ℝ (normalHyperplane u) = _ at h
        rw [Module.finrank_eq_card_basis b.toBasis] at h
        simpa only [Fintype.card_sum, Fintype.card_unique] using h)).ge

@[simp] private theorem normalFrame_inl {n : ℕ} {ι : Type uι} [Fintype ι]
    (u : Euclidean n) (hu : u ≠ 0)
    (b : OrthonormalBasis ι ℝ (normalHyperplane u)) (i : Unit) :
    normalFrame u hu b (.inl i) = ‖u‖⁻¹ • u := by
  simp [normalFrame, normalFrameVector]

@[simp] private theorem normalFrame_inr {n : ℕ} {ι : Type uι} [Fintype ι]
    (u : Euclidean n) (hu : u ≠ 0)
    (b : OrthonormalBasis ι ℝ (normalHyperplane u)) (i : ι) :
    normalFrame u hu b (.inr i) = (b i : Euclidean n) := by
  simp [normalFrame, normalFrameVector]

def projectionTransport {n : ℕ} (L : Euclidean n ≃ₗ[ℝ] Euclidean n) (u : Euclidean n) :
    normalHyperplane (L.symm u) →ₗ[ℝ] normalHyperplane u :=
  (normalHyperplane u).orthogonalProjectionOnto.toLinearMap ∘ₗ
    L.toLinearMap ∘ₗ (normalHyperplane (L.symm u)).subtype

private theorem projectionTransport_matrix {n : ℕ} {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (L : Euclidean n ≃ₗ[ℝ] Euclidean n) (u : Euclidean n) (hu : u ≠ 0)
    (hv : L.symm u ≠ 0)
    (bv : OrthonormalBasis ι ℝ (normalHyperplane (L.symm u)))
    (bu : OrthonormalBasis ι ℝ (normalHyperplane u)) :
    L.toLinearMap.toMatrix (normalFrame (L.symm u) hv bv).toBasis
      (normalFrame u hu bu).toBasis =
      Matrix.fromBlocks (Matrix.of (fun _ _ : Unit => ‖u‖ / ‖L.symm u‖))
        (Matrix.of (fun (_ : Unit) j => ⟪‖u‖⁻¹ • u, L (bv j)⟫)) 0
        ((projectionTransport L u).toMatrix bv.toBasis bu.toBasis) := by
  ext i j
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · simp only [normalFrame_inl]
    change ⟪‖u‖⁻¹ • u, L (‖L.symm u‖⁻¹ • L.symm u)⟫ = ‖u‖ / ‖L.symm u‖
    rw [map_smul, L.apply_symm_apply, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    field_simp
  · simp only [normalFrame_inl, normalFrame_inr]
    rfl
  · have hbi : ⟪(bu i : Euclidean n), u⟫ = 0 := by
      rw [real_inner_comm]
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (bu i).property
    simp only [normalFrame_inr, normalFrame_inl]
    change ⟪(bu i : Euclidean n), L (‖L.symm u‖⁻¹ • L.symm u)⟫ = 0
    rw [map_smul, L.apply_symm_apply, real_inner_smul_right, hbi, mul_zero]
  · simp only [normalFrame_inr]
    change ⟪(bu i : Euclidean n), L (bv j)⟫ =
      ((projectionTransport L u).toMatrix bv.toBasis bu.toBasis) i j
    rw [LinearMap.toMatrix_apply]
    rw [bu.coe_toBasis_repr_apply, bu.repr_apply_apply]
    change ⟪(bu i : Euclidean n), L (bv j)⟫ =
      ⟪bu i, (normalHyperplane u).orthogonalProjectionOnto (L (bv j))⟫
    exact (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left _ _).symm

theorem projectionTransport_normDet {n : ℕ}
    (L : Euclidean n ≃ₗ[ℝ] Euclidean n) (u : Euclidean n) (hu : u ≠ 0) :
    (projectionTransport L u).normDet =
      |L.toLinearMap.det| * ‖L.symm u‖ / ‖u‖ := by
  have hv : L.symm u ≠ 0 := by simpa using hu
  let bv := (stdOrthonormalBasis ℝ (normalHyperplane (L.symm u))).reindex
    (finCongr (normalHyperplane_finrank (L.symm u) hv))
  let bu := (stdOrthonormalBasis ℝ (normalHyperplane u)).reindex
    (finCongr (normalHyperplane_finrank u hu))
  have hL : |L.toLinearMap.det| =
      |(L.toLinearMap.toMatrix (normalFrame (L.symm u) hv bv).toBasis
        (normalFrame u hu bu).toBasis).det| := by
    rw [← L.toLinearMap.normDet_eq_abs_det]
    simpa only [Real.norm_eq_abs] using
      L.toLinearMap.normDet_eq_norm_det_toMatrix
        (normalFrame (L.symm u) hv bv) (normalFrame u hu bu)
  rw [projectionTransport_matrix L u hu hv bv bu,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique, Matrix.of_apply, abs_mul,
    abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _))] at hL
  have hA := (projectionTransport L u).normDet_eq_norm_det_toMatrix bv bu
  rw [Real.norm_eq_abs] at hA
  rw [← hA] at hL
  rw [hL]
  field_simp

theorem projectionTransport_project {n : ℕ}
    (L : Euclidean n ≃ₗ[ℝ] Euclidean n) (u x : Euclidean n) :
    projectionTransport L u ((normalHyperplane (L.symm u)).orthogonalProjectionOnto x) =
      (normalHyperplane u).orthogonalProjectionOnto (L x) := by
  have hmem := (normalHyperplane (L.symm u)).sub_starProjection_mem_orthogonal x
  have hspan : (normalHyperplane (L.symm u))ᗮ =
      Submodule.span ℝ ({L.symm u} : Set (Euclidean n)) := by
    simp [normalHyperplane]
  rw [hspan] at hmem
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
  have huorth : L (x - (normalHyperplane (L.symm u)).starProjection x) ∈
      (normalHyperplane u)ᗮ := by
    rw [← ht, map_smul, L.apply_symm_apply]
    simpa only [normalHyperplane, Submodule.orthogonal_orthogonal] using
      (Submodule.span ℝ ({u} : Set (Euclidean n))).smul_mem t
        (Submodule.mem_span_singleton_self u)
  have hz := (normalHyperplane u).orthogonalProjectionOnto_apply_of_mem_orthogonal huorth
  rw [map_sub, map_sub] at hz
  exact (sub_eq_zero.mp hz).symm

theorem projection_image_linearEquiv {n : ℕ}
    (L : Euclidean n ≃ₗ[ℝ] Euclidean n) (K : Set (Euclidean n)) (u : Euclidean n) :
    (normalHyperplane u).orthogonalProjectionOnto '' (L '' K) =
      projectionTransport L u ''
        ((normalHyperplane (L.symm u)).orthogonalProjectionOnto '' K) := by
  simp only [Set.image_image, projectionTransport_project]

theorem projectionVolume_linearEquiv_image {n : ℕ}
    (L : Euclidean n ≃ₗ[ℝ] Euclidean n) (K : Set (Euclidean n))
    (u : Euclidean n) (hu : u ≠ 0) :
    projectionVolume (L '' K) u =
      ENNReal.ofReal (|L.toLinearMap.det| * ‖L.symm u‖ / ‖u‖) *
        projectionVolume K (L.symm u) := by
  have hv : L.symm u ≠ 0 := by simpa using hu
  have hrank : Module.finrank ℝ (normalHyperplane (L.symm u)) =
      Module.finrank ℝ (normalHyperplane u) := by
    rw [normalHyperplane_finrank (L.symm u) hv, normalHyperplane_finrank u hu]
  have h := (projectionTransport L u).euclideanHausdorffMeasure_image_eq_normDet_mul_volume
    ((normalHyperplane (L.symm u)).orthogonalProjectionOnto '' K)
  rw [hrank, InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
    projectionTransport_normDet L u hu] at h
  simpa only [projectionVolume, projection_image_linearEquiv] using h

theorem brightness_linearEquiv_image {n : ℕ}
    (L : Euclidean n ≃ₗ[ℝ] Euclidean n) (K : Set (Euclidean n)) (u : Euclidean n) :
    brightness (L '' K) u = |L.toLinearMap.det| * brightness K (L.symm u) := by
  by_cases hu : u = 0
  · simp [hu, brightness]
  have hn : 0 ≤ |L.toLinearMap.det| * ‖L.symm u‖ / ‖u‖ :=
    div_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  rw [brightness, projectionVolume_linearEquiv_image L K u hu,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hn, brightness]
  field_simp

end Paper092

end

end OAI
