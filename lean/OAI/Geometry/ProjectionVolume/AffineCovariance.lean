import OAI.Geometry.ProjectionVolume.AffineBrightness
import OAI.Geometry.ProjectionVolume.Translation
import OAI.Geometry.ProjectionVolume.SimplexValue
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

namespace Paper092

theorem det_adjoint {n : ℕ} (A : Euclidean n →ₗ[ℝ] Euclidean n) :
    A.adjoint.det = A.det := by
  let b := stdOrthonormalBasis ℝ (Euclidean n)
  rw [← LinearMap.det_toMatrix b.toBasis A.adjoint, LinearMap.toMatrix_adjoint,
    Matrix.det_conjTranspose, LinearMap.det_toMatrix]
  simp

theorem projectionBody_linearEquiv_image {n : ℕ}
    (L : Euclidean n ≃ₗ[ℝ] Euclidean n) (K : Set (Euclidean n)) :
    projectionBody (L '' K) =
      (|L.toLinearMap.det| • L.symm.toLinearMap.adjoint) '' projectionBody K := by
  have hb := brightness_linearEquiv_image L K
  let c := |L.toLinearMap.det|
  have hc : 0 < c := abs_pos.mpr L.isUnit_det'.ne_zero
  ext y
  constructor
  · intro hy
    let z := c⁻¹ • L.toLinearMap.adjoint y
    refine ⟨z, ?_, ?_⟩
    · intro u
      have h := hy (L u)
      rw [hb, L.symm_apply_apply] at h
      change ⟪u, c⁻¹ • L.toLinearMap.adjoint y⟫ ≤ brightness K u
      rw [inner_smul_right, LinearMap.adjoint_inner_right]
      calc
        c⁻¹ * ⟪L u, y⟫ ≤ c⁻¹ * (c * brightness K u) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hc.le)
        _ = brightness K u := by field_simp
    · change c • L.symm.toLinearMap.adjoint z = y
      have hcancel : L.symm.toLinearMap.adjoint (L.toLinearMap.adjoint y) = y := by
        change (L.symm.toLinearMap.adjoint.comp L.toLinearMap.adjoint) y = y
        rw [← LinearMap.adjoint_comp]
        simp
      simp [z, map_smul, hcancel, smul_smul, hc.ne']
  · rintro ⟨z, hz, rfl⟩ u
    change ⟪u, c • L.symm.toLinearMap.adjoint z⟫ ≤ _
    rw [inner_smul_right, LinearMap.adjoint_inner_right, hb]
    exact mul_le_mul_of_nonneg_left (hz (L.symm u)) hc.le

theorem det_projectionBody_transform {n : ℕ} (hn : 0 < n)
    (L : Euclidean n ≃ₗ[ℝ] Euclidean n) :
    |(|L.toLinearMap.det| • L.symm.toLinearMap.adjoint).det| =
      |L.toLinearMap.det| ^ (n - 1) := by
  rw [LinearMap.det_smul, det_adjoint, LinearEquiv.det_coe_symm,
    finrank_euclideanSpace_fin, abs_mul, abs_pow, abs_abs, abs_inv]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  simp [pow_succ, L.isUnit_det'.ne_zero]

theorem normalizedProjectionVolume_linearEquiv_image {n : ℕ}
    (hn : 0 < n) (L : Euclidean n ≃ₗ[ℝ] Euclidean n) (K : Set (Euclidean n)) :
    normalizedProjectionVolume (L '' K) = normalizedProjectionVolume K := by
  have hc : |L.toLinearMap.det| ≠ 0 := abs_ne_zero.mpr L.isUnit_det'.ne_zero
  have hvol : volume (L '' K) =
      ENNReal.ofReal |L.toLinearMap.det| * volume K :=
    volume.addHaar_image_linearMap L.toLinearMap K
  unfold normalizedProjectionVolume
  rw [projectionBody_linearEquiv_image L K,
    volume.addHaar_image_linearMap, det_projectionBody_transform hn L,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (abs_nonneg _) _),
    hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hc)

theorem standardSimplex_affine_image_normalizedProjectionVolume {n : ℕ} (hn : 0 < n)
    (L : Euclidean n ≃ₗ[ℝ] Euclidean n) (v : Euclidean n) :
    normalizedProjectionVolume (v +ᵥ (L '' standardSimplex n)) = simplexConstant n := by
  rw [normalizedProjectionVolume_vadd, normalizedProjectionVolume_linearEquiv_image hn,
    standardSimplex_normalizedProjectionVolume n hn]

end Paper092

end OAI
