import OAI.Geometry.ProjectionVolume.AffineBrightness
import OAI.Geometry.ProjectionVolume.ProjectionJacobian

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace

namespace Paper092

def linearImageNormal {n : ℕ} (L : Euclidean n ≃ₗ[ℝ] Euclidean n)
    (v : Euclidean n) : Euclidean n :=
  ‖L.symm.toLinearMap.adjoint v‖⁻¹ • L.symm.toLinearMap.adjoint v

theorem inverseAdjoint_ne_zero {n : ℕ} (L : Euclidean n ≃ₗ[ℝ] Euclidean n)
    (v : Euclidean n) (hv : ‖v‖ = 1) : L.symm.toLinearMap.adjoint v ≠ 0 := by
  intro h
  have hh := L.symm.toLinearMap.adjoint_inner_left (L v) v
  rw [h, inner_zero_left] at hh
  change 0 = ⟪v, L.symm (L v)⟫ at hh
  rw [L.symm_apply_apply, real_inner_self_eq_norm_sq, hv, one_pow] at hh
  norm_num at hh

theorem linearImageNormal_norm {n : ℕ} (L : Euclidean n ≃ₗ[ℝ] Euclidean n)
    (v : Euclidean n) (hv : ‖v‖ = 1) : ‖linearImageNormal L v‖ = 1 := by
  simp [linearImageNormal, norm_smul, inverseAdjoint_ne_zero L v hv]

theorem linearImageNormal_inner {n : ℕ} (L : Euclidean n ≃ₗ[ℝ] Euclidean n)
    (v x : Euclidean n) :
    ⟪linearImageNormal L v, L x⟫ = ⟪v, x⟫ / ‖L.symm.toLinearMap.adjoint v‖ := by
  rw [linearImageNormal, real_inner_smul_left, LinearMap.adjoint_inner_left]
  change ‖L.symm.toLinearMap.adjoint v‖⁻¹ * ⟪v, L.symm (L x)⟫ = _
  rw [L.symm_apply_apply]
  ring

theorem linearImageNormal_support_iff {n : ℕ} (L : Euclidean n ≃ₗ[ℝ] Euclidean n)
    (v x : Euclidean n) (hv : ‖v‖ = 1) (c : ℝ) :
    ⟪linearImageNormal L v, L x⟫ ≤ c / ‖L.symm.toLinearMap.adjoint v‖ ↔ ⟪v, x⟫ ≤ c := by
  rw [linearImageNormal_inner, div_le_div_iff_of_pos_right
    (norm_pos_iff.mpr (inverseAdjoint_ne_zero L v hv))]

theorem linearImageNormal_plane {n : ℕ} (L : Euclidean n ≃ₗ[ℝ] Euclidean n)
    (v : Euclidean n) (c : ℝ) (F : Set (Euclidean n))
    (hplane : ∀ x ∈ F, ⟪v, x⟫ = c) :
    ∀ y ∈ L '' F, ⟪linearImageNormal L v, y⟫ = c / ‖L.symm.toLinearMap.adjoint v‖ := by
  rintro y ⟨x, hx, rfl⟩
  rw [linearImageNormal_inner, hplane x hx]

theorem affineHyperplane_area_lt_top {n : ℕ} (v : Euclidean n) (hv : ‖v‖ = 1)
    (c : ℝ) (F : Set (Euclidean n)) (hF : IsCompact F)
    (hplane : ∀ x ∈ F, ⟪v, x⟫ = c) : μHE[n - 1] F < ⊤ := by
  have h := projectionVolume_of_subset_affine_hyperplane v v hv hv c F hplane
  simp only [real_inner_self_eq_norm_sq, hv, one_pow, abs_one, ENNReal.ofReal_one,
    one_mul] at h
  rw [← h]
  exact (hF.image (normalHyperplane v).orthogonalProjectionOnto.continuous).measure_lt_top

theorem affineHyperplane_linearImage_area_real {n : ℕ}
    (L : Euclidean n ≃ₗ[ℝ] Euclidean n) (v : Euclidean n) (hv : ‖v‖ = 1)
    (c : ℝ) (F : Set (Euclidean n)) (hplane : ∀ x ∈ F, ⟪v, x⟫ = c) :
    (μHE[n - 1] (L '' F)).toReal =
      |L.toLinearMap.det| * ‖L.symm.toLinearMap.adjoint v‖ * (μHE[n - 1] F).toReal := by
  let w := linearImageNormal L v
  have hw : ‖w‖ = 1 := linearImageNormal_norm L v hv
  have hi := brightness_of_subset_affine_hyperplane w w hw
    (c / ‖L.symm.toLinearMap.adjoint v‖) (L '' F) (linearImageNormal_plane L v c F hplane)
  simp only [real_inner_self_eq_norm_sq, hw, one_pow, abs_one, one_mul] at hi
  rw [← hi, brightness_linearEquiv_image,
    brightness_of_subset_affine_hyperplane (L.symm w) v hv c F hplane]
  have hin : ⟪L.symm w, v⟫ = ‖L.symm.toLinearMap.adjoint v‖ := by
    change ⟪L.symm.toLinearMap w, v⟫ = _
    rw [← LinearMap.adjoint_inner_right]
    change ⟪linearImageNormal L v, L.symm.toLinearMap.adjoint v⟫ = _
    rw [linearImageNormal, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp [norm_ne_zero_iff.mpr (inverseAdjoint_ne_zero L v hv)]
  rw [hin, abs_of_nonneg (norm_nonneg _)]
  ring

theorem affineHyperplane_linearImage_area {n : ℕ}
    (L : Euclidean n ≃ₗ[ℝ] Euclidean n) (v : Euclidean n) (hv : ‖v‖ = 1)
    (c : ℝ) (F : Set (Euclidean n)) (hF : IsCompact F)
    (hplane : ∀ x ∈ F, ⟪v, x⟫ = c) :
    μHE[n - 1] (L '' F) = ENNReal.ofReal
      (|L.toLinearMap.det| * ‖L.symm.toLinearMap.adjoint v‖) * μHE[n - 1] F := by
  have hfinite := affineHyperplane_area_lt_top v hv c F hF hplane
  have hfinite' := affineHyperplane_area_lt_top (linearImageNormal L v)
    (linearImageNormal_norm L v hv) (c / ‖L.symm.toLinearMap.adjoint v‖)
    (L '' F) (hF.image L.toContinuousLinearEquiv.continuous)
    (linearImageNormal_plane L v c F hplane)
  apply (ENNReal.toReal_eq_toReal_iff' hfinite'.ne (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite.ne)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (abs_nonneg _) (norm_nonneg _))]
  exact affineHyperplane_linearImage_area_real L v hv c F hplane

end Paper092

end

end OAI
