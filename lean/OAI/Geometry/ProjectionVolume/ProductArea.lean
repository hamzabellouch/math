import OAI.Geometry.ProjectionVolume.ProductFacetAreas
import OAI.Geometry.ProjectionVolume.ProjectionJacobian

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace ENNReal Pointwise

namespace Paper092

theorem affineHyperplane_product_area_left {r s : ℕ} (hr : 0 < r)
    (v : Euclidean r) (hv : ‖v‖ = 1) (c : ℝ) (F : Set (Euclidean r))
    (hF : IsCompact F) (hplane : ∀ x ∈ F, ⟪v, x⟫ = c)
    (B : Set (Euclidean s)) (hB : MeasurableSet B) :
    μHE[(r + s - 1 : ℕ)] (splitEuclideanProduct r s ⁻¹' (F ×ˢ B)) =
      μHE[(r - 1 : ℕ)] F * volume B := by
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  let H := normalHyperplane v
  let T : Set (Euclidean r) := (-c) • v +ᵥ F
  have hT : T ⊆ (H : Set (Euclidean r)) := by
    rintro x ⟨y, hy, rfl⟩
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    change ⟪v, (-c) • v + y⟫ = 0
    simp [inner_add_right, inner_smul_right, hv, hplane y hy]
  let b := stdOrthonormalBasis ℝ H
  let f : Euclidean (Module.finrank ℝ H) →ₗᵢ[ℝ] Euclidean r :=
    H.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  let A : Set (Euclidean (Module.finrank ℝ H)) := f ⁻¹' T
  have hTcompact : IsCompact T := hF.image (continuous_const.add continuous_id)
  have hA : MeasurableSet A := hTcompact.measurableSet.preimage f.continuous.measurable
  have hfimage : f '' A = T := by
    apply image_preimage_eq_of_subset
    intro y hy
    refine ⟨b.repr ⟨y, hT hy⟩, ?_⟩
    change ((b.repr.symm (b.repr ⟨y, hT hy⟩) : H) : Euclidean r) = y
    rw [LinearIsometryEquiv.symm_apply_apply]
  have hrank : Module.finrank ℝ H = r - 1 := normalHyperplane_finrank v hv0
  have hvolA : volume A = μHE[(r - 1 : ℕ)] F := by
    have h := f.toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume A
    simp only [finrank_euclideanSpace_fin, LinearIsometry.normDet_eq_one,
      ENNReal.ofReal_one, one_mul] at h
    change μHE[Module.finrank ℝ H] (f '' A) = volume A at h
    rw [hfimage] at h
    conv_lhs at h => rw [hrank]
    change μHE[(r - 1 : ℕ)] ((-c) • v +ᵥ F) = volume A at h
    rw [measure_vadd] at h
    exact h.symm
  have hp := euclideanProductMap_image_area f.toLinearMap
    (LinearMap.id : Euclidean s →ₗ[ℝ] Euclidean s) A B hA hB
  simp only [LinearMap.id_coe, Set.image_id, LinearIsometry.normDet_eq_one,
    LinearMap.normDet_id, one_mul, ENNReal.ofReal_one] at hp
  change μHE[Module.finrank ℝ H + s]
    (splitEuclideanProduct r s ⁻¹' ((f '' A) ×ˢ B)) = volume A * volume B at hp
  rw [hfimage, hvolA] at hp
  change μHE[Module.finrank ℝ H + s]
    (splitEuclideanProduct r s ⁻¹' (((-c) • v +ᵥ F) ×ˢ B)) = _ at hp
  rw [← zero_vadd (Euclidean s) B, splitEuclideanProduct_preimage_vadd, measure_vadd] at hp
  have hdim : Module.finrank ℝ H + s = r + s - 1 := by omega
  simpa only [hdim, zero_vadd] using hp

theorem affineHyperplane_product_area_right {r s : ℕ} (hr : 0 < r)
    (v : Euclidean r) (hv : ‖v‖ = 1) (c : ℝ) (F : Set (Euclidean r))
    (hF : IsCompact F) (hplane : ∀ x ∈ F, ⟪v, x⟫ = c)
    (B : Set (Euclidean s)) (hB : MeasurableSet B) :
    μHE[(s + r - 1 : ℕ)] (splitEuclideanProduct s r ⁻¹' (B ×ˢ F)) =
      volume B * μHE[(r - 1 : ℕ)] F := by
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  let H := normalHyperplane v
  let T : Set (Euclidean r) := (-c) • v +ᵥ F
  have hT : T ⊆ (H : Set (Euclidean r)) := by
    rintro x ⟨y, hy, rfl⟩
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    change ⟪v, (-c) • v + y⟫ = 0
    simp [inner_add_right, inner_smul_right, hv, hplane y hy]
  let b := stdOrthonormalBasis ℝ H
  let f : Euclidean (Module.finrank ℝ H) →ₗᵢ[ℝ] Euclidean r :=
    H.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  let A : Set (Euclidean (Module.finrank ℝ H)) := f ⁻¹' T
  have hTcompact : IsCompact T := hF.image (continuous_const.add continuous_id)
  have hA : MeasurableSet A := hTcompact.measurableSet.preimage f.continuous.measurable
  have hfimage : f '' A = T := by
    apply image_preimage_eq_of_subset
    intro y hy
    refine ⟨b.repr ⟨y, hT hy⟩, ?_⟩
    change ((b.repr.symm (b.repr ⟨y, hT hy⟩) : H) : Euclidean r) = y
    rw [LinearIsometryEquiv.symm_apply_apply]
  have hrank : Module.finrank ℝ H = r - 1 := normalHyperplane_finrank v hv0
  have hvolA : volume A = μHE[(r - 1 : ℕ)] F := by
    have h := f.toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume A
    simp only [finrank_euclideanSpace_fin, LinearIsometry.normDet_eq_one,
      ENNReal.ofReal_one, one_mul] at h
    change μHE[Module.finrank ℝ H] (f '' A) = volume A at h
    rw [hfimage] at h
    conv_lhs at h => rw [hrank]
    change μHE[(r - 1 : ℕ)] ((-c) • v +ᵥ F) = volume A at h
    rw [measure_vadd] at h
    exact h.symm
  have hp := euclideanProductMap_image_area
    (LinearMap.id : Euclidean s →ₗ[ℝ] Euclidean s) f.toLinearMap B A hB hA
  simp only [LinearMap.id_coe, Set.image_id, LinearIsometry.normDet_eq_one,
    LinearMap.normDet_id, one_mul, ENNReal.ofReal_one] at hp
  change μHE[s + Module.finrank ℝ H]
    (splitEuclideanProduct s r ⁻¹' (B ×ˢ (f '' A))) = volume B * volume A at hp
  rw [hfimage, hvolA] at hp
  change μHE[s + Module.finrank ℝ H]
    (splitEuclideanProduct s r ⁻¹' (B ×ˢ ((-c) • v +ᵥ F))) = _ at hp
  rw [← zero_vadd (Euclidean s) B, splitEuclideanProduct_preimage_vadd, measure_vadd] at hp
  have hdim : s + Module.finrank ℝ H = s + r - 1 := by omega
  simpa only [hdim, zero_vadd] using hp

end Paper092

end

end OAI
