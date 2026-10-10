import OAI.Geometry.ProjectionVolume.PrismVolume

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

namespace Paper092

theorem vadd_add_set {n : ℕ} (a : Euclidean n) (A B : Set (Euclidean n)) :
    (a +ᵥ A) + B = a +ᵥ (A + B) := by
  ext z
  constructor
  · rintro ⟨x, ⟨x₀, hx, rfl⟩, y, hy, rfl⟩
    exact ⟨x₀ + y, ⟨x₀, hx, y, hy, rfl⟩, (add_assoc a x₀ y).symm⟩
  · rintro ⟨z, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨a + x, ⟨x, hx, rfl⟩, y, hy, add_assoc a x y⟩

theorem affineHyperplane_unitPrism_volume {n : ℕ} (hn : 0 < n)
    (v : Euclidean n) (hv : ‖v‖ = 1) (c : ℝ) (F : Set (Euclidean n))
    (hF : IsCompact F) (hplane : ∀ x ∈ F, ⟪v, x⟫ = c) :
    volume (F + segment ℝ 0 v) = μHE[n - 1] F := by
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  let H := normalHyperplane v
  let T : Set (Euclidean n) := (-c) • v +ᵥ F
  have hT : T ⊆ (H : Set (Euclidean n)) := by
    rintro x ⟨y, hy, rfl⟩
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    change ⟪v, (-c) • v + y⟫ = 0
    simp [inner_add_right, inner_smul_right, hv, hplane y hy]
  let b := stdOrthonormalBasis ℝ H
  let f : Euclidean (Module.finrank ℝ H) →ₗᵢ[ℝ] Euclidean n :=
    H.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  let A : Set (Euclidean (Module.finrank ℝ H)) := f ⁻¹' T
  have hTcompact : IsCompact T := hF.image (continuous_const.add continuous_id)
  have hA : MeasurableSet A := hTcompact.measurableSet.preimage f.continuous.measurable
  have hfimage : f '' A = T := by
    apply image_preimage_eq_of_subset
    intro y hy
    refine ⟨b.repr ⟨y, hT hy⟩, ?_⟩
    change ((b.repr.symm (b.repr ⟨y, hT hy⟩) : H) : Euclidean n) = y
    rw [LinearIsometryEquiv.symm_apply_apply]
  have hrank : Module.finrank ℝ H = n - 1 := normalHyperplane_finrank v hv0
  have hvolA : volume A = μHE[n - 1] F := by
    have h := f.toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume A
    simp only [finrank_euclideanSpace_fin, LinearIsometry.normDet_eq_one,
      ENNReal.ofReal_one, one_mul] at h
    change μHE[Module.finrank ℝ H] (f '' A) = volume A at h
    rw [hfimage] at h
    conv_lhs at h => rw [hrank]
    change μHE[n - 1] ((-c) • v +ᵥ F) = volume A at h
    rw [measure_vadd] at h
    exact h.symm
  have hfperp (x : Euclidean (Module.finrank ℝ H)) : ⟪v, f x⟫ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b.repr.symm x).property
  have h := orthogonalPrism_volume f v hv hfperp (by omega) A hA
  rw [hfimage, hvolA] at h
  change volume (((-c) • v +ᵥ F) + segment ℝ 0 v) = _ at h
  rw [vadd_add_set, measure_vadd] at h
  exact h

theorem linearImage_unitPrism {n : ℕ} (L : Euclidean n ≃ₗ[ℝ] Euclidean n)
    (v : Euclidean n) (F : Set (Euclidean n)) :
    L '' (F + segment ℝ 0 v) = L '' F + segment ℝ 0 (L v) := by
  rw [Set.image_add]
  congr 1
  simpa using (image_segment ℝ (L.toLinearMap.toAffineMap) (0 : Euclidean n) v)

theorem linearImage_unitPrism_volume {n : ℕ} (hn : 0 < n)
    (L : Euclidean n ≃ₗ[ℝ] Euclidean n) (v : Euclidean n) (hv : ‖v‖ = 1)
    (c : ℝ) (F : Set (Euclidean n)) (hF : IsCompact F)
    (hplane : ∀ x ∈ F, ⟪v, x⟫ = c) :
    volume (L '' F + segment ℝ 0 (L v)) = ENNReal.ofReal |L.toLinearMap.det| * μHE[n - 1] F := by
  rw [← linearImage_unitPrism]
  change volume (L.toLinearMap '' (F + segment ℝ 0 v)) = _
  rw [volume.addHaar_image_linearMap, affineHyperplane_unitPrism_volume hn v hv c F hF hplane]

theorem linearImage_unitPrism_height {n : ℕ} (L : Euclidean n ≃ₗ[ℝ] Euclidean n)
    (v : Euclidean n) (hv : ‖v‖ = 1) :
    ⟪linearImageNormal L v, L v⟫ = 1 / ‖L.symm.toLinearMap.adjoint v‖ := by
  rw [linearImageNormal_inner, real_inner_self_eq_norm_sq, hv, one_pow]

theorem linearImage_unitPrism_offset {n : ℕ} (L : Euclidean n ≃ₗ[ℝ] Euclidean n)
    (v : Euclidean n) (hv : ‖v‖ = 1) (c : ℝ) (x : Euclidean n)
    (hx : ⟪v, x⟫ = c) (t : ℝ) :
    ⟪linearImageNormal L v, L (x + t • v)⟫ =
      c / ‖L.symm.toLinearMap.adjoint v‖ + t / ‖L.symm.toLinearMap.adjoint v‖ := by
  rw [linearImageNormal_inner, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hv, one_pow, mul_one, hx, add_div]

theorem linearImage_unitPrism_volume_eq_area_mul_height {n : ℕ} (hn : 0 < n)
    (L : Euclidean n ≃ₗ[ℝ] Euclidean n) (v : Euclidean n) (hv : ‖v‖ = 1)
    (c : ℝ) (F : Set (Euclidean n)) (hF : IsCompact F)
    (hplane : ∀ x ∈ F, ⟪v, x⟫ = c) :
    (volume (L '' F + segment ℝ 0 (L v))).toReal =
      (μHE[n - 1] (L '' F)).toReal * (1 / ‖L.symm.toLinearMap.adjoint v‖) := by
  rw [linearImage_unitPrism_volume hn L v hv c F hF hplane, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), affineHyperplane_linearImage_area_real L v hv c F hplane]
  field_simp [norm_ne_zero_iff.mpr (inverseAdjoint_ne_zero L v hv)]

end Paper092

end

end OAI
