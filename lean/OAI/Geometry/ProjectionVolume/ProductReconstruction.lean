import OAI.Geometry.ProjectionVolume.ProductPolytope

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

namespace Paper092

theorem cartesianBody_volume {r s : ℕ} (A : Set (Euclidean r)) (B : Set (Euclidean s))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    volume (cartesianBody A B) = volume A * volume B := by
  rw [cartesianBody_eq_preimage, splitEuclideanProduct_volume r s A B hA hB]

theorem volume_smul_toReal {d : ℕ} (S : Set (Euclidean d)) (c : ℝ) :
    (volume (c • S)).toReal = |c| ^ d * (volume S).toReal := by
  rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, ENNReal.toReal_mul, abs_pow,
    ENNReal.toReal_ofReal (pow_nonneg (abs_nonneg c) d)]

theorem projectionBody_cartesian_of_brightness {r s : ℕ}
    (A : Set (Euclidean r)) (B : Set (Euclidean s))
    (ha : 0 < (volume A).toReal) (hb : 0 < (volume B).toReal)
    (h : ∀ w, brightness (cartesianBody A B) w =
      (volume B).toReal * brightness A (splitEuclideanProduct r s w).1 +
      (volume A).toReal * brightness B (splitEuclideanProduct r s w).2) :
    projectionBody (cartesianBody A B) =
      cartesianBody ((volume B).toReal • projectionBody A)
        ((volume A).toReal • projectionBody B) := by
  have hAz : brightness A 0 = 0 := by simp [brightness]
  have hBz : brightness B 0 = 0 := by simp [brightness]
  ext z
  change (∀ w, ⟪w, z⟫ ≤ brightness (cartesianBody A B) w) ↔
    ((splitEuclideanProduct r s z).1 ∈ (volume B).toReal • projectionBody A ∧
      (splitEuclideanProduct r s z).2 ∈ (volume A).toReal • projectionBody B)
  constructor
  · intro hz
    constructor
    · rw [mem_smul_set_iff_inv_smul_mem₀ hb.ne']
      intro u
      have hu := hz (productLiftLeft r s u)
      rw [h, inner_productLiftLeft, split_productLiftLeft] at hu
      simp only [hBz, mul_zero, add_zero] at hu
      have hh := mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hb.le)
      simpa only [inner_smul_right, ← mul_assoc, inv_mul_cancel₀ hb.ne', one_mul] using hh
    · rw [mem_smul_set_iff_inv_smul_mem₀ ha.ne']
      intro u
      have hu := hz (productLiftRight r s u)
      rw [h, inner_productLiftRight, split_productLiftRight] at hu
      simp only [hAz, mul_zero, zero_add] at hu
      have hh := mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr ha.le)
      simpa only [inner_smul_right, ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] using hh
  · rintro ⟨⟨x, hx, hxe⟩, ⟨y, hy, hye⟩⟩ w
    rw [h, splitEuclideanProduct_inner r s, ← hxe, ← hye, inner_smul_right,
      inner_smul_right]
    exact add_le_add (mul_le_mul_of_nonneg_left (hx _) hb.le)
      (mul_le_mul_of_nonneg_left (hy _) ha.le)

theorem normalized_cartesian_of_projectionBody_eq {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (A : Set (Euclidean r)) (B : Set (Euclidean s)) (hA : IsCompact A) (hB : IsCompact B)
    (ha : 0 < (volume A).toReal) (hb : 0 < (volume B).toReal)
    (h : projectionBody (cartesianBody A B) =
      cartesianBody ((volume B).toReal • projectionBody A)
        ((volume A).toReal • projectionBody B)) :
    normalizedProjectionVolume (cartesianBody A B) =
      normalizedProjectionVolume A * normalizedProjectionVolume B := by
  unfold normalizedProjectionVolume
  rw [h, cartesianBody_volume _ _
    (IsCompact.smul _ (projectionBody_isCompact A)).measurableSet
    (IsCompact.smul _ (projectionBody_isCompact B)).measurableSet,
    cartesianBody_volume A B hA.measurableSet hB.measurableSet,
    ENNReal.toReal_mul, ENNReal.toReal_mul, volume_smul_toReal, volume_smul_toReal,
    abs_of_pos hb, abs_of_pos ha, mul_pow]
  have hpa : (volume A).toReal ^ (r + s - 1) =
      (volume A).toReal ^ (r - 1) * (volume A).toReal ^ s := by
    rw [← pow_add]
    congr 1
    omega
  have hpb : (volume B).toReal ^ (r + s - 1) =
      (volume B).toReal ^ (s - 1) * (volume B).toReal ^ r := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpa, hpb]
  field_simp [ha.ne', hb.ne']

end Paper092

end

end OAI
