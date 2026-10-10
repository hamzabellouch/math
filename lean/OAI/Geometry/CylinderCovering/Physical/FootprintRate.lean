import OAI.Geometry.CylinderCovering.Physical.PhysicalFootprints

namespace OAI

noncomputable section
open Set MeasureTheory

namespace CylinderCovering.Footprints

theorem sum_affineArea_error_bound {n : ℕ} {R d A B h : ℝ}
    (M W : Fin n → ℝ) (hM : ∀ i, 0 ≤ M i) (hMR : ∀ i, M i ≤ R)
    (hW : ∀ i, 0 ≤ W i) (hWh : ∀ i, W i ≤ h)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B) (hh : 0 ≤ h) :
    0 ≤ (∑ i, W i * affineArea (M i) d A B) -
        (∑ i, W i * (d * (M i)^2 / 2)) ∧
      (∑ i, W i * affineArea (M i) d A B) -
        (∑ i, W i * (d * (M i)^2 / 2)) ≤
        (n : ℝ) * h * ((A + 2 * B) * R + 4*A*B) * d^2 := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  constructor
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hW i)
      (affineArea_error_bound (hM i) (hMR i) hd hd1 hA hB).1)
  · calc
      (∑ i, W i * (affineArea (M i) d A B - d * (M i)^2 / 2)) ≤
          ∑ _i : Fin n, h * (((A + 2 * B) * R + 4*A*B) * d^2) := by
        apply Finset.sum_le_sum
        intro i _
        have he := affineArea_error_bound (hM i) (hMR i) hd hd1 hA hB
        exact mul_le_mul (hWh i) he.2 he.1 hh
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end CylinderCovering.Footprints

namespace CylinderCovering.PhysicalFootprints
open RuledApproximation Footprints

theorem physicalWeight_le_one (h : ℝ) (g : Plane) : physicalWeight h g ≤ 1 := by
  have hs : 1 ≤ Real.sqrt (1 + g 0 ^ 2 + h ^ 2 * g 1 ^ 2) := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by positivity)).2
    nlinarith [sq_nonneg (g 0), mul_nonneg (sq_nonneg h) (sq_nonneg (g 1))]
  exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hs).trans_eq (by norm_num)

theorem absolute_family_area_error {n : ℕ} {h R d A B : ℝ}
    (hh : 0 < h) (M m : Fin n → ℝ) (g : Fin n → Plane)
    (hM : ∀ i, 0 ≤ M i) (hMR : ∀ i, M i ≤ R)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ familyArea (fun i => footprintCylinder h (g i)
        (absoluteFootprint (m i) (M i) d A B)) -
      (∑ i, h * physicalWeight h (g i) * (d * (M i)^2 / 2)) ∧
    familyArea (fun i => footprintCylinder h (g i)
        (absoluteFootprint (m i) (M i) d A B)) -
      (∑ i, h * physicalWeight h (g i) * (d * (M i)^2 / 2)) ≤
      (n : ℝ) * h * ((A + 2*B)*R + (A^2 + 4*A*B)) * d^2 := by
  have hcost : familyArea (fun i => footprintCylinder h (g i)
      (absoluteFootprint (m i) (M i) d A B)) =
      ∑ i, (h * physicalWeight h (g i)) * absoluteArea (M i) d A B := by
    unfold familyArea
    apply Finset.sum_congr rfl
    intro i _
    rw [footprintCylinder_area hh (g i) (isCompact_absoluteFootprint _ _ _ _ _),
      realVolume_absoluteFootprint (hM i) hd hA hB]
    ring
  rw [hcost]
  exact sum_absoluteArea_error_bound M (fun i => h * physicalWeight h (g i)) hM hMR
    (fun i => mul_nonneg hh.le (physicalWeight_pos h (g i)).le)
    (fun i => by simpa using mul_le_mul_of_nonneg_left (physicalWeight_le_one h (g i)) hh.le)
    hd hd1 hA hB hh.le

theorem affine_family_area_error {n : ℕ} {h R d A B : ℝ}
    (hh : 0 < h) (M m : Fin n → ℝ) (g : Fin n → Plane)
    (hM : ∀ i, 0 ≤ M i) (hMR : ∀ i, M i ≤ R)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (hA : 0 ≤ A) (hB : A/2 ≤ B) :
    0 ≤ familyArea (fun i => footprintCylinder h (g i)
        (affineFootprint (m i) (M i) d A B)) -
      (∑ i, h * physicalWeight h (g i) * (d * (M i)^2 / 2)) ∧
    familyArea (fun i => footprintCylinder h (g i)
        (affineFootprint (m i) (M i) d A B)) -
      (∑ i, h * physicalWeight h (g i) * (d * (M i)^2 / 2)) ≤
      (n : ℝ) * h * ((A + 2*B)*R + 4*A*B) * d^2 := by
  have hB0 : 0 ≤ B := (div_nonneg hA (by norm_num : (0 : ℝ) ≤ 2)).trans hB
  have hcost : familyArea (fun i => footprintCylinder h (g i)
      (affineFootprint (m i) (M i) d A B)) =
      ∑ i, (h * physicalWeight h (g i)) * affineArea (M i) d A B := by
    unfold familyArea
    apply Finset.sum_congr rfl
    intro i _
    rw [footprintCylinder_area hh (g i) (isCompact_affineFootprint _ _ _ _ _),
      realVolume_affineFootprint (hM i) hd hA hB]
    ring
  rw [hcost]
  exact sum_affineArea_error_bound M (fun i => h * physicalWeight h (g i)) hM hMR
    (fun i => mul_nonneg hh.le (physicalWeight_pos h (g i)).le)
    (fun i => by simpa using mul_le_mul_of_nonneg_left (physicalWeight_le_one h (g i)) hh.le)
    hd hd1 hA hB0 hh.le

theorem absolute_equal_mesh_error {N : ℕ} {h R L A B : ℝ}
    (hN : 0 < N) (hh : 0 < h) (hL : 0 ≤ L) (hLN : L ≤ (N : ℝ))
    (M m : Fin N → ℝ) (g : Fin N → Plane)
    (hM : ∀ i, 0 ≤ M i) (hMR : ∀ i, M i ≤ R)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ familyArea (fun i => footprintCylinder h (g i)
        (absoluteFootprint (m i) (M i) (L/N) A B)) -
      (∑ i, h * physicalWeight h (g i) * ((L/N) * (M i)^2 / 2)) ∧
    familyArea (fun i => footprintCylinder h (g i)
        (absoluteFootprint (m i) (M i) (L/N) A B)) -
      (∑ i, h * physicalWeight h (g i) * ((L/N) * (M i)^2 / 2)) ≤
      h * ((A + 2*B)*R + (A^2 + 4*A*B)) * L^2 / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have he := absolute_family_area_error hh M m g hM hMR
    (div_nonneg hL hn.le) ((div_le_one hn).2 hLN) hA hB
  convert he using 1
  field_simp

theorem affine_equal_mesh_error {N : ℕ} {h R L A B : ℝ}
    (hN : 0 < N) (hh : 0 < h) (hL : 0 ≤ L) (hLN : L ≤ (N : ℝ))
    (M m : Fin N → ℝ) (g : Fin N → Plane)
    (hM : ∀ i, 0 ≤ M i) (hMR : ∀ i, M i ≤ R)
    (hA : 0 ≤ A) (hB : A/2 ≤ B) :
    0 ≤ familyArea (fun i => footprintCylinder h (g i)
        (affineFootprint (m i) (M i) (L/N) A B)) -
      (∑ i, h * physicalWeight h (g i) * ((L/N) * (M i)^2 / 2)) ∧
    familyArea (fun i => footprintCylinder h (g i)
        (affineFootprint (m i) (M i) (L/N) A B)) -
      (∑ i, h * physicalWeight h (g i) * ((L/N) * (M i)^2 / 2)) ≤
      h * ((A + 2*B)*R + 4*A*B) * L^2 / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have he := affine_family_area_error hh M m g hM hMR
    (div_nonneg hL hn.le) ((div_le_one hn).2 hLN) hA hB
  convert he using 1
  field_simp

end CylinderCovering.PhysicalFootprints

end

end OAI
