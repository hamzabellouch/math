import OAI.Geometry.CylinderCovering.Physical.ProjectionDictionary
import OAI.Geometry.CylinderCovering.Radial.PartitionAffine

namespace OAI

open Set
noncomputable section
namespace RadialPhysical
open CylinderCovering

lemma halfheight_upperLocal_image {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (i : Fin N) :
    mapToCanonical b '' upperSweepOn false b eta T (RadialRiemann.cell (-b) b N i) =
      upperSweepOn true 1 (effectiveTilt b eta) (fun r => 2*T (b*r))
        (RadialRiemann.cell (-1) 1 N i) := by
  have hb0 := ne_of_gt hb
  ext z
  constructor
  · rintro ⟨v, ⟨s, hs, rho, hrho, x, hx, rfl⟩, rfl⟩
    have hbs : b*(s/b)=s := by field_simp
    refine ⟨s/b, (RadialRiemann.div_mem_symmetric_cell_iff hb N i s).2 hs,
      2*rho, ⟨by linarith [hrho.1], ?_⟩, 2*x/b, ?_, ?_⟩
    · change 2*rho ≤ 2*T (b*(s/b))
      rw [hbs]
      linarith [hrho.2]
    · change |x| ≤ b at hx
      norm_num only [axialBound, Bool.true_eq, ite_true, mul_one]
      rw [abs_div, abs_mul, abs_of_pos hb]
      norm_num
      apply (div_le_iff₀ hb).mpr
      linarith
    · ext j
      fin_cases j <;> simp [mapToCanonical, upperPoint, point, height,
        effectiveTilt] <;> field_simp
      ring
  · rintro ⟨r, hr, rho, hrho, x, hx, hz⟩
    refine ⟨upperPoint b eta (rho/2) (b*r) (b*x/2), ?_, ?_⟩
    · refine ⟨b*r, ?_, (rho/2), ⟨by linarith [hrho.1], by linarith [hrho.2]⟩, (b*x/2), ?_, rfl⟩
      · apply (RadialRiemann.div_mem_symmetric_cell_iff hb N i (b*r)).1
        simpa [hb0] using hr
      · norm_num only [axialBound, Bool.true_eq, ite_true, mul_one] at hx
        change |(b*x/2)| ≤ b
        rw [abs_div, abs_mul, abs_of_pos hb]
        norm_num
        nlinarith
    · rw [hz]
      ext j
      fin_cases j <;> simp [mapToCanonical, upperPoint, point, height,
        effectiveTilt] <;> field_simp
      ring

lemma halfheight_lowerLocal_image {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (i : Fin N) :
    mapToCanonical b '' lowerSweepOn false b eta T (RadialRiemann.cell (-b) b N i) =
      lowerSweepOn true 1 (effectiveTilt b eta) (fun r => 2*T (b*r))
        (RadialRiemann.cell (-1) 1 N i) := by
  have hb0 := ne_of_gt hb
  ext z
  constructor
  · rintro ⟨v, ⟨s, hs, rho, hrho, x, hx, rfl⟩, rfl⟩
    have hbs : b*(s/b)=s := by field_simp
    refine ⟨s/b, (RadialRiemann.div_mem_symmetric_cell_iff hb N i s).2 hs,
      2*rho, ⟨by linarith [hrho.1], ?_⟩, 2*x/b, ?_, ?_⟩
    · change 2*rho ≤ 2*T (b*(s/b))
      rw [hbs]
      linarith [hrho.2]
    · change |x| ≤ b at hx
      norm_num only [axialBound, Bool.true_eq, ite_true, mul_one]
      rw [abs_div, abs_mul, abs_of_pos hb]
      norm_num
      apply (div_le_iff₀ hb).mpr
      linarith
    · ext j
      fin_cases j <;> simp [mapToCanonical, lowerPoint, point, height,
        effectiveTilt] <;> field_simp
      ring
  · rintro ⟨r, hr, rho, hrho, x, hx, hz⟩
    refine ⟨lowerPoint false b eta (rho/2) (b*r) (b*x/2), ?_, ?_⟩
    · refine ⟨b*r, ?_, (rho/2), ⟨by linarith [hrho.1], by linarith [hrho.2]⟩, (b*x/2), ?_, rfl⟩
      · apply (RadialRiemann.div_mem_symmetric_cell_iff hb N i (b*r)).1
        simpa [hb0] using hr
      · norm_num only [axialBound, Bool.true_eq, ite_true, mul_one] at hx
        change |(b*x/2)| ≤ b
        rw [abs_div, abs_mul, abs_of_pos hb]
        norm_num
        nlinarith
    · rw [hz]
      ext j
      fin_cases j <;> simp [mapToCanonical, lowerPoint, point, height,
        effectiveTilt] <;> field_simp
      ring

lemma centered_upperLocal_image {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (i : Fin N) :
    mapCenteredToCanonical b '' upperSweepOn true b eta T (RadialRiemann.cell (-b) b N i) =
      upperSweepOn true 1 (effectiveTilt b eta) (fun r => T (b*r))
        (RadialRiemann.cell (-1) 1 N i) := by
  have hb0 := ne_of_gt hb
  ext z
  constructor
  · rintro ⟨v, ⟨s, hs, rho, hrho, x, hx, rfl⟩, rfl⟩
    have hbs : b*(s/b)=s := by field_simp
    refine ⟨s/b, (RadialRiemann.div_mem_symmetric_cell_iff hb N i s).2 hs,
      rho, ⟨hrho.1, ?_⟩, x/b, ?_, ?_⟩
    · change rho ≤ T (b*(s/b))
      rw [hbs]
      linarith [hrho.2]
    · change |x| ≤ 2*b at hx
      norm_num only [axialBound, Bool.true_eq, ite_true, mul_one]
      rw [abs_div, abs_of_pos hb]
      apply (div_le_iff₀ hb).mpr
      linarith
    · ext j
      fin_cases j <;> simp [mapCenteredToCanonical, upperPoint, point, height,
        effectiveTilt] <;> field_simp
  · rintro ⟨r, hr, rho, hrho, x, hx, hz⟩
    refine ⟨upperPoint b eta rho (b*r) (b*x), ?_, ?_⟩
    · refine ⟨b*r, ?_, rho, hrho, (b*x), ?_, rfl⟩
      · apply (RadialRiemann.div_mem_symmetric_cell_iff hb N i (b*r)).1
        simpa [hb0] using hr
      · norm_num only [axialBound, Bool.true_eq, ite_true, mul_one] at hx
        change |(b*x)| ≤ 2*b
        rw [abs_mul, abs_of_pos hb]
        nlinarith
    · rw [hz]
      ext j
      fin_cases j <;> simp [mapCenteredToCanonical, upperPoint, point, height,
        effectiveTilt] <;> field_simp

lemma centered_lowerLocal_image {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (i : Fin N) :
    mapCenteredToCanonical b '' lowerSweepOn true b eta T (RadialRiemann.cell (-b) b N i) =
      lowerSweepOn true 1 (effectiveTilt b eta) (fun r => T (b*r))
        (RadialRiemann.cell (-1) 1 N i) := by
  have hb0 := ne_of_gt hb
  ext z
  constructor
  · rintro ⟨v, ⟨s, hs, rho, hrho, x, hx, rfl⟩, rfl⟩
    have hbs : b*(s/b)=s := by field_simp
    refine ⟨s/b, (RadialRiemann.div_mem_symmetric_cell_iff hb N i s).2 hs,
      rho, ⟨hrho.1, ?_⟩, x/b, ?_, ?_⟩
    · change rho ≤ T (b*(s/b))
      rw [hbs]
      linarith [hrho.2]
    · change |x| ≤ 2*b at hx
      norm_num only [axialBound, Bool.true_eq, ite_true, mul_one]
      rw [abs_div, abs_of_pos hb]
      apply (div_le_iff₀ hb).mpr
      linarith
    · ext j
      fin_cases j <;> simp [mapCenteredToCanonical, lowerPoint, point, height,
        effectiveTilt] <;> field_simp
  · rintro ⟨r, hr, rho, hrho, x, hx, hz⟩
    refine ⟨lowerPoint true b eta rho (b*r) (b*x), ?_, ?_⟩
    · refine ⟨b*r, ?_, rho, hrho, (b*x), ?_, rfl⟩
      · apply (RadialRiemann.div_mem_symmetric_cell_iff hb N i (b*r)).1
        simpa [hb0] using hr
      · norm_num only [axialBound, Bool.true_eq, ite_true, mul_one] at hx
        change |(b*x)| ≤ 2*b
        rw [abs_mul, abs_of_pos hb]
        nlinarith
    · rw [hz]
      ext j
      fin_cases j <;> simp [mapCenteredToCanonical, lowerPoint, point, height,
        effectiveTilt] <;> field_simp

lemma upperPhysicalAxis_normalized {b : ℝ} (hb : 0 < b) (eta s : ℝ) :
    upperPhysicalAxis b eta s =
      upperPhysicalAxis 1 (effectiveTilt b eta) (s/b) := by
  rw [upperPhysicalAxis_canonical (ne_of_gt hb),
    upperPhysicalAxis_canonical (show (1 : ℝ) ≠ 0 by norm_num)]
  simp [effectiveTilt]

lemma lowerPhysicalAxis_normalized {b : ℝ} (hb : 0 < b) (eta s : ℝ) :
    lowerPhysicalAxis b eta s =
      lowerPhysicalAxis 1 (effectiveTilt b eta) (s/b) := by
  rw [lowerPhysicalAxis_canonical (ne_of_gt hb),
    lowerPhysicalAxis_canonical (show (1 : ℝ) ≠ 0 by norm_num)]
  simp [effectiveTilt]

lemma halfheight_upperBase_image {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) :
    (fun z => (2/b) • z -
        TriangularCovering.projection (upperPhysicalAxis b eta (tag i))
          (!₂[0,0,Real.sqrt 2] : Space)) ''
      upperPhysicalBase false b eta T N tag i =
        upperPhysicalBase true 1 (effectiveTilt b eta) (fun r => 2*T (b*r))
          N (fun j => tag j/b) i := by
  unfold upperPhysicalBase
  rw [← projected_image_mapToCanonical, halfheight_upperLocal_image hb,
    upperPhysicalAxis_normalized hb]

lemma halfheight_upperBase_area {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) :
    TriangularCovering.area
      (upperPhysicalBase true 1 (effectiveTilt b eta) (fun r => 2*T (b*r))
        N (fun j => tag j/b) i) =
      (2/b)^2 * TriangularCovering.area (upperPhysicalBase false b eta T N tag i) := by
  unfold upperPhysicalBase
  rw [← upperPhysicalAxis_normalized hb eta (tag i),
    ← halfheight_upperLocal_image hb eta T N i]
  exact projected_area_mapToCanonical (ne_of_gt hb) _ _

lemma halfheight_lowerBase_image {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) :
    (fun z => (2/b) • z -
        TriangularCovering.projection (lowerPhysicalAxis b eta (tag i))
          (!₂[0,0,Real.sqrt 2] : Space)) ''
      lowerPhysicalBase false b eta T N tag i =
        lowerPhysicalBase true 1 (effectiveTilt b eta) (fun r => 2*T (b*r))
          N (fun j => tag j/b) i := by
  unfold lowerPhysicalBase
  rw [← projected_image_mapToCanonical, halfheight_lowerLocal_image hb,
    lowerPhysicalAxis_normalized hb]

lemma halfheight_lowerBase_area {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) :
    TriangularCovering.area
      (lowerPhysicalBase true 1 (effectiveTilt b eta) (fun r => 2*T (b*r))
        N (fun j => tag j/b) i) =
      (2/b)^2 * TriangularCovering.area (lowerPhysicalBase false b eta T N tag i) := by
  unfold lowerPhysicalBase
  rw [← lowerPhysicalAxis_normalized hb eta (tag i),
    ← halfheight_lowerLocal_image hb eta T N i]
  exact projected_area_mapToCanonical (ne_of_gt hb) _ _

lemma centered_upperBase_image {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) :
    (fun z => (1/b) • z) ''
      upperPhysicalBase true b eta T N tag i =
        upperPhysicalBase true 1 (effectiveTilt b eta) (fun r => T (b*r))
          N (fun j => tag j/b) i := by
  unfold upperPhysicalBase
  rw [← projected_image_mapCenteredToCanonical, centered_upperLocal_image hb,
    upperPhysicalAxis_normalized hb]

lemma centered_upperBase_area {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) :
    TriangularCovering.area
      (upperPhysicalBase true 1 (effectiveTilt b eta) (fun r => T (b*r))
        N (fun j => tag j/b) i) =
      (1/b)^2 * TriangularCovering.area (upperPhysicalBase true b eta T N tag i) := by
  unfold upperPhysicalBase
  rw [← upperPhysicalAxis_normalized hb eta (tag i),
    ← centered_upperLocal_image hb eta T N i]
  exact projected_area_mapCenteredToCanonical (ne_of_gt hb) _ _

lemma centered_lowerBase_image {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) :
    (fun z => (1/b) • z) ''
      lowerPhysicalBase true b eta T N tag i =
        lowerPhysicalBase true 1 (effectiveTilt b eta) (fun r => T (b*r))
          N (fun j => tag j/b) i := by
  unfold lowerPhysicalBase
  rw [← projected_image_mapCenteredToCanonical, centered_lowerLocal_image hb,
    lowerPhysicalAxis_normalized hb]

lemma centered_lowerBase_area {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) :
    TriangularCovering.area
      (lowerPhysicalBase true 1 (effectiveTilt b eta) (fun r => T (b*r))
        N (fun j => tag j/b) i) =
      (1/b)^2 * TriangularCovering.area (lowerPhysicalBase true b eta T N tag i) := by
  unfold lowerPhysicalBase
  rw [← lowerPhysicalAxis_normalized hb eta (tag i),
    ← centered_lowerLocal_image hb eta T N i]
  exact projected_area_mapCenteredToCanonical (ne_of_gt hb) _ _

lemma halfheight_actualCost_scale {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tagU tagL : Fin N → ℝ) :
    physicalActualCost true 1 (effectiveTilt b eta) (fun r => 2*T (b*r))
      N (fun j => tagU j/b) (fun j => tagL j/b) =
      (2/b)^2 * physicalActualCost false b eta T N tagU tagL := by
  unfold physicalActualCost
  simp only [halfheight_upperBase_area hb, halfheight_lowerBase_area hb,
    ← Finset.mul_sum, mul_add]

lemma centered_actualCost_scale {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tagU tagL : Fin N → ℝ) :
    physicalActualCost true 1 (effectiveTilt b eta) (fun r => T (b*r))
      N (fun j => tagU j/b) (fun j => tagL j/b) =
      (1/b)^2 * physicalActualCost true b eta T N tagU tagL := by
  unfold physicalActualCost
  simp only [centered_upperBase_area hb, centered_lowerBase_area hb,
    ← Finset.mul_sum, mul_add]

lemma halfheight_upperCylinder_image {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) :
    mapToCanonical b ''
      RadialSweep.cylinder (upperPhysicalAxis b eta (tag i))
        (upperPhysicalBase false b eta T N tag i) =
      RadialSweep.cylinder (upperPhysicalAxis 1 (effectiveTilt b eta) (tag i/b))
        (upperPhysicalBase true 1 (effectiveTilt b eta) (fun r => 2*T (b*r))
          N (fun j => tag j/b) i) := by
  rw [cylinder_mapToCanonical (ne_of_gt hb), halfheight_upperBase_image hb,
    upperPhysicalAxis_normalized hb]

lemma halfheight_lowerCylinder_image {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) :
    mapToCanonical b ''
      RadialSweep.cylinder (lowerPhysicalAxis b eta (tag i))
        (lowerPhysicalBase false b eta T N tag i) =
      RadialSweep.cylinder (lowerPhysicalAxis 1 (effectiveTilt b eta) (tag i/b))
        (lowerPhysicalBase true 1 (effectiveTilt b eta) (fun r => 2*T (b*r))
          N (fun j => tag j/b) i) := by
  rw [cylinder_mapToCanonical (ne_of_gt hb), halfheight_lowerBase_image hb,
    lowerPhysicalAxis_normalized hb]

lemma centered_upperCylinder_image {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) :
    mapCenteredToCanonical b ''
      RadialSweep.cylinder (upperPhysicalAxis b eta (tag i))
        (upperPhysicalBase true b eta T N tag i) =
      RadialSweep.cylinder (upperPhysicalAxis 1 (effectiveTilt b eta) (tag i/b))
        (upperPhysicalBase true 1 (effectiveTilt b eta) (fun r => T (b*r))
          N (fun j => tag j/b) i) := by
  rw [cylinder_mapCenteredToCanonical (ne_of_gt hb), centered_upperBase_image hb,
    upperPhysicalAxis_normalized hb]

lemma centered_lowerCylinder_image {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) :
    mapCenteredToCanonical b ''
      RadialSweep.cylinder (lowerPhysicalAxis b eta (tag i))
        (lowerPhysicalBase true b eta T N tag i) =
      RadialSweep.cylinder (lowerPhysicalAxis 1 (effectiveTilt b eta) (tag i/b))
        (lowerPhysicalBase true 1 (effectiveTilt b eta) (fun r => T (b*r))
          N (fun j => tag j/b) i) := by
  rw [cylinder_mapCenteredToCanonical (ne_of_gt hb), centered_lowerBase_image hb,
    lowerPhysicalAxis_normalized hb]

end RadialPhysical

end

end OAI
