import OAI.Geometry.CylinderCovering.Angular.TableCover

namespace OAI

noncomputable section
open Set

namespace CylinderCovering.AngularTableCover

open AngularTable

theorem continuous_ceiling_cover :
    ∃ δ A : ℝ, 0 < δ ∧ 0 < A ∧ ∀ c : ℝ, 0 < c → c < δ →
      RowConclusion .radial (continuousTwo c ⌈2 / c ^ 2⌉₊)
        (1 / 2 - (13 / 6000 : ℝ) * c ^ 2) A c := by
  obtain ⟨δ, A, hδ, hA, h⟩ := table_covers.2.2.2.1
  exact ⟨δ, A, hδ, hA, fun c hc hcδ => h c hc hcδ _ (Nat.le_ceil _)⟩

theorem continuous_reciprocal_covers :
    ∃ N : ℕ, ∃ A : ℝ, 0 < N ∧ 0 < A ∧ ∀ n ≥ N,
      ∀ m : ℕ, 2 * n ^ 2 ≤ m →
        RowConclusion .radial (continuousTwo (1 / (n : ℝ)) m)
          (1 / 2 - (13 / 6000 : ℝ) * (1 / (n : ℝ)) ^ 2) A (1 / (n : ℝ)) := by
  obtain ⟨δ, A, hδ, hA, h⟩ := table_covers.2.2.2.1
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hNreal : (0 : ℝ) < N := (one_div_pos.mpr hδ).trans hN
  have hNpos : 0 < N := by exact_mod_cast hNreal
  refine ⟨N, A, hNpos, hA, ?_⟩
  intro n hn m hm
  have hnpos : 0 < n := hNpos.trans_le hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnlarge : 1 / δ < (n : ℝ) := hN.trans_le (by exact_mod_cast hn)
  have hsmall : 1 / (n : ℝ) < δ := by
    apply (div_lt_iff₀ hnr).mpr
    have hh := (div_lt_iff₀ hδ).mp hnlarge
    nlinarith only [hh]
  apply h (1 / (n : ℝ)) (one_div_pos.mpr hnr) hsmall m
  have hmreal : 2 * (n : ℝ) ^ 2 ≤ (m : ℝ) := by exact_mod_cast hm
  simpa only [one_div, inv_pow, div_inv_eq_mul] using hmreal

theorem squared_family_costs :
    ∃ N : ℕ, ∃ B : ℝ, 0 < N ∧ 0 < B ∧ ∀ n ≥ N,
      |lowerFamilyArea .squared (squaredTwo n) -
        TriangularCovering.H *
          (1 / 4 + (1 / 240 - 1 / 120) * (1 / (n : ℝ)) ^ 2)| ≤
        B * (1 / (n : ℝ)) ^ 4 ∧
      |upperFamilyArea .squared (squaredTwo n) -
        TriangularCovering.H *
          (1 / 4 + (1 / 240 - 1 / 120) * (1 / (n : ℝ)) ^ 2)| ≤
        B * (1 / (n : ℝ)) ^ 4 := by
  obtain ⟨N, A, hN, hA, h⟩ := table_covers.2.2.2.2.1
  refine ⟨N, 8 * TriangularCovering.H * A, hN,
    mul_pos (mul_pos (by norm_num) TriangularCovering.H_pos) hA, ?_⟩
  intro n hn
  have he := (h n hn).1.2.2.2.1
  dsimp only [squaredTwo] at he
  simp only [show (2 : ℝ) / 2 = 1 by norm_num] at he
  rw [AngularTableGeometry.normalizedArea_dilate (by norm_num : (1 : ℝ) ≠ 0)] at he
  have hf := AngularTableGeometry.squared_separate_family_expansions
    (n := n) (A := A) (D := data .squared (squaredTwo n)) he
  convert hf using 1 <;>
    simp [lowerFamilyArea, upperFamilyArea, squaredTwo, data,
      AngularCaps.withSquaredCaps, AngularOrdinaryCaps.ordinaryData] <;> rfl

theorem cartesian_family_costs :
    ∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧ ∀ t : ℝ, 0 < t → t < δ →
      |lowerFamilyArea (.cartesian (3 / 4)) (cartesianThreeQuarters t) -
        ((1 / TriangularCovering.H) / 4 -
          (1 / TriangularCovering.H) * t ^ 2 / 3840)| ≤ B * t ^ 4 ∧
      |upperFamilyArea (.cartesian (3 / 4)) (cartesianThreeQuarters t) -
        ((1 / TriangularCovering.H) / 4 -
          (1 / TriangularCovering.H) * t ^ 2 / 3840)| ≤ B * t ^ 4 := by
  obtain ⟨δ, A, hδ, hA, h⟩ := table_covers.2.2.2.2.2.2.1
  refine ⟨δ, A / (32 * TriangularCovering.H), hδ,
    div_pos hA (mul_pos (by norm_num) TriangularCovering.H_pos), ?_⟩
  intro t ht htδ
  have he := (h t ht htδ).1.2.2.2.1
  dsimp only [cartesianThreeQuarters] at he
  have hscale : Real.sqrt 2 / 2 = 1 / TriangularCovering.H := by
    change TriangularCovering.H / 2 = 1 / TriangularCovering.H
    apply (div_eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)
      TriangularCovering.H_ne_zero).mpr
    nlinarith [TriangularCovering.H_sq]
  rw [hscale, AngularTableGeometry.normalizedArea_dilate
    (one_div_ne_zero TriangularCovering.H_ne_zero)] at he
  have hf := AngularTableGeometry.cartesian_separate_family_expansions
    (lam := t) (A := A) (D := data (.cartesian (3 / 4)) (cartesianThreeQuarters t)) he
  convert hf using 1 <;>
    simp [lowerFamilyArea, upperFamilyArea, cartesianThreeQuarters, hscale,
      data, CartesianCaps.cartesianData, CartesianCaps.withCartesianCaps,
      AngularOrdinaryCaps.ordinaryData] <;> rfl

theorem reciprocal_midpoint_data (n : ℕ) :
    data .midpoint (midpointOne (1 / (n : ℝ))) = data .midpoint (midpointTwo n) := by
  simp only [data, midpointOne, midpointTwo, one_div, inv_inv, ← Nat.cast_pow,
    Nat.ceil_natCast]

theorem reciprocal_midpoint_lower_base (n j : ℕ) :
    AngularTableGeometry.dilate 2
      (AngularTableGeometry.lowerBase (1 / 2) (1 / (n : ℝ))
        (data .midpoint (midpointOne (1 / (n : ℝ)))) j) =
      AngularTableGeometry.lowerBase 1 (1 / (n : ℝ))
        (data .midpoint (midpointTwo n)) j := by
  rw [reciprocal_midpoint_data]
  simp only [AngularTableGeometry.lowerBase, AngularTableGeometry.dilate,
    image_image, smul_smul]
  norm_num

theorem reciprocal_midpoint_upper_base (n j : ℕ) :
    AngularTableGeometry.dilate 2
      (AngularTableGeometry.upperBase (1 / 2) (1 / (n : ℝ))
        (data .midpoint (midpointOne (1 / (n : ℝ)))) j) =
      AngularTableGeometry.upperBase 1 (1 / (n : ℝ))
        (data .midpoint (midpointTwo n)) j := by
  rw [reciprocal_midpoint_data]
  simp only [AngularTableGeometry.upperBase, AngularTableGeometry.dilate,
    image_image, smul_smul]
  norm_num

end CylinderCovering.AngularTableCover

end

end OAI
