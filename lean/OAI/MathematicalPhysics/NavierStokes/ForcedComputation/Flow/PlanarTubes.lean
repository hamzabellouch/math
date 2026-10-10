import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarOrdering
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarPulse

namespace OAI

/-! Clearance for the actual filled extraction and insertion tubes. -/

namespace ForcedComputation.PlanarRouting

open ShearFlows

theorem box_ext {R S : RationalBox 2} (hl : R.lower = S.lower) (hu : R.upper = S.upper) : R = S := by
  cases R
  cases S
  cases hl
  cases hu
  rfl

@[simp] theorem centerQ_sub_halfWidthQ (R : RationalBox 2) (j : Fin 2) :
    centerQ R j - halfWidthQ R j = R.lower j := by
  dsimp [centerQ, halfWidthQ]
  ring

@[simp] theorem centerQ_add_halfWidthQ (R : RationalBox 2) (j : Fin 2) :
    centerQ R j + halfWidthQ R j = R.upper j := by
  dsimp [centerQ, halfWidthQ]
  ring

def horizontalCenter (R : RationalBox 2) (x : ℚ) : Fin 2 → ℚ :=
  letI := ShearFlows.neZeroTwo
  ![x, centerQ R 1]

theorem horizontalTube_eq_rightSweep (R : RationalBox 2) {x : ℚ}
    (hx : centerQ R 0 ≤ x) :
    translationTube R (horizontalCenter R x) = rightSweep R (x + halfWidthQ R 0) := by
  have hl : R.lower 0 ≤ x - halfWidthQ R 0 := by
    rw [← centerQ_sub_halfWidthQ R 0]
    linarith
  apply box_ext
  · funext j
    fin_cases j
    · exact min_eq_left hl
    · simp [translationTube, recenter, horizontalCenter, rightSweep]
  · funext j
    fin_cases j
    · rfl
    · simp [translationTube, recenter, horizontalCenter, rightSweep]

def parkingColumn (n : ℕ) (κ : ℚ) (i : Fin n) : RationalBox 2 :=
  ⟨![(parkingBox n κ i).lower 0, 0], ![(parkingBox n κ i).upper 0, 7 / 8]⟩

theorem parkingColumn_gap {n : ℕ} {κ : ℚ} (hκ : κ ≤ 1 / 64)
    {i j : Fin n} (hij : i ≠ j) : EndpointGap (parkingScale n) (parkingColumn n κ i) (parkingColumn n κ j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨0, Or.inl (parkingBox_gap hκ h)⟩
  · exact ⟨0, Or.inr (parkingBox_gap hκ h)⟩

theorem parkingColumn_left {n : ℕ} {κ : ℚ} (hκ : 0 ≤ κ) (hκ' : κ ≤ 1 / 64)
    (i : Fin n) : (3 / 8 : ℚ) < (parkingColumn n κ i).lower 0 := by
  have hp := (parkingCenter_bounds n i).1
  have hs := parkingScale_pos n
  have hs' := parkingScale_le n
  have hm := mul_le_mul hs' hκ' hκ (by norm_num : (0 : ℚ) ≤ 1 / 64)
  change 3 / 8 < parkingCenter n i 0 - parkingScale n * κ
  nlinarith

theorem low_horizontal_gap_column {n : ℕ} {κ : ℚ} (hκ : 0 ≤ κ) (hκ' : κ ≤ 1 / 64)
    {R : RationalBox 2} (hR : R.upper 0 ≤ 1 / 3) (i : Fin n) :
    EndpointGap (1 / 24) R (parkingColumn n κ i) := by
  refine ⟨0, Or.inl ?_⟩
  have h := parkingColumn_left hκ hκ' i
  linarith

theorem parkingBox_subset_column {n : ℕ} {κ : ℚ} (hκ : 0 ≤ κ) (hκ' : κ ≤ 1 / 64)
    (i : Fin n) : (parkingBox n κ i).carrier ⊆ (parkingColumn n κ i).carrier := by
  intro x hx j
  fin_cases j
  · exact hx 0
  · have hy := parkingBox_bounds hκ hκ' i hx
    have h : (0 : ℝ) ≤ x 1 ∧ x 1 ≤ 7 / 8 := by
      constructor <;> linarith [hy.2.2.1, hy.2.2.2]
    simpa [parkingColumn] using h

theorem verticalTube_subset_column {n : ℕ} {κ : ℚ}
    (R : RationalBox 2) (i : Fin n)
    (hx : centerQ R 0 = parkingCenter n i 0)
    (hw : halfWidthQ R 0 ≤ parkingScale n * κ)
    (hlo : (0 : ℚ) ≤ R.lower 1) (hhi : R.upper 1 ≤ 7 / 8)
    (hheight : halfWidthQ R 1 ≤ 1 / 8) :
    (translationTube R (parkingCenter n i)).carrier ⊆ (parkingColumn n κ i).carrier := by
  have hl₀ : (parkingBox n κ i).lower 0 ≤ R.lower 0 := by
    rw [← centerQ_sub_halfWidthQ R 0, hx]
    exact sub_le_sub_left hw _
  have hu₀ : R.upper 0 ≤ (parkingBox n κ i).upper 0 := by
    rw [← centerQ_add_halfWidthQ R 0, hx]
    change parkingCenter n i 0 + halfWidthQ R 0 ≤ parkingCenter n i 0 + parkingScale n * κ
    exact add_le_add_right hw _
  have hl₁ : (0 : ℚ) ≤ (recenter R (parkingCenter n i)).lower 1 := by
    change 0 ≤ 3 / 4 - halfWidthQ R 1
    linarith
  have hu₁ : (recenter R (parkingCenter n i)).upper 1 ≤ (7 / 8 : ℚ) := by
    change 3 / 4 + halfWidthQ R 1 ≤ 7 / 8
    linarith
  intro x hxR j
  have hb := hxR j
  fin_cases j
  · have hl : (parkingColumn n κ i).lower 0 ≤ (translationTube R (parkingCenter n i)).lower 0 := by
      apply le_min hl₀
      exact sub_le_sub_left hw _
    have hu : (translationTube R (parkingCenter n i)).upper 0 ≤ (parkingColumn n κ i).upper 0 := by
      apply max_le hu₀
      change parkingCenter n i 0 + halfWidthQ R 0 ≤ parkingCenter n i 0 + parkingScale n * κ
      exact add_le_add_right hw _
    have hl' : ((parkingColumn n κ i).lower 0 : ℝ) ≤
        (translationTube R (parkingCenter n i)).lower 0 := by exact_mod_cast hl
    have hu' : ((translationTube R (parkingCenter n i)).upper 0 : ℝ) ≤
        (parkingColumn n κ i).upper 0 := by exact_mod_cast hu
    exact ⟨hl'.trans hb.1, hb.2.trans hu'⟩
  · have hl : (0 : ℚ) ≤ (translationTube R (parkingCenter n i)).lower 1 := le_min hlo hl₁
    have hu : (translationTube R (parkingCenter n i)).upper 1 ≤ (7 / 8 : ℚ) := max_le hhi hu₁
    have hl' : (0 : ℝ) ≤ (translationTube R (parkingCenter n i)).lower 1 := by exact_mod_cast hl
    have hu' : ((translationTube R (parkingCenter n i)).upper 1 : ℝ) ≤ 7 / 8 := by
      have he := (Rat.cast_le (K := ℝ)).mpr hu
      simpa only [Rat.cast_div, Rat.cast_ofNat] using he
    simpa [parkingColumn] using (show (0 : ℝ) ≤ x 1 ∧ x 1 ≤ 7 / 8 from
      ⟨hl'.trans hb.1, hb.2.trans hu'⟩)

end ForcedComputation.PlanarRouting

end OAI
