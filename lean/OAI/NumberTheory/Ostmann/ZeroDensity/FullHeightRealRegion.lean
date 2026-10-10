import OAI.NumberTheory.Ostmann.ZeroDensity.FullHeightRealExclusion

namespace OAI

/-! # A uniform full-height real-character zero-free region with one simple exception -/

namespace Ostmann

open Complex

theorem exists_full_height_real_region : ∃ c : ℝ, 0 < c ∧
    ∀ (χ : PrimitiveRealCharacter) (T : ℝ), 2 ≤ T →
      let H := Real.log χ.modulus + Real.log (T + 2) + 1
      (∀ i, |((realCharacterActualZeros χ).zeros i).im| ≤ T →
        1 - c / H ≤ ((realCharacterActualZeros χ).zeros i).re →
        ((realCharacterActualZeros χ).zeros i).im = 0) ∧
      (∀ i j, |((realCharacterActualZeros χ).zeros i).im| ≤ T →
        |((realCharacterActualZeros χ).zeros j).im| ≤ T →
        1 - c / H ≤ ((realCharacterActualZeros χ).zeros i).re →
        1 - c / H ≤ ((realCharacterActualZeros χ).zeros j).re → i = j) := by
  obtain ⟨C, hC, hshift⟩ := exists_full_height_real_shifted_bound
  obtain ⟨R, hR, hreal⟩ := exists_real_zero_sum_upper
  let D := R + C + 4
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨1 / (2000 * D), by positivity, ?_⟩
  intro χ T hT
  dsimp only
  let H := Real.log χ.modulus + Real.log (T + 2) + 1
  have hq : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
  have ht : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hHp : 0 < H := by linarith
  have hqH : Real.log χ.modulus ≤ H := by dsimp [H]; linarith
  let δ := 1 / (100 * D * H)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hDH : 1 ≤ D * H := by
    have hmul := mul_le_mul_of_nonneg_left hH hD.le
    dsimp [D] at *
    linarith
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hmass : δ * (D * H) = 1 / 100 := by dsimp [δ]; field_simp
  have hRE : (1 / 2) * Real.log χ.modulus + R ≤ D * H := by
    have hrh := mul_le_mul_of_nonneg_left hH hR.le
    have hch := mul_nonneg hC.le hHp.le
    dsimp [D]
    nlinarith
  have hCE : C * H ≤ D * H := by dsimp [D]; nlinarith [mul_nonneg hR.le hHp.le]
  have hRb : δ * ((1 / 2) * Real.log χ.modulus + R) ≤ 1 / 10 := by
    have hh := mul_le_mul_of_nonneg_left hRE hδ.le
    rw [hmass] at hh
    linarith
  have hCb : δ * (C * H) ≤ 1 / 10 := by
    have hh := mul_le_mul_of_nonneg_left hCE hδ.le
    rw [hmass] at hh
    linarith
  have hr : shiftedRealCharacterZeroSum χ ((1 + δ : ℝ) : ℂ) ≤
      1 / δ + ((1 / 2) * Real.log χ.modulus + R) := by
    simpa only [add_sub_cancel_left, add_assoc] using
      hreal χ (1 + δ) (by linarith) (by linarith)
  have hs : ∀ t : ℝ, |t| ≤ T →
      4 * shiftedRealCharacterZeroSum χ (((1 + δ : ℝ) : ℂ) + (t : ℂ) * I) ≤
        3 / δ + realZeroKernel δ (2 * t) + C * H := by
    intro t htT
    have hh := hshift χ (1 + δ) t (by linarith) (by linarith)
    simp only [add_sub_cancel_left] at hh
    have hlog : Real.log (|t| + 2) ≤ Real.log (T + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hm := mul_le_mul_of_nonneg_left hlog hC.le
    dsimp [H]
    linarith
  obtain ⟨ha, hu⟩ := near_real_zeros_real_unique_height χ δ
    ((1 / 2) * Real.log χ.modulus + R) (C * H) T hδ hδ1 hRb hCb hr hs
  have hcut : (1 / (2000 * D)) / H = δ / 20 := by
    dsimp [δ]
    field_simp
    ring
  constructor
  · intro i hi hnear
    apply ha i _ hi
    change 1 - (1 / (2000 * D)) / H ≤ _ at hnear
    rwa [hcut] at hnear
  · intro i j hi hj hnear hnear'
    apply hu i j _ _ hi hj
    · change 1 - (1 / (2000 * D)) / H ≤ _ at hnear
      rwa [hcut] at hnear
    · change 1 - (1 / (2000 * D)) / H ≤ _ at hnear'
      rwa [hcut] at hnear'

end Ostmann

end OAI
