import OAI.NumberTheory.Ostmann.ZeroDensity.FullHeightRegionComparison

namespace OAI

/-! # The unique simple real zero that can enter a character's Riesz rectangle -/

namespace Ostmann

theorem character_near_zero_unique : ∃ c : ℝ, 0 < c ∧
    ∀ (χ : PrimitiveComplexCharacter) (T : ℝ), 2 ≤ T →
      let H := Real.log χ.modulus + Real.log (T + 2) + 1
      (∀ i : ℕ, |((actualCharacterZeros χ).zeros i).im| ≤ T →
        1 - c / H ≤ ((actualCharacterZeros χ).zeros i).re →
          χ.character ^ 2 = 1 ∧ ((actualCharacterZeros χ).zeros i).im = 0) ∧
      (∀ i j : ℕ, |((actualCharacterZeros χ).zeros i).im| ≤ T →
        |((actualCharacterZeros χ).zeros j).im| ≤ T →
        1 - c / H ≤ ((actualCharacterZeros χ).zeros i).re →
        1 - c / H ≤ ((actualCharacterZeros χ).zeros j).re → i = j) := by
  obtain ⟨cn, hcn, hn⟩ := exists_nonquadratic_zero_free_region
  obtain ⟨cr, hcr, hr⟩ := exists_full_height_real_region
  let c := min (cn / 2) (cr / 2)
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hcnc : c < cn := by
    have hh := min_le_left (cn / 2) (cr / 2)
    dsimp [c]
    linarith
  have hcrc : c ≤ cr := by
    have hh := min_le_right (cn / 2) (cr / 2)
    dsimp [c]
    linarith
  refine ⟨c, hc, ?_⟩
  intro χ T hT
  dsimp only
  let H := Real.log χ.modulus + Real.log (T + 2) + 1
  have hq : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
  have hHp : 0 < H := by
    have ht : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
    dsimp [H]
    linarith
  by_cases hsq : χ.character ^ 2 = 1
  · have hreal := hr (χ.asReal hsq) T hT
    dsimp only at hreal
    simp only [realCharacterActualZeros] at hreal
    rw [χ.asReal_asComplex hsq] at hreal
    have hcut : c / H ≤ cr / H := div_le_div_of_nonneg_right hcrc hHp.le
    constructor
    · intro i hi hnear
      refine ⟨hsq, ?_⟩
      apply hreal.1 i
      · exact hi
      · change 1 - cr / H ≤ _
        linarith
    · intro i j hi hj hni hnj
      apply hreal.2 i j
      · exact hi
      · exact hj
      · change 1 - cr / H ≤ _
        linarith
      · change 1 - cr / H ≤ _
        linarith
  · have hnone (i : ℕ) (hi : |((actualCharacterZeros χ).zeros i).im| ≤ T)
        (hnear : 1 - c / H ≤ ((actualCharacterZeros χ).zeros i).re) : False := by
      let V := Real.log χ.modulus + Real.log (|((actualCharacterZeros χ).zeros i).im| + 2) + 1
      have hVp : 0 < V := by
        have ht : 0 ≤ Real.log (|((actualCharacterZeros χ).zeros i).im| + 2) :=
          Real.log_nonneg (by linarith [abs_nonneg ((actualCharacterZeros χ).zeros i).im])
        dsimp [V]
        linarith
      have hVH : V ≤ H := by
        have hh := Real.log_le_log (by positivity : 0 < |((actualCharacterZeros χ).zeros i).im| + 2)
          (show |((actualCharacterZeros χ).zeros i).im| + 2 ≤ T + 2 by linarith)
        dsimp [V, H]
        linarith
      have hm : cn / H ≤ cn / V := div_le_div_of_nonneg_left hcn.le hVp hVH
      have hs : c / H < cn / H := (div_lt_div_iff_of_pos_right hHp).mpr hcnc
      have hz := hn χ hsq i
      change cn / V ≤ _ at hz
      linarith
    exact ⟨fun i hi hnear => (hnone i hi hnear).elim,
      fun i _ hi _ hnear _ => (hnone i hi hnear).elim⟩

end Ostmann

end OAI
