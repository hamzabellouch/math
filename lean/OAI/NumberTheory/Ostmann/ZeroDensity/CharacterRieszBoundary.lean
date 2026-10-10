import OAI.NumberTheory.Ostmann.ZeroDensity.OneZeroBoundaryCut
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterNearZeroSimple
import OAI.NumberTheory.Ostmann.Characters.CharacterLogarithmicSeparation
import OAI.NumberTheory.Ostmann.ZeroDensity.ActualLocalZeros

namespace OAI

/-! # A uniformly controlled Riesz boundary, including exceptional characters -/

namespace Ostmann

open Complex

theorem character_riesz_boundary_data : ∃ c C : ℝ,
    0 < c ∧ c ≤ 1 / 4 ∧ c ≤ actualPageConstant / 10 ∧ 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (T : ℝ), 2 ≤ T →
      let H := Real.log χ.modulus + Real.log (T + 4) + 1
      (∀ i : ℕ, |((actualCharacterZeros χ).zeros i).im| ≤ T + 2 →
        1 - 4 * c / H ≤ ((actualCharacterZeros χ).zeros i).re →
        χ.character ^ 2 = 1 ∧ ((actualCharacterZeros χ).zeros i).im = 0 ∧
          analyticOrderNatAt χ.L ((actualCharacterZeros χ).zeros i) = 1) ∧
      (∀ i j : ℕ, |((actualCharacterZeros χ).zeros i).im| ≤ T + 2 →
        |((actualCharacterZeros χ).zeros j).im| ≤ T + 2 →
        1 - 4 * c / H ≤ ((actualCharacterZeros χ).zeros i).re →
        1 - 4 * c / H ≤ ((actualCharacterZeros χ).zeros j).re → i = j) ∧
      ∃ a : ℝ, 1 - 2 * c / H ≤ a ∧ a ≤ 1 - c / H ∧
        ∀ s : ℂ, ((s.re = a ∧ |s.im| ≤ T) ∨
          (a ≤ s.re ∧ s.re ≤ 2 ∧ |s.im| = T)) →
          χ.L s ≠ 0 ∧ ‖logDeriv χ.L s‖ ≤ C * H ^ 2 := by
  obtain ⟨c0, hc0, hnear⟩ := character_near_zero_simple
  obtain ⟨C0, hC0, hbound⟩ := character_logDeriv_logarithmic_separation
  let c := min (c0 / 4) (min (1 / 4) (actualPageConstant / 10))
  have hc : 0 < c := lt_min (by positivity) (lt_min (by norm_num)
    (div_pos actualPageConstant_pos (by norm_num)))
  have hc4 : c ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hcp : c ≤ actualPageConstant / 10 := (min_le_right _ _).trans (min_le_right _ _)
  have hcc : 4 * c ≤ c0 := by
    have hh := min_le_left (c0 / 4) (min (1 / 4) (actualPageConstant / 10))
    dsimp [c]
    linarith
  refine ⟨c, C0 * (1 + 2 / c), hc, hc4, hcp, by positivity, ?_⟩
  intro χ T hT
  dsimp only
  let H := Real.log χ.modulus + Real.log (T + 4) + 1
  have hq : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
  have htlog : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hHp : 0 < H := by linarith
  let δ := c / H
  have hδ : 0 < δ := div_pos hc hHp
  have hδ4 : δ ≤ 1 / 4 := calc
    c / H ≤ c / 1 := div_le_div_of_nonneg_left hc.le (by norm_num) hH
    _ ≤ 1 / 4 := by simpa using hc4
  obtain ⟨hr, hu⟩ := hnear χ (T + 2) (by linarith)
  rw [show T + 2 + 2 = T + 4 by ring] at hr hu
  have hfrac : 4 * c / H ≤ c0 / H := div_le_div_of_nonneg_right hcc hHp.le
  have hr' (i : ℕ) (hi : |((actualCharacterZeros χ).zeros i).im| ≤ T + 2)
      (hn : 1 - 4 * c / H ≤ ((actualCharacterZeros χ).zeros i).re) :
      χ.character ^ 2 = 1 ∧ ((actualCharacterZeros χ).zeros i).im = 0 ∧
        analyticOrderNatAt χ.L ((actualCharacterZeros χ).zeros i) = 1 := by
    apply hr i hi
    change 1 - c0 / H ≤ _
    linarith
  have hu' (i j : ℕ) (hi : |((actualCharacterZeros χ).zeros i).im| ≤ T + 2)
      (hj : |((actualCharacterZeros χ).zeros j).im| ≤ T + 2)
      (hni : 1 - 4 * c / H ≤ ((actualCharacterZeros χ).zeros i).re)
      (hnj : 1 - 4 * c / H ≤ ((actualCharacterZeros χ).zeros j).re) : i = j := by
    apply hu i j hi hj <;> change 1 - c0 / H ≤ _ <;> linarith
  refine ⟨hr', hu', ?_⟩
  obtain ⟨a, ha, ha', hsep⟩ := one_zero_boundary_cut (actualCharacterZeros χ).zeros δ T
    hδ hδ4 hT (fun i hi hn => (hr' i hi (by simpa [δ, mul_div_assoc] using hn)).2.1)
    (fun i j hi hj hni hnj => hu' i j hi hj
      (by simpa [δ, mul_div_assoc] using hni) (by simpa [δ, mul_div_assoc] using hnj))
  refine ⟨a, by simpa [δ, mul_div_assoc] using ha, ha', ?_⟩
  intro s hs
  have hsa : a ≤ s.re := by
    rcases hs with hs | hs
    · exact hs.1.ge
    · exact hs.1
  have hs2 : s.re ≤ 2 := by
    rcases hs with hs | hs
    · rw [hs.1]; linarith
    · exact hs.2.1
  have hst : |s.im| ≤ T := by
    rcases hs with hs | hs
    · exact hs.2
    · exact hs.2.2.le
  have hspos : 1 / 2 ≤ s.re := by linarith
  have hdist := hsep s hs
  have hne : χ.L s ≠ 0 := by
    have hcn : χ.completed s ≠ 0 := by
      intro hz
      obtain ⟨i, hi⟩ := actualCharacterZeros_complete χ s ((χ.completed_zero_iff s).mp hz)
      have hh := hdist i
      rw [hi, sub_self, norm_zero] at hh
      linarith
    rw [χ.L_eq_completed_mul_all]
    exact mul_ne_zero hcn (χ.gammaInverse_ne_zero s (by linarith))
  refine ⟨hne, ?_⟩
  have hb := hbound χ s (δ / 2) hspos hs2 (by positivity) hdist
  have hlogs : Real.log χ.modulus + Real.log (|s.im| + 2) + 1 ≤ H := by
    have hh := Real.log_le_log (by positivity : 0 < |s.im| + 2)
      (show |s.im| + 2 ≤ T + 4 by linarith)
    dsimp [H]
    linarith
  have hinv : (δ / 2)⁻¹ = 2 * H / c := by dsimp [δ]; field_simp
  have hcost : 1 + (δ / 2)⁻¹ ≤ H * (1 + 2 / c) := by
    rw [hinv]
    calc
      1 + 2 * H / c ≤ H + 2 * H / c := add_le_add hH le_rfl
      _ = H * (1 + 2 / c) := by ring
  calc
    _ ≤ C0 * H * (H * (1 + 2 / c)) := hb.trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hlogs hC0.le) hcost
        (by positivity) (by positivity))
    _ = _ := by ring

end Ostmann

end OAI
