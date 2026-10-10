import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterRieszBoundary
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterRieszZeroSelection
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterRieszResidueBound

namespace OAI

/-! # A uniform Riesz estimate with its actual possible real-zero term -/

namespace Ostmann

open Complex

theorem character_riesz_local_bound : ∃ c A B E : ℝ,
    0 < c ∧ c ≤ 1 / 4 ∧ c ≤ actualPageConstant / 10 ∧ 0 < A ∧ 0 < B ∧ 0 < E ∧
    ∀ (χ : PrimitiveComplexCharacter) (T : ℝ), 2 ≤ T →
      let H := Real.log χ.modulus + Real.log (T + 4) + 1
      ∃ e : Option ℕ,
        (∀ i, e = some i → 1 - 2 * c / H < ((actualCharacterZeros χ).zeros i).re ∧
          χ.character ^ 2 = 1 ∧ ((actualCharacterZeros χ).zeros i).im = 0) ∧
        (∀ i, 1 - c / H ≤ ((actualCharacterZeros χ).zeros i).re →
          |((actualCharacterZeros χ).zeros i).im| ≤ T → e = some i) ∧
        ∀ X b : ℝ, 1 ≤ X → 1 < b → b ≤ 2 →
          ‖characterRieszMean χ X - characterRieszZeroTerm χ X e‖ ≤
            A * H ^ 2 * X ^ (1 - c / H) + B * H ^ 2 * X ^ b / T ^ 2 +
              2 * (1 / (b - 1) + E) * X ^ b / T := by
  obtain ⟨c, C, hc, hc4, hcp, hC, hdata⟩ := character_riesz_boundary_data
  obtain ⟨K, E, hK, hE, hrect⟩ := characterRieszMean_residue_rectangle_bound
  refine ⟨c, K * C, 4 * C, E, hc, hc4, hcp, by positivity, by positivity, hE, ?_⟩
  intro χ T hT
  dsimp only
  let H := Real.log χ.modulus + Real.log (T + 4) + 1
  have hq : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
  have htlog : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hHp : 0 < H := by linarith
  have hδ : 0 < c / H := div_pos hc hHp
  have hδ4 : c / H ≤ 1 / 4 := calc
    c / H ≤ c / 1 := div_le_div_of_nonneg_left hc.le (by norm_num) hH
    _ ≤ 1 / 4 := by simpa using hc4
  obtain ⟨hr, hu, a, ha, ha', hedge⟩ := hdata χ T hT
  change 1 - 2 * c / H ≤ a at ha
  change a ≤ 1 - c / H at ha'
  have ha0 : 1 / 2 ≤ a := by rw [mul_div_assoc] at ha; linarith
  have ha1 : a < 1 := by linarith
  have hreal (i : ℕ) (hi : a ≤ ((actualCharacterZeros χ).zeros i).re)
      (hit : |((actualCharacterZeros χ).zeros i).im| ≤ T) :
      χ.character ^ 2 = 1 ∧ ((actualCharacterZeros χ).zeros i).im = 0 ∧
        analyticOrderNatAt χ.L ((actualCharacterZeros χ).zeros i) = 1 := by
    apply hr i (by linarith)
    change 1 - 4 * c / H ≤ _
    have hh : 0 ≤ c / H := hδ.le
    rw [mul_div_assoc] at ha ⊢
    linarith
  have huniq (i j : ℕ) (hi : a ≤ ((actualCharacterZeros χ).zeros i).re)
      (hj : a ≤ ((actualCharacterZeros χ).zeros j).re)
      (hit : |((actualCharacterZeros χ).zeros i).im| ≤ T)
      (hjt : |((actualCharacterZeros χ).zeros j).im| ≤ T) : i = j := by
    apply hu i j (by linarith) (by linarith)
    · change 1 - 4 * c / H ≤ _
      rw [mul_div_assoc] at ha ⊢
      linarith
    · change 1 - 4 * c / H ≤ _
      rw [mul_div_assoc] at ha ⊢
      linarith
  obtain ⟨e, he, hecomplete, heres⟩ := character_riesz_zero_selection χ a T
    (by linarith) ha1 (by linarith) (fun s hs ht => (hedge s (.inl ⟨hs, ht⟩)).1)
    hreal huniq
  refine ⟨e, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨hai, hsq, him⟩ := he i hi
    exact ⟨ha.trans_lt hai, hsq, him⟩
  · intro i hi hit
    exact hecomplete i (ha'.trans hi) hit
  · intro X b hX hb hb2
    have hab : a ≤ b := ha1.le.trans hb.le
    have hbound (s : ℂ) (hs : (s.re = a ∧ |s.im| ≤ T) ∨
        (a ≤ s.re ∧ s.re ≤ b ∧ |s.im| = T)) : ‖logDeriv χ.L s‖ ≤ C * H ^ 2 := by
      apply (hedge s _).2
      rcases hs with hs | hs
      · exact .inl hs
      · exact .inr ⟨hs.1, hs.2.1.trans hb2, hs.2.2⟩
    have hh := hrect χ X a b T (C * H ^ 2) (characterRieszZeroTerm χ X e)
      hX ha0 hab hb hb2 (by linarith) (by positivity)
      (heres X b (by linarith) hb) hbound
    have hx : X ^ a ≤ X ^ (1 - c / H) := Real.rpow_le_rpow_of_exponent_le hX ha'
    have hfirst := mul_le_mul_of_nonneg_left hx (show 0 ≤ K * (C * H ^ 2) by positivity)
    have hlen : b - a ≤ 2 := by linarith
    have hsecond := mul_le_mul_of_nonneg_left hlen
      (show 0 ≤ 2 * (C * H ^ 2 * X ^ b / T ^ 2) by positivity)
    calc
      _ ≤ K * (C * H ^ 2) * X ^ a +
          2 * (C * H ^ 2 * X ^ b / T ^ 2) * (b - a) +
          2 * (1 / (b - 1) + E) * X ^ b / T := hh
      _ ≤ K * (C * H ^ 2) * X ^ (1 - c / H) +
          2 * (C * H ^ 2 * X ^ b / T ^ 2) * 2 +
          2 * (1 / (b - 1) + E) * X ^ b / T := by linarith
      _ = _ := by ring

end Ostmann

end OAI
