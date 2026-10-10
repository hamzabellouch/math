import OAI.NumberTheory.Ostmann.Characters.CharacterFaithfulEnumeration

namespace OAI

/-! # Local ordinate bins retain the actual analytic zero multiplicities -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_local_index_count (χ : PrimitiveComplexCharacter) (S : Finset ℕ) (n : ℤ)
    (hr : ∀ i ∈ S, 1 / 2 ≤ ((actualCharacterZeros χ).zeros i).re)
    (hn : ∀ i ∈ S, ⌊((actualCharacterZeros χ).zeros i).im⌋ = n) :
    (S.card : ℝ) ≤ Real.log (48 * (χ.modulus : ℝ) * (|(n : ℝ) + 1 / 2| + 2)) /
      Real.log (14 / 13) := by
  let Z := actualCharacterZeros χ
  let F := S.image Z.zeros
  have hcard : S.card = ∑ z ∈ F, (S.filter fun i => Z.zeros i = z).card :=
    Finset.card_eq_sum_card_image Z.zeros S
  have hbound : (S.card : ℝ) ≤ ∑ z ∈ F, (characterZeroOrder χ z : ℝ) := by
    rw [hcard, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro z _
    have h := actualCharacterZeros_respectsMultiplicity χ S z
    rw [characterZeroOrder_eq_nat]
    exact_mod_cast h
  have hlocal := characterZeroOrder_sum_le_local χ ((n : ℝ) + 1 / 2) F (by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    have h := character_floor_mem_disk (Z.zeros i) (hr i hi) (Z.in_strip i).2.le
    change Z.zeros i ∈ Metric.closedBall (characterZeroCenter ((n : ℝ) + 1 / 2)) (13 / 8)
    have hni : ⌊(Z.zeros i).im⌋ = n := hn i hi
    simpa only [hni] using h)
  have hlocalR : (∑ z ∈ F, (characterZeroOrder χ z : ℝ)) ≤
      (characterLocalZeroMass χ ((n : ℝ) + 1 / 2) : ℝ) := by exact_mod_cast hlocal
  exact hbound.trans (hlocalR.trans (χ.local_zero_mass_bound _))

 theorem density_local_index_log_bound (Q : ℕ) (hQ : 1 ≤ Q) (T : ℝ) (hT : 2 ≤ T)
    (χ : PrimitiveComplexCharacter) (hχ : χ.modulus ≤ Q) (S : Finset ℕ) (n : ℤ)
    (hr : ∀ i ∈ S, 1 / 2 ≤ ((actualCharacterZeros χ).zeros i).re)
    (hn : ∀ i ∈ S, ⌊((actualCharacterZeros χ).zeros i).im⌋ = n)
    (hcenter : |(n : ℝ) + 1 / 2| ≤ T + 1) :
    (S.card : ℝ) ≤ (8 / Real.log (14 / 13)) * Real.log ((Q : ℝ) * T) := by
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hc : (χ.modulus : ℝ) ≤ Q := by exact_mod_cast hχ
  have hcp : (0 : ℝ) < χ.modulus := by exact_mod_cast χ.positive
  have hl : Real.log 2 ≤ Real.log ((Q : ℝ) * T) := Real.log_le_log (by norm_num) (by nlinarith)
  have hlog : Real.log (48 * (χ.modulus : ℝ) * (|(n : ℝ) + 1 / 2| + 2)) ≤
      8 * Real.log ((Q : ℝ) * T) := by
    have hsize : 48 * (χ.modulus : ℝ) * (|(n : ℝ) + 1 / 2| + 2) ≤
        128 * ((Q : ℝ) * T) := by
      have h1 := mul_le_mul_of_nonneg_left hcenter (show 0 ≤ 48 * (χ.modulus : ℝ) by positivity)
      have h2 := mul_le_mul_of_nonneg_right hc (show 0 ≤ 48 * (T + 3) by positivity)
      nlinarith
    apply (Real.log_le_log (by positivity) hsize).trans
    rw [Real.log_mul (by norm_num) (by positivity)]
    have h128 : Real.log 128 = 7 * Real.log 2 := by
      have h := Real.log_pow (2 : ℝ) 7
      norm_num at h
      exact h
    rw [h128]
    linarith
  have h := (density_local_index_count χ S n hr hn).trans
    (div_le_div_of_nonneg_right hlog (Real.log_pos (by norm_num : (1 : ℝ) < 14 / 13)).le)
  convert h using 1
  ring

end Ostmann

end OAI
