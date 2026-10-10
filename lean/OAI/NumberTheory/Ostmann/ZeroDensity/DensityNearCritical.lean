import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OAI.NumberTheory.Ostmann.Characters.CharacterFaithfulEnumeration

namespace OAI

/-! # Ordinary zero counting in the narrow strip next to the critical line -/

namespace Ostmann

open scoped BigOperators

 theorem density_near_critical_power (B σ : ℝ) (hB : 1 < B)
    (_hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) (hnear : σ ≤ 1 / 2 + 1 / Real.log B) :
    B ≤ Real.exp 2 * B ^ (3 * (1 - σ) / (2 - σ)) := by
  let a := 3 * (1 - σ) / (2 - σ)
  have hl : 0 < Real.log B := Real.log_pos hB
  have hd : 0 < 2 - σ := by linarith
  have he : (1 - a) * (2 - σ) = 2 * (σ - 1 / 2) := by
    dsimp [a]
    field_simp
    ring
  have ht : 2 * (σ - 1 / 2) ≤ 2 / Real.log B := by
    rw [show 2 / Real.log B = 2 * (1 / Real.log B) by ring]
    linarith
  have hp : 2 / Real.log B ≤ (2 / Real.log B) * (2 - σ) := by
    apply le_mul_of_one_le_right (by positivity)
    linarith
  have ha : 1 - a ≤ 2 / Real.log B := by nlinarith
  have hm : (1 - a) * Real.log B ≤ 2 := by
    have hh := mul_le_mul_of_nonneg_right ha hl.le
    rwa [div_mul_cancel₀ _ hl.ne'] at hh
  calc
    B = Real.exp (Real.log B) := (Real.exp_log (by linarith)).symm
    _ ≤ Real.exp (2 + Real.log B * a) := Real.exp_le_exp.mpr (by nlinarith)
    _ = Real.exp 2 * B ^ a := by rw [Real.exp_add, Real.rpow_def_of_pos (by linarith)]

 theorem density_ordinary_family_bound (Q : ℕ) (hQ : 1 ≤ Q) (T : ℝ) (hT : 0 ≤ T)
    (σ : ℝ) (F : Finset PrimitiveComplexCharacter) (hF : ∀ χ ∈ F, χ.modulus ≤ Q) :
    (∑ χ ∈ F, ((actualCharacterZeros χ).count σ T : ℝ)) ≤
      (32 / Real.log (14 / 13)) * (Q : ℝ) ^ 2 * (T + 1) *
        Real.log ((Q : ℝ) * (T + 2)) := by
  calc
    _ ≤ ∑ χ ∈ F, ((actualCharacterZeros χ).count 0 T : ℝ) := by
      apply Finset.sum_le_sum
      intro χ _
      apply Nat.cast_le.mpr
      rw [ComplexZeroEnumeration.count_zero_eq_card]
      exact Finset.card_filter_le _ _
    _ ≤ _ := family_zero_count_of_individual (32 / Real.log (14 / 13))
      (by positivity)
      (fun χ U hU => (actualCharacterZeros χ).count_bound_of_multiplicity
        (actualCharacterZeros_respectsMultiplicity χ) U hU) Q hQ T hT F hF

 theorem density_log_thirteen_absorption (x : ℝ) (hx : Real.log 2 ≤ x) :
    x ≤ (Real.log 2)⁻¹ ^ 12 * x ^ 13 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx0 : 0 ≤ x := hl.le.trans hx
  have hp := pow_le_pow_left₀ hl.le hx 12
  have h : (Real.log 2) ^ 12 * x ≤ x ^ 13 := by
    calc
      _ ≤ x ^ 12 * x := mul_le_mul_of_nonneg_right hp hx0
      _ = _ := by ring
  calc
    x = (Real.log 2)⁻¹ ^ 12 * ((Real.log 2) ^ 12 * x) := by
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hl.ne', one_pow, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

 theorem density_near_critical_family :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T σ : ℝ, 2 ≤ T →
      1 / 2 ≤ σ → σ ≤ 1 → σ ≤ 1 / 2 + 1 / Real.log ((Q : ℝ) ^ 2 * T) →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ((actualCharacterZeros χ).count σ T : ℝ)) ≤
        C * ((Q : ℝ) ^ 2 * T) ^ (3 * (1 - σ) / (2 - σ)) *
          (Real.log ((Q : ℝ) * T)) ^ 13 := by
  let C0 := 32 / Real.log (14 / 13)
  refine ⟨4 * C0 * Real.exp 2 * (Real.log 2)⁻¹ ^ 12, by dsimp [C0]; positivity, ?_⟩
  intro Q hQ T σ hT hσ hσ1 hnear F hF
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq0 : (0 : ℝ) < Q := by linarith
  have hB : 1 < (Q : ℝ) ^ 2 * T := by nlinarith
  have hl : Real.log 2 ≤ Real.log ((Q : ℝ) * T) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have hl0 : 0 ≤ Real.log ((Q : ℝ) * T) := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hl
  have hlog : Real.log ((Q : ℝ) * (T + 2)) ≤ 2 * Real.log ((Q : ℝ) * T) := by
    calc
      _ ≤ Real.log (2 * ((Q : ℝ) * T)) := Real.log_le_log (by positivity) (by nlinarith)
      _ = Real.log 2 + Real.log ((Q : ℝ) * T) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ _ := by linarith
  have hC : 0 ≤ C0 := by dsimp [C0]; positivity
  have hlog0 : 0 ≤ Real.log ((Q : ℝ) * (T + 2)) :=
    Real.log_nonneg (by nlinarith)
  have hordinary := density_ordinary_family_bound Q hQ T (by linarith) σ F hF
  have hpow := density_near_critical_power ((Q : ℝ) ^ 2 * T) σ hB hσ hσ1 hnear
  have habs := density_log_thirteen_absorption (Real.log ((Q : ℝ) * T)) hl
  calc
    _ ≤ C0 * (Q : ℝ) ^ 2 * (T + 1) * Real.log ((Q : ℝ) * (T + 2)) := hordinary
    _ ≤ C0 * (Q : ℝ) ^ 2 * (2 * T) * (2 * Real.log ((Q : ℝ) * T)) := by
      apply mul_le_mul _ hlog hlog0 (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith : T + 1 ≤ 2 * T) (by positivity)
    _ = 4 * C0 * ((Q : ℝ) ^ 2 * T) * Real.log ((Q : ℝ) * T) := by ring
    _ ≤ 4 * C0 * (Real.exp 2 * ((Q : ℝ) ^ 2 * T) ^ (3 * (1 - σ) / (2 - σ))) *
        ((Real.log 2)⁻¹ ^ 12 * (Real.log ((Q : ℝ) * T)) ^ 13) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) habs hl0 (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
