import OAI.NumberTheory.Ostmann.Construction.CanonicalHistoryProductChoicesDefs

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantFrequencyCount
open Construction

theorem allowedFrequency_card (V : ℕ → ℕ) (l : ℕ) :
    Fintype.card (AllowedFrequency V l) = 2 * V l + 1 := by
  rw [Fintype.card_coe, Int.card_Icc]
  omega

theorem frequencyChoices_card_succ (V : ℕ → ℕ) (l : ℕ) :
    (Fintype.card (FrequencyChoices V (l + 1)) : ℝ) =
      (2 * (V l : ℝ) + 1)^2 * (Fintype.card (FrequencyChoices V l) : ℝ)^2 := by
  change (Fintype.card (AllowedFrequency V l × AllowedFrequency V l ×
    FrequencyChoices V l × FrequencyChoices V l) : ℝ) = _
  simp only [Fintype.card_prod, allowedFrequency_card, Nat.cast_mul, Nat.cast_add,
    Nat.cast_ofNat, Nat.cast_one]
  ring

theorem frequencyChoices_card_le_exp (V : ℕ → ℕ) (k : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hV : ∀ j < k, 2 * (V j : ℝ) + 1 ≤ Real.exp A) :
    ∀ l : ℕ, l ≤ k → (Fintype.card (FrequencyChoices V l) : ℝ) ≤
      Real.exp ((4 : ℝ)^l * A) := by
  intro l
  induction l with
  | zero =>
    intro _
    have hz : Fintype.card (FrequencyChoices V 0) = 1 := by
      change @Fintype.card Unit _ = 1
      exact Fintype.card_unique
    simpa only [hz, Nat.cast_one, pow_zero, one_mul] using Real.one_le_exp hA
  | succ l ih =>
    intro hl
    have hc := ih (by omega)
    have hv := hV l (by omega)
    have hp : (1 : ℝ) ≤ (4 : ℝ)^l := one_le_pow₀ (by norm_num)
    rw [frequencyChoices_card_succ]
    calc
      _ ≤ (Real.exp A)^2 * (Real.exp ((4 : ℝ)^l * A))^2 := by
        gcongr
      _ = Real.exp ((2 + 2 * (4 : ℝ)^l) * A) := by
        rw [pow_two, ← Real.exp_add, pow_two, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp ((4 : ℝ)^(l + 1) * A) := by
        apply Real.exp_le_exp.mpr
        rw [pow_succ]
        nlinarith

end Ostmann.Arithmetic.HistoryGiantFrequencyCount

end

end OAI
