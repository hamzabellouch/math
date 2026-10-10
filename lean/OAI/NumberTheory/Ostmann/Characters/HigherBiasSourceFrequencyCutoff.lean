import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyBudgetBasic
import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScaleBasic

namespace OAI

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Filter InitialCharacterScale

theorem eventually_initial_frequency_budget_covers_width (k : ℕ) (BD : ℝ)
    (hBD : 0≤BD) (W : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (initialGap BD k L+W) ≤
        4*(HistoryFrequencyBudget.bound (BD+20*Real.log (depthScale k))
          (wordSize k L : ℝ) 0 : ℝ) := by
  have hz : 0≤Real.log (depthScale k) := by
    unfold depthScale
    rw [Real.log_exp]
    positivity
  have ha : 0≤BD+20*Real.log (depthScale k) := by positivity
  filter_upwards [(Real.tendsto_sqrt_atTop.comp (wordSize_tendsto k)).eventually_ge_atTop W] with L hL
  let a := BD+20*Real.log (depthScale k)
  let m := (wordSize k L : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hW : W≤2*Real.sqrt m := by
    have h0 := Real.sqrt_nonneg m
    change W≤Real.sqrt m at hL
    linarith
  have hpos : 1≤HistoryFrequencyBudget.bound a m 0 := HistoryFrequencyBudget.bound_pos ha hm 0
  have hf := Nat.lt_floor_add_one (Real.exp (HistoryFrequencyBudget.exponent a m 0))
  have hposR : (1:ℝ)≤(HistoryFrequencyBudget.bound a m 0:ℝ) := by exact_mod_cast hpos
  have hmain : Real.exp (initialGap BD k L+W)≤Real.exp (HistoryFrequencyBudget.exponent a m 0) := by
    apply Real.exp_le_exp.mpr
    simp only [HistoryFrequencyBudget.exponent,pow_zero,one_mul,mul_one,initialGap]
    change a*m+W≤a*m+2*Real.sqrt m
    linarith
  change Real.exp (initialGap BD k L+W)≤4*(HistoryFrequencyBudget.bound a m 0:ℝ)
  unfold HistoryFrequencyBudget.bound at hposR ⊢
  linarith

end Ostmann.Characters.HigherBiasSource

end

end OAI
