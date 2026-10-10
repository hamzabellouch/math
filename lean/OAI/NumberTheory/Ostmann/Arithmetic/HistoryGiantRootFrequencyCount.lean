import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantFrequencyCount

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantFrequencyCount
open Construction Conclusion Filter

theorem actual_root_pair_card_le (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (hL : 0 ≤ L) (hm : 1 ≤ bulkSize k L) {l : ℕ} (hl : l ≤ k) :
    (Fintype.card (FrequencyChoices (frequencyBound Bs BD Bz k L) (l + 1)) : ℝ) ≤
      Real.exp (2 * actualFrequencyCost Bs BD Bz k * L) := by
  let C := scaleLinearConstant Bs BD Bz k + 1
  have hC : 0 ≤ C := by dsimp only [C]; linarith [scaleLinearConstant_pos Bs BD Bz k]
  have hp : (1 : ℝ) ≤ (4 : ℝ)^k := one_le_pow₀ (by norm_num)
  have hmle := (bulkSize_bounds k hL).2
  have hroot := actual_allowedFrequency_le Bs BD Bz k L hm hl
  have hinternal := actual_pair_card_le Bs BD Bz k L hL hm hl
  have hrootexponent : 4 * C * (bulkSize k L : ℝ) ≤
      actualFrequencyCost Bs BD Bz k * L := by
    have hpow := mul_le_mul_of_nonneg_right hp
      (show 0 ≤ 4 * C * (bulkSize k L : ℝ) by positivity)
    have hsize := mul_le_mul_of_nonneg_left hmle
      (show 0 ≤ 4 * (4 : ℝ)^k * C by positivity)
    dsimp only [actualFrequencyCost]
    change 4 * C * (bulkSize k L : ℝ) ≤ 4 * (4 : ℝ)^k * C * bulkScale k * L
    nlinarith
  have hrootbound : (2 * (frequencyBound Bs BD Bz k L l : ℝ) + 1)^2 ≤
      Real.exp (actualFrequencyCost Bs BD Bz k * L) := by
    calc
      _ ≤ (Real.exp (2 * C * (bulkSize k L : ℝ)))^2 := by gcongr
      _ = Real.exp (4 * C * (bulkSize k L : ℝ)) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hrootexponent
  have hint : (Fintype.card (FrequencyChoices (frequencyBound Bs BD Bz k L) l) : ℝ)^2 ≤
      Real.exp (actualFrequencyCost Bs BD Bz k * L) := by
    simpa only [Fintype.card_prod, Nat.cast_mul, pow_two] using hinternal
  rw [frequencyChoices_card_succ]
  calc
    _ ≤ Real.exp (actualFrequencyCost Bs BD Bz k * L) *
      Real.exp (actualFrequencyCost Bs BD Bz k * L) :=
        mul_le_mul hrootbound hint (sq_nonneg _) (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem eventually_actual_root_pair_card_le (Bs BD Bz : ℝ) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ l : ℕ, l ≤ k →
      (Fintype.card (FrequencyChoices (frequencyBound Bs BD Bz k L) (l + 1)) : ℝ) ≤
        Real.exp (2 * actualFrequencyCost Bs BD Bz k * L) := by
  filter_upwards [(bulkSize_tendsto_atTop hk).eventually_ge_atTop 1,
    eventually_ge_atTop (0 : ℝ)] with L hm hL
  intro l hl
  exact actual_root_pair_card_le Bs BD Bz k L hL (by exact_mod_cast hm) hl

end Ostmann.Arithmetic.HistoryGiantFrequencyCount

end

end OAI
