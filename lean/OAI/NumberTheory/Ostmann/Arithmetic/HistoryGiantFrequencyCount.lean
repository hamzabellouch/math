import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantFrequencyCountBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightScaleNumerics

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantFrequencyCount
open Construction Conclusion Filter

def actualFrequencyCost (Bs BD Bz : ℝ) (k : ℕ) : ℝ :=
  4 * (4 : ℝ)^k * (scaleLinearConstant Bs BD Bz k + 1) * bulkScale k

theorem actualFrequencyCost_pos (Bs BD Bz : ℝ) {k : ℕ} (hk : 0 < k) :
    0 < actualFrequencyCost Bs BD Bz k := by
  have hC := scaleLinearConstant_pos Bs BD Bz k
  unfold actualFrequencyCost bulkScale
  positivity

theorem actual_allowedFrequency_le (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (hm : 1 ≤ bulkSize k L) {j : ℕ} (hj : j ≤ k) :
    2 * (frequencyBound Bs BD Bz k L j : ℝ) + 1 ≤
      Real.exp (2 * (scaleLinearConstant Bs BD Bz k + 1) * (bulkSize k L : ℝ)) := by
  have hlog := log_frequencyBound_add_one_le_linear Bs BD Bz k L hm hj
  have hp : (frequencyBound Bs BD Bz k L j : ℝ) + 1 ≤
      Real.exp ((scaleLinearConstant Bs BD Bz k + 1) * (bulkSize k L : ℝ)) :=
    (Real.log_le_iff_le_exp (by positivity)).mp hlog
  calc
    _ ≤ ((frequencyBound Bs BD Bz k L j : ℝ) + 1)^2 := by
      nlinarith [sq_nonneg (frequencyBound Bs BD Bz k L j : ℝ)]
    _ ≤ (Real.exp ((scaleLinearConstant Bs BD Bz k + 1) * (bulkSize k L : ℝ)))^2 := by
      gcongr
    _ = _ := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring

theorem actual_pair_card_le (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (hL : 0 ≤ L) (hm : 1 ≤ bulkSize k L) {l : ℕ} (hl : l ≤ k) :
    (Fintype.card (FrequencyChoices (frequencyBound Bs BD Bz k L) l ×
      FrequencyChoices (frequencyBound Bs BD Bz k L) l) : ℝ) ≤
      Real.exp (actualFrequencyCost Bs BD Bz k * L) := by
  let C := scaleLinearConstant Bs BD Bz k + 1
  let A := 2 * C * (bulkSize k L : ℝ)
  have hC : 0 ≤ C := by dsimp only [C]; linarith [scaleLinearConstant_pos Bs BD Bz k]
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hc := frequencyChoices_card_le_exp (frequencyBound Bs BD Bz k L) k hA
    (fun j hj => actual_allowedFrequency_le Bs BD Bz k L hm hj.le) l hl
  have hp : (4 : ℝ)^l ≤ (4 : ℝ)^k := pow_le_pow_right₀ (by norm_num) hl
  have hmle := (bulkSize_bounds k hL).2
  have hterm := mul_le_mul_of_nonneg_right hp hA
  have hsize := mul_le_mul_of_nonneg_left hmle
    (show 0 ≤ 4 * (4 : ℝ)^k * C by positivity)
  calc
    _ = (Fintype.card (FrequencyChoices (frequencyBound Bs BD Bz k L) l) : ℝ)^2 := by
      simp only [Fintype.card_prod, Nat.cast_mul, pow_two]
    _ ≤ (Real.exp ((4 : ℝ)^l * A))^2 := by gcongr
    _ = Real.exp (2 * ((4 : ℝ)^l * A)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (actualFrequencyCost Bs BD Bz k * L) := by
      apply Real.exp_le_exp.mpr
      dsimp only [actualFrequencyCost]
      change 2 * ((4 : ℝ)^l * A) ≤ 4 * (4 : ℝ)^k * C * bulkScale k * L
      dsimp only [A] at hterm
      dsimp only [A]
      nlinarith

theorem eventually_actual_pair_card_le (Bs BD Bz : ℝ) {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop, ∀ l : ℕ, l ≤ k →
      (Fintype.card (FrequencyChoices (frequencyBound Bs BD Bz k L) l ×
        FrequencyChoices (frequencyBound Bs BD Bz k L) l) : ℝ) ≤ Real.exp (C * L) := by
  refine ⟨actualFrequencyCost Bs BD Bz k, actualFrequencyCost_pos Bs BD Bz hk, ?_⟩
  filter_upwards [(bulkSize_tendsto_atTop hk).eventually_ge_atTop 1,
    eventually_ge_atTop (0 : ℝ)] with L hm hL
  intro l hl
  exact actual_pair_card_le Bs BD Bz k L hL (by exact_mod_cast hm) hl

end Ostmann.Arithmetic.HistoryGiantFrequencyCount

end

end OAI
