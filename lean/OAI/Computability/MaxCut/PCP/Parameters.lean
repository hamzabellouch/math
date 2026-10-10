import Mathlib
import OAI.Computability.MaxCut.Model

namespace OAI

/-!
Scalar parameter selection for the v2 repetition rate.

These results concern powers of real numbers only. In particular, they do not
assert a parallel-repetition theorem for games. The exponent depends only on
the gap and the desired error; no alphabet or logical dimension occurs here.
-/

namespace MaxCutGames.Repetition

/-- The scalar rate appearing in the alphabet-independent repetition estimate. -/
noncomputable def dsRate (gap : ℝ) : ℝ := 1 - gap ^ 2 / 16

theorem dsRate_nonneg {gap : ℝ} (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1) :
    0 ≤ dsRate gap := by
  dsimp [dsRate]
  nlinarith

theorem dsRate_lt_one {gap : ℝ} (hgap : 0 < gap) : dsRate gap < 1 := by
  dsimp [dsRate]
  nlinarith [sq_pos_of_pos hgap]

/-- A scalar contraction admits a strictly positive exponent for every positive
target error. This lemma makes no assertion about any game value. -/
theorem exists_positive_power_lt {rate error : ℝ}
    (hrate₀ : 0 ≤ rate) (hrate₁ : rate < 1) (herror : 0 < error) :
    ∃ n : ℕ, 1 ≤ n ∧ rate ^ n < error := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hrate₀ hrate₁
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds herror)).exists
  refine ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), ?_⟩
  calc
    rate ^ (n + 1) = rate ^ n * rate := pow_succ _ _
    _ ≤ rate ^ n := mul_le_of_le_one_right (pow_nonneg hrate₀ n) hrate₁.le
    _ < error := hn

/-- Select the repetition count before choosing any alphabet. -/
theorem exists_dsRate_pow_le {gap error : ℝ}
    (hgap₀ : 0 < gap) (hgap₁ : gap < 1) (herror : 0 < error) :
    ∃ n : ℕ, 1 ≤ n ∧ dsRate gap ^ n ≤ error := by
  obtain ⟨n, hn, hbound⟩ := exists_positive_power_lt
    (dsRate_nonneg hgap₀.le hgap₁.le) (dsRate_lt_one hgap₀) herror
  exact ⟨n, hn, hbound.le⟩

theorem dsRate_one_div_eight_hundred :
    dsRate (1 / 800) = 1 - (1 : ℝ) / 10240000 := by
  norm_num [dsRate]

theorem dsRate_one_div_fifteen :
    dsRate (1 / 15) = 1 - (1 : ℝ) / 3600 := by
  norm_num [dsRate]

/-- The final soundness exponent depends only on `error`, even when the later
construction chooses its alphabet after this exponent. -/
theorem exists_final_repetition_count {error : ℝ} (herror : 0 < error) :
    ∃ n : ℕ, 1 ≤ n ∧ (1 - (1 : ℝ) / 10240000) ^ n ≤ error := by
  simpa only [dsRate_one_div_eight_hundred] using
    exists_dsRate_pow_le (gap := (1 / 800 : ℝ)) (by norm_num) (by norm_num) herror

/-- The preliminary constant-gap specialization of the same scalar rate. -/
theorem exists_preliminary_repetition_count {error : ℝ} (herror : 0 < error) :
    ∃ n : ℕ, 1 ≤ n ∧ (1 - (1 : ℝ) / 3600) ^ n ≤ error := by
  simpa only [dsRate_one_div_fifteen] using
    exists_dsRate_pow_le (gap := (1 / 15 : ℝ)) (by norm_num) (by norm_num) herror

end MaxCutGames.Repetition

end OAI
