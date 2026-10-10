import OAI.Computability.UniqueGames.Games.FinishBoundsLemmas
import OAI.Computability.UniqueGames.Repetition.AnalyticCheegerLemmas

namespace OAI

section

/-!
The outer error parameters are fixed before the latent gadget or its alphabet.
We use the same positive reciprocal integer for the latent noise budget and
the rounding tolerance. This permitted specialization makes uniform occurrence
rounding an exact fixed-copy operation. The later parity error is chosen only
after the tuple length has been fixed.
-/

namespace UniqueGamesTheorem.ParameterSelection
noncomputable section

structure OuterParameters (ε δ : ℝ) where
  epsilon0 : ℚ
  delta0 : ℚ
  epsilon0_pos : 0 < epsilon0
  delta0_pos : 0 < delta0
  epsilon0_le : (epsilon0 : ℝ) ≤ ε
  delta0_le : (delta0 : ℝ) ≤ δ
  repetitions : ℕ
  repetitions_pos : 0 < repetitions
  soundness_rate : (1 - (1 : ℝ) / 10240000) ^ repetitions ≤ delta0
  copies : ℕ
  copies_large : 200 ≤ copies
  reciprocal_pos : (0 : ℚ) < 1 / copies
  reciprocal_small : 1 / (copies : ℚ) ≤ 1 / 200
  reciprocal_budget : 1 / (copies : ℚ) ≤ epsilon0 / repetitions

/-- Choose the alphabet-independent exponent and both rational budgets using
only the two prescribed real errors. -/
theorem exists_outerParameters (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    Nonempty (OuterParameters ε δ) := by
  obtain ⟨ε₀, hε₀, hεbound⟩ := exists_rat_btwn hε
  obtain ⟨δ₀, hδ₀, hδbound⟩ := exists_rat_btwn hδ
  have hεq : (0 : ℚ) < ε₀ := by exact_mod_cast hε₀
  have hδq : (0 : ℚ) < δ₀ := by exact_mod_cast hδ₀
  obtain ⟨t, ht, hrate⟩ := Repetition.exists_final_repetition_count hδ₀
  have htpos : 0 < t := ht
  obtain ⟨C, hC, hCpos, hCsmall, hCbudget⟩ :=
    Explicit.FinishBounds.exists_reciprocal_tolerance ε₀ hεq t htpos
  exact ⟨⟨ε₀, δ₀, hεq, hδq, hεbound.le, hδbound.le,
    t, htpos, hrate, C, hC, hCpos, hCsmall, hCbudget⟩⟩

namespace OuterParameters

variable {ε δ : ℝ} (P : OuterParameters ε δ)

def pStar : ℚ := 1 / P.copies

theorem pStar_pos : 0 < P.pStar := P.reciprocal_pos

theorem pStar_lt_one : P.pStar < 1 :=
  P.reciprocal_small.trans_lt (by norm_num)

theorem exists_parity_error (k : ℕ) (hk : 0 < k) :
    ∃ ξ : ℚ, 0 < ξ ∧ ξ < 1 / 100 ∧
      ξ < P.epsilon0 / (2 * k * P.repetitions) := by
  have hdenom : (0 : ℚ) < 2 * k * P.repetitions := by
    exact mul_pos (mul_pos (by norm_num) (by exact_mod_cast hk))
      (by exact_mod_cast P.repetitions_pos)
  let ξ := min (1 / 100 : ℚ) (P.epsilon0 / (2 * k * P.repetitions)) / 2
  have hmin : 0 < min (1 / 100 : ℚ) (P.epsilon0 / (2 * k * P.repetitions)) :=
    lt_min (by norm_num) (div_pos P.epsilon0_pos hdenom)
  refine ⟨ξ, div_pos hmin (by norm_num), ?_, ?_⟩
  · have hle := min_le_left (1 / 100 : ℚ) (P.epsilon0 / (2 * k * P.repetitions))
    dsimp [ξ]
    linarith
  · have hle := min_le_right (1 / 100 : ℚ) (P.epsilon0 / (2 * k * P.repetitions))
    dsimp [ξ]
    linarith

/-- Both matrix-test completeness losses fit the budget fixed before the
alphabet, for the later chosen positive tuple length. -/
theorem matrix_error_budget (k : ℕ) (hk : 0 < k) (ξ : ℚ)
    (hξ : ξ ≤ P.epsilon0 / (2 * k * P.repetitions)) :
    (k : ℚ) * ξ + P.pStar / 2 ≤ P.epsilon0 / P.repetitions := by
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have htq : (0 : ℚ) < P.repetitions := by exact_mod_cast P.repetitions_pos
  have hx := (le_div_iff₀ (mul_pos (mul_pos (by norm_num) hkq) htq)).mp hξ
  have hp := (le_div_iff₀ htq).mp P.reciprocal_budget
  apply (le_div_iff₀ htq).mpr
  dsimp [pStar]
  nlinarith

end OuterParameters
end
end UniqueGamesTheorem.ParameterSelection

end

end OAI
