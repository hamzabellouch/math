import Mathlib
import OAI.Computability.MaxCut.PCP.Parameters

namespace OAI

/-!
Scalar estimates for the last paragraph of the v2 construction. These lemmas
only perform the stated rounding/subdivision/repetition arithmetic; they do
not assume or assert an unproved repetition theorem or hardness result.
-/

namespace MaxCutGames.Explicit.FinishBounds

theorem exists_reciprocal_tolerance (ε : ℚ) (hε : 0 < ε) (t : Nat) (ht : 0 < t) :
    ∃ C : Nat, 200 ≤ C ∧ (0 : ℚ) < 1 / C ∧
      1 / (C : ℚ) ≤ 1 / 200 ∧ 1 / (C : ℚ) ≤ ε / t := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((t : ℚ) / ε)
  let C := n + 200
  have hC : (0 : ℚ) < C := by dsimp [C]; positivity
  have ht' : (0 : ℚ) < t := by exact_mod_cast ht
  have hCn : (n : ℚ) ≤ C := by dsimp [C]; exact_mod_cast Nat.le_add_right n 200
  have hbound : (t : ℚ) / ε < C := lt_of_lt_of_le hn hCn
  have hbudget : (t : ℚ) ≤ ε * C := by
    have he := (div_lt_iff₀ hε).mp hbound
    nlinarith
  refine ⟨C, by dsimp [C]; omega, one_div_pos.mpr hC, ?_, ?_⟩
  · apply one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 200)
    dsimp [C]
    exact_mod_cast Nat.le_add_left 200 n
  · apply (div_le_div_iff₀ hC ht').mpr
    simpa [mul_comm] using hbudget

theorem subdivision_completeness (vH vB d τ : ℝ)
    (hH : 1 - d ≤ vH)
    (hround : |vB - (1 - (1 - vH) / 4)| ≤ τ / 4) :
    1 - (d + τ) / 4 ≤ vB := by
  have h := (abs_le.mp hround).1
  linarith

theorem subdivision_soundness (vH vB τ : ℝ)
    (hH : vH ≤ 99 / 100) (hτ : τ ≤ 1 / 200)
    (hround : |vB - (1 - (1 - vH) / 4)| ≤ τ / 4) :
    vB ≤ 1 - 1 / 800 := by
  have h := (abs_le.mp hround).2
  linarith

/-- The full completeness loss after the coordinatewise product labeling. -/
theorem final_completeness (vB vG d τ ε₀ ε : ℝ) (t : Nat) (ht : 0 < t)
    (hB : 1 - (d + τ) / 4 ≤ vB)
    (hG : 1 - (t : ℝ) * (1 - vB) ≤ vG)
    (hd : d ≤ ε₀ / t) (hτ : τ ≤ ε₀ / t)
    (hε₀ : 0 ≤ ε₀) (hε : ε₀ ≤ ε) :
    1 - ε ≤ vG := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hd' := (le_div_iff₀ ht').mp hd
  have hτ' := (le_div_iff₀ ht').mp hτ
  have hB' : (t : ℝ) * (1 - vB) ≤ t * ((d + τ) / 4) :=
    mul_le_mul_of_nonneg_left (by linarith) ht'.le
  nlinarith

end MaxCutGames.Explicit.FinishBounds

/-!
The outer error parameters are fixed before the latent gadget or its alphabet.
We use the same positive reciprocal integer for the latent noise budget and
the rounding tolerance. This permitted specialization makes uniform occurrence
rounding an exact fixed-copy operation. The later parity error is chosen only
after the tuple length has been fixed.
-/

namespace MaxCutGames.ParameterSelection
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
end MaxCutGames.ParameterSelection

end OAI
