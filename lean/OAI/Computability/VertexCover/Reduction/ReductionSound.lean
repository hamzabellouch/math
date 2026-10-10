import Mathlib
import OAI.Computability.VertexCover.Analysis.PowerValueRepetition

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.ClauseProjection
open UniqueGames.Foundations
open LabelCover
noncomputable section

def baseGap : ℝ := (PCP.PCPIteration.finalClauseGap : ℝ) / 3

theorem baseGap_pos : 0 < baseGap := by
  exact div_pos (Rat.cast_pos.mpr PCP.PCPIteration.finalClauseGap_positive) (by norm_num)

theorem baseGap_le_third : baseGap ≤ 1/3 := by
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast PCP.TableGapReduction.finalClauseGap_le_one) (by norm_num)

def repetitionAlphabetBudget : ℝ := max 1 (Repetition.logTwo 14)

theorem repetitionAlphabetBudget_pos : 0 < repetitionAlphabetBudget :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

def repetitionBase : ℝ := 1 - baseGap ^ 3 / 6000

theorem repetitionBase_mem : 0 < repetitionBase ∧ repetitionBase < 1 := by
  have hp := baseGap_pos
  have hu := baseGap_le_third
  have hc : baseGap ^ 3 ≤ 1 := by
    calc
      _ ≤ (1 : ℝ)^3 := pow_le_pow_left₀ hp.le (by linarith) 3
      _ = 1 := by norm_num
  constructor
  · unfold repetitionBase; linarith
  · unfold repetitionBase; have : 0 < baseGap^3 / 6000 := by positivity
    linarith

theorem exists_repetition_length (σ : ℝ) (hσ : 0 < σ) :
    ∃ n : ℕ, repetitionBase ^ ((n : ℝ) / repetitionAlphabetBudget) < σ := by
  have hr := Real.rpow_lt_one repetitionBase_mem.1.le repetitionBase_mem.2
    (one_div_pos.mpr repetitionAlphabetBudget_pos)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hσ hr
  refine ⟨n, ?_⟩
  have he : (n : ℝ) / repetitionAlphabetBudget =
      (1 / repetitionAlphabetBudget) * (n : ℝ) := by ring
  rw [he, Real.rpow_mul repetitionBase_mem.1.le, Real.rpow_natCast]
  exact hn

def repetitionLength (σ : ℝ) (hσ : 0 < σ) : ℕ :=
  (exists_repetition_length σ hσ).choose

def reduction (σ : ℝ) (hσ : 0 < σ) (F : Target.Formula) : LabelCover :=
  (baseReduction F).parallelPower (repetitionLength σ hσ)

theorem reduction_alphabets (σ : ℝ) (hσ : 0 < σ) (F : Target.Formula) :
    (reduction σ hσ F).qU = 7 ^ repetitionLength σ hσ ∧
    (reduction σ hσ F).qV = 2 ^ repetitionLength σ hσ := ⟨rfl, rfl⟩

theorem reduction_complete (σ : ℝ) (hσ : 0 < σ) (F : Target.Formula)
    (hF : F.Satisfiable) :
    ∃ A : (reduction σ hσ F).Labeling, ∀ e, (reduction σ hσ F).Satisfies A e := by
  obtain ⟨A, hA⟩ := baseReduction_complete F hF
  exact ⟨_, LabelCover.repeat_perfect _ _ A hA⟩

theorem reduction_sound (σ : ℝ) (hσ : 0 < σ) (F : Target.Formula)
    (hF : ¬F.Satisfiable) : (reduction σ hσ F).value < σ := by
  let Φ := baseReduction F
  let n := repetitionLength σ hσ
  let : Nonempty (Fin Φ.qU) := ⟨⟨0, Φ.qU_pos⟩⟩
  let : Nonempty (Fin Φ.qV) := ⟨⟨0, Φ.qV_pos⟩⟩
  have hv : Φ.asGame.value ≤ 1 - baseGap := by
    change Φ.asGameValue ≤ 1 - baseGap
    rw [LabelCover.asGameValue_eq Φ (baseReduction_coherent F)]
    exact baseReduction_sound F hF
  have hb := Repetition.holenstein_repetition_value Φ.asGame n hv
    (by have := baseGap_pos; linarith : 1 - baseGap < 1)
    (le_max_left 1 (Repetition.logTwo 14))
    (show Repetition.logTwo ((Fintype.card (Fin Φ.qU) : ℝ) *
        (Fintype.card (Fin Φ.qV) : ℝ)) ≤ repetitionAlphabetBudget from by
      change Repetition.logTwo ((7 : ℝ) * 2) ≤ repetitionAlphabetBudget
      norm_num only [show (7 : ℝ) * 2 = 14 by norm_num]
      exact le_max_right _ _)
  have he : 1 - (1 - (1 - baseGap)) ^ 3 / 6000 = repetitionBase := by
    unfold repetitionBase; ring
  rw [he] at hb
  exact lt_of_le_of_lt ((LabelCover.power_value_le_repetition Φ
    (baseReduction_coherent F) n).trans hb)
    (exists_repetition_length σ hσ).choose_spec

end
end VertexCover.ClauseProjection


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
