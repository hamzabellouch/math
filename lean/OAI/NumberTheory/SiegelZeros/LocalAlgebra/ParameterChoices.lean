import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.ParameterChoices

theorem first_term_bound {r : ℝ} (hr : r ≤ 1 / 12) :
    (3 / 4 : ℝ) * (1 + r) ≤ 13 / 16 := by
  linarith

theorem choose_weight (K : ℝ) :
    ∃ H : ℕ, 2 ≤ H ∧ ∀ r : ℝ, r ≤ K / (H : ℝ) → r ≤ 1 / 12 := by
  obtain ⟨H, hH⟩ := exists_nat_gt (max (2 : ℝ) (12 * K))
  have hHtwo : (2 : ℝ) < H := lt_of_le_of_lt (le_max_left _ _) hH
  have hHK : 12 * K < (H : ℝ) := lt_of_le_of_lt (le_max_right _ _) hH
  have hHpos : (0 : ℝ) < H := by linarith
  have hHnat : 2 ≤ H := by exact_mod_cast (le_of_lt hHtwo)
  refine ⟨H, hHnat, ?_⟩
  intro r hr
  have hratio : K / (H : ℝ) ≤ 1 / 12 := by
    apply (div_le_iff₀ hHpos).2
    linarith
  exact hr.trans hratio

theorem choose_exponent (C : ℝ) (hC : 0 ≤ C) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ r : ℝ, r ≤ 1 / 12 →
      (C + (1 + r) / 2) * 3 / (4 * γ) < 1 / 16 := by
  refine ⟨12 * (C + 13 / 24) + 1, by linarith, ?_⟩
  intro r hr
  have hden : 0 < 4 * (12 * (C + 13 / 24) + 1) := by linarith
  apply (div_lt_iff₀ hden).2
  linarith

theorem choose_exponent_quotient (C : ℝ) (hC : 0 ≤ C) :
    ∃ γ : ℝ, 0 < γ ∧ (C + 13 / 24) / (4 * γ / 3) < 1 / 16 := by
  obtain ⟨γ, hγ, hb⟩ := choose_exponent C hC
  refine ⟨γ, hγ, ?_⟩
  have h := hb (1 / 12) le_rfl
  have hp : 0 < 4 * γ := by positivity
  have hm := (div_lt_iff₀ hp).1 h
  apply (div_lt_iff₀ (show 0 < 4 * γ / 3 by positivity)).2
  linarith

theorem choose_weight_then_exponent (K : ℝ) :
    ∃ H : ℕ, 2 ≤ H ∧ ∀ C : ℝ, 0 ≤ C →
      ∃ γ : ℝ, 0 < γ ∧ ∀ r : ℝ, r ≤ K / (H : ℝ) →
        (3 / 4 : ℝ) * (1 + r) ≤ 13 / 16 ∧
        (C + (1 + r) / 2) * 3 / (4 * γ) < 1 / 16 := by
  obtain ⟨H, hH, hratio⟩ := choose_weight K
  refine ⟨H, hH, ?_⟩
  intro C hC
  obtain ⟨γ, hγ, hsecond⟩ := choose_exponent C hC
  refine ⟨γ, hγ, ?_⟩
  intro r hr
  exact ⟨first_term_bound (hratio r hr), hsecond r (hratio r hr)⟩

theorem explicit_pivot_weight :
    (192 * (4 * 97 ^ 2) : ℝ) / 86713344 = 1 / 12 := by
  norm_num

theorem allowances_sum : (13 / 16 : ℝ) + 1 / 16 = 7 / 8 := by norm_num

end WeightedTorusJets.ParameterChoices

end

end SiegelZeros

end OAI
