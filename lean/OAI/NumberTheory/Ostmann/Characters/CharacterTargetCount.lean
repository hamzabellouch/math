import OAI.NumberTheory.Ostmann.Characters.CharacterTargetWords
import OAI.NumberTheory.Ostmann.Characters.CharacterDepthChoice
import OAI.NumberTheory.Ostmann.Characters.AnchorNonbulkBudget

namespace OAI

/-! # The actual target-word certificates satisfy the uniform cell-role bound -/
namespace Ostmann
open scoped Classical BigOperators

/-- The filler is counted once and there are exactly two anchors per step. -/
theorem character_target_cell_count {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j)) :
    (((∑ j : Fin k, (w (some j)).indices.length) + (w none).indices.length + 2 * k : ℕ) : ℝ) ≤
      cellRoleCountBound (256 / (δ * c) + 2) k := by
  let p := Real.exp (2 * (k : ℝ) / 10000)
  have hp : 1 ≤ p := Real.one_le_exp_iff.mpr (by positivity)
  have ht : (∑ j : Option (Fin k), ((w j).indices.length : ℝ)) ≤
      ((k : ℝ) + 1) * (256 / (δ * c) * p) := by
    calc
      _ ≤ ∑ _j : Option (Fin k), (256 / (δ * c) * p) :=
        Finset.sum_le_sum (fun j _ => (w j).length_le)
      _ = _ := by simp
  rw [Fintype.sum_option] at ht
  have hk := Nat.cast_nonneg (α := ℝ) k
  have hh := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 * ((k : ℝ) + 1))
  unfold cellRoleCountBound cellRoleEpsilon
  have he : 2 * (1 / 10000 : ℝ) * k = 2 * (k : ℝ) / 10000 := by ring
  rw [he]
  change _ ≤ (256 / (δ * c) + 2) * ((k : ℝ) + 1) * p
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum]
  nlinarith only [ht, hk, hh]

/-- The extra top slot in the matching complement fits the same role budget
with one further absolute unit. -/
theorem character_target_active_count {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j)) :
    ((1 + ((∑ j : Fin k, (w (some j)).indices.length) + 2 * k) : ℕ) : ℝ) ≤
      cellRoleCountBound (256 / (δ * c) + 3) k := by
  have hc := character_target_cell_count w
  have hp : 1 ≤ Real.exp (2 * cellRoleEpsilon * k) :=
    Real.one_le_exp_iff.mpr (by unfold cellRoleEpsilon; positivity)
  have hk := Nat.cast_nonneg (α := ℝ) k
  have hf := Nat.cast_nonneg (α := ℝ) (w none).indices.length
  have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ (k : ℝ) + 1 by positivity)
  unfold cellRoleCountBound at hc ⊢
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum] at hc ⊢
  nlinarith only [hc, hk, hf, hh]

theorem character_target_total_with_top {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j)) :
    ((1 + ((∑ j : Fin k, (w (some j)).indices.length) + (w none).indices.length + 2 * k) : ℕ) : ℝ) ≤
      cellRoleCountBound (256 / (δ * c) + 3) k := by
  have hc := character_target_cell_count w
  have hp : 1 ≤ Real.exp (2 * cellRoleEpsilon * k) :=
    Real.one_le_exp_iff.mpr (by unfold cellRoleEpsilon; positivity)
  have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ (k : ℝ) + 1 by positivity)
  have hk := Nat.cast_nonneg (α := ℝ) k
  unfold cellRoleCountBound at hc ⊢
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum] at hc ⊢
  nlinarith only [hc, hh, hk]

/-- The depth is chosen before the endpoints, targets or their words. Every
resulting actual list meets the same prescribed normalization budget. -/
theorem eventual_character_target_role_budget (c δ C ε : ℝ)
    (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in Filter.atTop, ∀ (P : Finset ℕ) (F : ℕ → ℂ) (U : ℝ)
      (T : Option (Fin k) → ℝ) (w : ∀ j, CharacterTargetWord P F c δ U k (T j)),
      4 * C * (1 + ((∑ j : Fin k, (w (some j)).indices.length) +
        (w none).indices.length + 2 * k) : ℕ) ≤ ε * cellRoleScale k := by
  filter_upwards [eventual_anchor_role_budget (256 / (δ * c) + 3) C ε hC hε] with k hk
  intro P F U T w
  exact hk _ (character_target_total_with_top w)

end Ostmann

end OAI
