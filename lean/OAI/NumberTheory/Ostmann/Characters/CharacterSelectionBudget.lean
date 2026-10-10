import OAI.NumberTheory.Ostmann.Characters.CharacterTargetCount
import OAI.NumberTheory.Ostmann.Characters.CharacterSelectionRate

namespace OAI

/-! # A single depth choice pays for all actual cell-selection codes -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def characterTargetLabelBound (c δ : ℝ) (k : ℕ) : ℕ :=
  ⌈cellRoleCountBound (256 / (δ * c)) k⌉₊

theorem character_target_label_bound {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j)) :
    (∑ j : Option (Fin k), (w j).indices.length) ≤ characterTargetLabelBound c δ k := by
  have hb : ((∑ j : Option (Fin k), (w j).indices.length) : ℝ) ≤
      cellRoleCountBound (256 / (δ * c)) k := by
    calc
      _ ≤ ∑ _j : Option (Fin k),
          256 / (δ * c) * Real.exp (2 * (k : ℝ) / 10000) :=
        Finset.sum_le_sum (fun j _ => (w j).length_le)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_option, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_add, Nat.cast_one, cellRoleCountBound, cellRoleEpsilon]
        rw [show 2 * (k : ℝ) / 10000 = 2 * (1 / 10000 : ℝ) * k by ring]
        ring
  exact_mod_cast hb.trans (Nat.le_ceil _)

theorem character_selection_code_bound (c δ : ℝ) (k : ℕ) (hc : 0 < c) (hδ : 0 < δ) :
    ((characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) : ℝ) ≤
      cellRoleCountBound (256 / (δ * c) + 3) k := by
  have hpos : 0 ≤ cellRoleCountBound (256 / (δ * c)) k :=
    cellRoleCountBound_nonneg (by positivity) k
  have hceil := Nat.ceil_lt_add_one hpos
  have hp : 1 ≤ Real.exp (2 * cellRoleEpsilon * k) :=
    Real.one_le_exp_iff.mpr (by unfold cellRoleEpsilon; positivity)
  have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 3 * ((k : ℝ) + 1) by positivity)
  have hk := Nat.cast_nonneg (α := ℝ) k
  change (characterTargetLabelBound c δ k : ℝ) < _ at hceil
  unfold cellRoleCountBound at hceil ⊢
  simp only [Nat.cast_add, Nat.cast_one]
  nlinarith only [hceil, hh, hk]

/-- This threshold precedes the density increment and is uniform over the
resulting depth, endpoint tests, target values and selected word lengths. -/
theorem character_selection_depth (c δ C b : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (hb : 0 < b) (Kmin : ℕ) :
    ∃ K : ℕ, Kmin ≤ K ∧ ∀ k : ℕ, K ≤ k →
      1 ≤ k ∧ 1 ≤ cellRoleScale k ∧
      C + 20 * Real.log (cellRoleScale k) ≤ (k : ℝ) * Real.log 2 - 1 ∧
      ((characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) : ℝ) ≤ b * cellRoleScale k := by
  obtain ⟨K, hK, hdepth⟩ := character_depth_cutoff C (256 / (δ * c) + 3) b hb Kmin
  refine ⟨K, hK, ?_⟩
  intro k hk
  obtain ⟨hk1, hz, he, hcount⟩ := hdepth k hk
  exact ⟨hk1, hz, he, (character_selection_code_bound c δ k hc hδ).trans hcount⟩

end Ostmann

end OAI
