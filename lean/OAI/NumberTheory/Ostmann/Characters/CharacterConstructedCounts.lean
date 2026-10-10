import OAI.NumberTheory.Ostmann.Construction.ConstructedCharacterCells
import OAI.NumberTheory.Ostmann.Characters.CharacterParameterChoice

namespace OAI

/-! # Every constructed list fits the chosen finite character budgets -/
namespace Ostmann
open scoped Classical BigOperators

theorem characterCellSlots_card {k : ℕ} (r : Fin k → ℕ) (f : ℕ) :
    Fintype.card (Σ v, Fin (characterCellSize r f v)) = (∑ j, r j) + 2 * k + f := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  simp [Fintype.sum_sum_type, characterCellSize, Nat.mul_comm, Nat.add_assoc]

theorem character_constructed_counts {P : Finset ℕ} {G : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P G c δ U k (T j)) :
    let N := characterTargetLabelBound c δ k
    let r := fun j => (w (some j)).indices.length
    let f := (w none).indices.length
    (∀ j, r j ≤ N) ∧ f ≤ N ∧
      Fintype.card (Σ v, Fin (characterCellSize r f v)) ≤ N + 2 * k ∧
      1 + ((∑ j, r j) + 2 * k) ≤ N + (k + 1) + (k + 1) := by
  intro N r f
  have h := character_target_label_bound w
  rw [Fintype.sum_option] at h
  change f + (∑ j, r j) ≤ N at h
  have hr (j) : r j ≤ ∑ j, r j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  refine ⟨fun j => (hr j).trans (by omega), by omega, ?_, by omega⟩
  rw [characterCellSlots_card]
  omega

theorem character_constructed_mass_budgets {P : Finset ℕ} {G : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P G c δ U k (T j))
    (C z : ℝ) (hC : 0 ≤ C)
    (hbudget : 4 * C * (characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) ≤ z) :
    let r := fun j => (w (some j)).indices.length
    let f := (w none).indices.length
    4 * Fintype.card (Σ v, Fin (characterCellSize r f v)) * C ≤ z ∧
      C * (∑ j, (r j : ℝ)) ≤ z / 4 := by
  intro r f
  have hcounts := character_constructed_counts w
  dsimp only at hcounts
  have hcard : Fintype.card (Σ v, Fin (characterCellSize r f v)) ≤
      characterTargetLabelBound c δ k + (k + 1) + (k + 1) := hcounts.2.2.1.trans (by omega)
  have hcardR : (Fintype.card (Σ v, Fin (characterCellSize r f v)) : ℝ) ≤
      (characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) := by exact_mod_cast hcard
  have hsum : (∑ j, r j) ≤ characterTargetLabelBound c δ k + (k + 1) + (k + 1) := by
    have hh := hcounts.2.2.2
    change 1 + ((∑ j, r j) + 2 * k) ≤ _ at hh
    omega
  have hsumR : (∑ j, (r j : ℝ)) ≤
      (characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) := by exact_mod_cast hsum
  constructor
  · have hh := mul_le_mul_of_nonneg_left hcardR (show 0 ≤ 4 * C by positivity)
    nlinarith only [hh, hbudget]
  · have hh := mul_le_mul_of_nonneg_left hsumR (show 0 ≤ 4 * C by positivity)
    nlinarith only [hh, hbudget]

end Ostmann

end OAI
