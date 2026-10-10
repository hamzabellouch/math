import OAI.NumberTheory.Ostmann.Characters.CharacterTargetSelectionRate
import OAI.NumberTheory.Ostmann.Construction.CommonAnchorCells

namespace OAI

/-! # One endpoint family has common anchors and common target-cell lists -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- The word bin has already been fixed. We fix the anchors and then the
actual shell/list data without changing it, retaining an explicit rate. -/
theorem eventual_common_character_selection (k N : ℕ) (C z : ℝ)
    (hC : 0 ≤ C) (hz : 1 ≤ z) (hsize : (N + (k + 1) + (k + 1) : ℕ) ≤ z) :
    ∀ᶠ L : ℝ in atTop, ∀ (B : ℕ) (m X A : ℝ),
      (B + 1 : ℕ) ≤ Real.exp (C * L) → z * L ≤ 2 * m →
      ∀ (E : Finset ℕ), E.Nonempty → Real.sqrt X * Real.exp (-A * m) ≤ E.card →
      ∀ (P : Finset ℕ) (F : ℕ → ℕ → ℂ) (c δ U : ℝ)
        (anchor : ℕ → (Fin k × Bool) → ℕ) (T : ℕ → Option (Fin k) → ℝ)
        (w : ∀ a j, CharacterTargetWord P (F a) c δ U k (T a j)),
      0 < c → 0 < δ → 5 * k ≤ B → (∀ p ∈ P, primeLogIndex p ≤ B) →
      (∀ a ∈ E, ∀ j, anchor a j ≤ B) →
      (∀ a ∈ E, (∑ j : Option (Fin k), (w a j).indices.length) ≤ N) →
      ∃ a₀ ∈ E, ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
        Real.sqrt X * Real.exp (-(A + 4 * C + 4) * m) ≤ S.card ∧
        ∀ a ∈ S, anchor a = anchor a₀ ∧ ∀ j,
          (w a j).indices = (w a₀ j).indices ∧ ∀ h, (w a j).cell h = (w a₀ j).cell h := by
  filter_upwards [eventual_common_character_target_cells k N C z hC hz hsize,
    eventually_ge_atTop (0 : ℝ)] with L hselect hL
  intro B m X A hB hm E hE hEcount P F c δ U anchor T w hc hδ hk hP hanchor hN
  obtain ⟨a₁, _, E₁, hE₁E, hE₁, hcard, hsame⟩ :=
    common_bounded_anchor_cells E hE k B anchor hanchor
  have hsmallN : ((2 * k : ℕ) : ℝ) ≤ (N + (k + 1) + (k + 1) : ℕ) := by
    exact_mod_cast (show 2 * k ≤ N + (k + 1) + (k + 1) by omega)
  have hsmall : (2 * k : ℕ) ≤ z := hsmallN.trans hsize
  have hcount₁ : Real.sqrt X * Real.exp (-(A + 2 * C) * m) ≤ E₁.card :=
    cell_group_endpoint_rate E.card E₁.card _ X A (2 * C) m
      (by exact_mod_cast hcard) (anchor_cell_cost k B C L z m hC hL hsmall hB hm) hEcount
  obtain ⟨S, hSE₁, hS, hScount, hcodes⟩ := hselect B m X (A + 2 * C) hB hm E₁ hE₁ hcount₁
    P F c δ U T w hc hδ hk hP (fun a ha => hN a (hE₁E ha))
  obtain ⟨a₀, ha₀⟩ := hS
  refine ⟨a₀, hE₁E (hSE₁ ha₀), S, hSE₁.trans hE₁E, ⟨a₀, ha₀⟩, ?_, ?_⟩
  · rw [show A + 4 * C + 4 = (A + 2 * C) + 2 * (C + 2) by ring]
    exact hScount
  · intro a ha
    exact ⟨(hsame a (hSE₁ ha)).trans (hsame a₀ (hSE₁ ha₀)).symm,
      hcodes a ha a₀ ha₀⟩

end Ostmann

end OAI
