import OAI.NumberTheory.Ostmann.Characters.CharacterTargetCode
import OAI.NumberTheory.Ostmann.Tree.CellGroupExponentialCost

namespace OAI

/-! # Fixing actual target words preserves exponentially many endpoints -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_common_character_target_cells (k N : ℕ) (C z : ℝ)
    (hC : 0 ≤ C) (hz : 1 ≤ z) (hsize : (N + (k + 1) + (k + 1) : ℕ) ≤ z) :
    ∀ᶠ L : ℝ in atTop, ∀ (B : ℕ) (m X A : ℝ),
      (B + 1 : ℕ) ≤ Real.exp (C * L) → z * L ≤ 2 * m →
      ∀ (E : Finset ℕ), E.Nonempty → Real.sqrt X * Real.exp (-A * m) ≤ E.card →
      ∀ (P : Finset ℕ) (F : ℕ → ℕ → ℂ) (c δ U : ℝ)
        (T : ℕ → Option (Fin k) → ℝ)
        (w : ∀ a j, CharacterTargetWord P (F a) c δ U k (T a j)),
      0 < c → 0 < δ → 5 * k ≤ B → (∀ p ∈ P, primeLogIndex p ≤ B) →
      (∀ a ∈ E, (∑ j : Option (Fin k), (w a j).indices.length) ≤ N) →
      ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
        Real.sqrt X * Real.exp (-(A + 2 * (C + 2)) * m) ≤ S.card ∧
        ∀ a ∈ S, ∀ b ∈ S, ∀ j,
          (w a j).indices = (w b j).indices ∧ ∀ h, (w a j).cell h = (w b j).cell h := by
  filter_upwards [eventual_cell_group_cost (N + (k + 1)) (k + 1) C z hC hz hsize] with L hcost
  intro B m X A hB hm E hE hcount P F c δ U T w hc hδ hk hP hN
  obtain ⟨S, hSE, hS, hcard, hsame⟩ := common_character_target_cells E hE P F c δ U
    k N B T w hc hδ hk hP hN
  refine ⟨S, hSE, hS, ?_, hsame⟩
  apply cell_group_endpoint_rate E.card S.card _ X A (2 * (C + 2)) m
    (by exact_mod_cast hcard) (hcost B m hB hm) hcount

end Ostmann

end OAI
