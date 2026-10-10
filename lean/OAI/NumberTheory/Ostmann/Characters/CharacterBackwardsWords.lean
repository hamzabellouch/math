import OAI.NumberTheory.Ostmann.Characters.CharacterTargetRanges
import OAI.NumberTheory.Ostmann.Characters.CharacterSelectionBudget

namespace OAI

/-! # Whole-shell words for the actual backwards pivot and filler targets -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- The words are constructed after fixing the bin and anchor indices. The
large-parameter threshold is uniform over those choices and the endpoint test. -/
theorem PublishedProgressionInput.character_backwards_words
    (P0 : PublishedProgressionInput) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 20000 ≤ k →
      C ≤ Real.exp ((k : ℝ) / 10000) → ∀ (B z α : ℝ),
      0 ≤ B → 1 ≤ z → 0 < α →
      ∀ᶠ L : ℝ in atTop, ∀ (U τ J : ℝ) (m : ℕ),
      α * L ≤ U → U ≤ Real.log τ → Real.log τ ≤ U + 2 * (k : ℝ) / 10000 →
      0 < τ → (m : ℝ) ≤ z * L → τ / 2 ≤ J → J ≤ 4 * τ →
      ∀ (a : Fin k → Bool → ℕ),
      (∀ j, (a j false : ℝ) + a j true ≤ 4 * τ) →
      ∀ (P : Finset ℕ) (F : ℕ → ℂ), (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, ‖F p‖ ≤ 1) →
      (∀ u v : ℝ, U ≤ u → v ≤ U + 5 * k → (k : ℝ) / 10000 ≤ v - u →
        ∃ j : ℕ, u ≤ U + j ∧ U + j + 1 ≤ v ∧
          c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) →
      (∀ j : ℕ, j ≤ 5 * k → c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ →
        (∀ p ∈ loglogShell P (U + j),
          Real.log (p : ℝ) ≤ (1000 * (4 : ℝ) ^ k * τ) / 4) →
        δ * (∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) ≤
          ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ * (F p).re) →
      let TP := characterPivotTarget k J (fun j => (a j false : ℝ) + a j true)
        (fun j => characterPivotGap B z m j.val)
      let TF := characterFillerTarget (1000 * (4 : ℝ) ^ k * τ)
        (characterBaseGap B z m) J TP (fun j b => (a j b : ℝ))
      ∃ w : ∀ j : Option (Fin k), CharacterTargetWord P F c δ U k (j.elim TF TP),
        (∀ j, 0 < (w j).indices.length) ∧
        (∑ j : Option (Fin k), (w j).indices.length) ≤ characterTargetLabelBound c δ k := by
  obtain ⟨C, hC, hwords⟩ := P0.character_target_words c δ hc hδ
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hwords
  refine ⟨C, hC, ?_⟩
  intro k hk hCk B z α hB hz hα
  have hu : ∀ᶠ L : ℝ in atTop, U₀ ≤ α * L :=
    (tendsto_id.const_mul_atTop hα).eventually (eventually_ge_atTop U₀)
  filter_upwards [hu, eventual_character_target_gaps k B z α hB hz hα] with L hU hg
  intro U τ J m hUL hτlo hτhi hτ hm hJlo hJhi a ha P F hP hF hrich htest TP TF
  have hexp : Real.exp (α * L) ≤ τ := by
    exact (Real.exp_le_exp.mpr (hUL.trans hτlo)).trans_eq (Real.exp_log hτ)
  have hgap := hg m τ (Nat.cast_nonneg m) hm hexp
  have hranges := character_constructed_target_ranges k (by omega) J τ
    (characterBaseGap B z m) (fun j b => (a j b : ℝ))
    (fun j => characterPivotGap B z m j.val) hτ hJlo hJhi
    (fun j => ⟨by positivity, ha j⟩) (fun j => hgap.2.2 j.val j.isLt)
    ⟨hgap.1, hgap.2.1⟩
  obtain ⟨w, hw, _⟩ := hU₀ U (hU.trans hUL) k hk hCk τ hτ hτlo hτhi
    P F hP hF hrich htest (fun j : Option (Fin k) => j.elim TF TP)
    (fun j => (hranges j).1) (fun j => (hranges j).2)
  exact ⟨w, hw, character_target_label_bound w⟩

end Ostmann

end OAI
