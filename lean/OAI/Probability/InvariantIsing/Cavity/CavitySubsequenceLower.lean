import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Basic.Real.Basic

namespace OAI

/-! The subsequence principle needed to remove the compact Gibbs-array
limit from the eventual physical pressure increment inequality. -/

noncomputable section
open Filter

namespace InvariantIsing

theorem cavity_eventual_lower_of_subsequence (f : ℕ → ℝ) (L : ℝ)
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ ε>0, ∀ᶠ r in atTop, L-ε<f (φ (ψ r))) :
    ∀ ε>0, ∀ᶠ r in atTop, L-ε<f r := by
  intro ε hε
  by_contra hn
  have hf : ∃ᶠ r in atTop, ¬L-ε<f r := by
    simpa only [Filter.Frequently, not_not] using hn
  obtain ⟨φ,hφ,hbad⟩ := extraction_of_frequently_atTop hf
  obtain ⟨ψ,_hψ,hgood⟩ := h φ hφ
  obtain ⟨r,hr⟩ := (hgood ε hε).exists
  exact hbad (ψ r) hr

end InvariantIsing

end

end OAI
