import OAI.NumberTheory.Ostmann.Construction.PositiveWordBins

namespace OAI

/-! # Absolute endpoint means suffice for selecting the original character bin -/
namespace Ostmann
open scoped Classical BigOperators

theorem binnedWordAverage_total_norm_lower {A B : Type*} [Fintype A] [Fintype B] {n : ℕ}
    (μ : Fin n → A → ℝ) (F : Fin n → A → ℂ) (bin : (Fin n → A) → B)
    (δ : ℝ) (hδ : 0 ≤ δ) (hmean : ∀ i, δ ≤ ‖∑ a, (μ i a : ℂ) * F i a‖) :
    δ ^ n ≤ ‖∑ b, binnedWordAverage μ F bin b‖ := by
  rw [binnedWordAverage_sum, norm_prod]
  calc
    δ ^ n = ∏ _i : Fin n, δ := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hδ) (fun i _ => hmean i)

/-- This pigeonhole fixes the bin before the endpoint-dependent cell lists. -/
theorem common_large_word_bin_of_norm {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    {n : ℕ} (E : Finset ℕ) (μ : Fin n → A → ℝ) (F : ℕ → Fin n → A → ℂ)
    (bin : (Fin n → A) → B) (δ : ℝ) (hδ : 0 ≤ δ)
    (hmean : ∀ a ∈ E, ∀ i, δ ≤ ‖∑ p, (μ i p : ℂ) * F a i p‖) :
    ∃ b, ∃ S : Finset ℕ, S ⊆ E ∧ E.card ≤ Fintype.card B * S.card ∧
      ∀ a ∈ S, δ ^ n ≤ (Fintype.card B : ℝ) * ‖binnedWordAverage μ (F a) bin b‖ := by
  exact common_large_bin E (fun a => binnedWordAverage μ (F a) bin) (δ ^ n)
    (fun a ha => binnedWordAverage_total_norm_lower μ (F a) bin δ hδ (hmean a ha))

end Ostmann

end OAI
