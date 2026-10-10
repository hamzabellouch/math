import OAI.NumberTheory.Ostmann.Construction.FiniteTransfer

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistorySelectedRootErrorBudget
open Construction

theorem norm_cmean_le_of_mass_ne_zero {α : Type*} [Fintype α]
    (μ : FinitePrior α) (F : α → ℂ) (B : ℝ)
    (hF : ∀ a, μ.mass a ≠ 0 → ‖F a‖ ≤ B) : ‖μ.cmean F‖ ≤ B := by
  apply (μ.norm_cmean_le F).trans
  calc
    μ.mean (fun a => ‖F a‖) ≤ μ.mean (fun _ => B) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : μ.mass a = 0
      · simp only [ha,zero_mul,le_refl]
      · exact mul_le_mul_of_nonneg_left (hF a ha) (μ.mass_nonneg a)
    _ = B := μ.mean_const B

theorem nested_root_sum_error_le {α β ρ : Type*}
    [Fintype α] [Fintype β] [Fintype ρ]
    (μ : FinitePrior α) (ν : α → FinitePrior β)
    (F : α → β → ρ → ℂ) (δ : ℝ)
    (hF : ∀ a, μ.mass a ≠ 0 → ∀ b, (ν a).mass b ≠ 0 → ∀ r, ‖F a b r‖ ≤ δ) :
    ‖μ.cmean (fun a => (ν a).cmean (fun b => ∑ r, F a b r))‖ ≤ (Fintype.card ρ:ℝ)*δ := by
  apply norm_cmean_le_of_mass_ne_zero μ _ _
  intro a ha
  apply norm_cmean_le_of_mass_ne_zero (ν a) _ _
  intro b hb
  apply (norm_sum_le _ _).trans
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
    Finset.sum_le_sum (s := Finset.univ) (fun r _ => hF a ha b hb r)

end Ostmann.Arithmetic.HistorySelectedRootErrorBudget

end

end OAI
