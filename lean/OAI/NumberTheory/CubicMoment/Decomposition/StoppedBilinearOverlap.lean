import OAI.NumberTheory.CubicMoment.Decomposition.StoppedMixedModel
import OAI.NumberTheory.CubicMoment.Estimates.ModelOverlapBound
import OAI.NumberTheory.CubicMoment.Estimates.OverlapScale

namespace OAI

/-! Shared-prime incidence for the literal support. Inactive stopped
coefficients contribute zero, so only active rows require roughness. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma active_noncoprime_bipartite_energy (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) {Y R Q : ℝ} (hY : 0 ≤ Y) (hR : 0 < R) (hQ : 0 ≤ Q)
    (hP : ∀ a ∈ P, a ≠ 0 ∧ norm a ≤ Y)
    (hB : ∀ b ∈ B, primary b ∧ Squarefree b)
    (hn : ∀ b ∈ B, β b ≠ 0 → ((primaryPrimeFactors b).card:ℝ) ≤ Q)
    (hrough : ∀ b ∈ B, β b ≠ 0 → ∀ p ∈ primaryPrimeFactors b, R ≤ norm p) :
    (∑ a ∈ P, ∑ b ∈ B, if ¬IsCoprime a b then ‖α a‖*‖β b‖ else 0)^2 ≤
      ((B.card:ℝ)*∑ a ∈ P, ‖α a‖^2)*
        (Q*(18*Y/R)*∑ b ∈ B, ‖β b‖^2) := by
  let rel := fun a b : Eisenstein => ¬IsCoprime a b ∧ β b ≠ 0
  have hr (a : Eisenstein) (_ha : a ∈ P) :
      ((B.filter (rel a)).card:ℝ) ≤ B.card := by
    exact_mod_cast Finset.card_filter_le B (rel a)
  have hc (b : Eisenstein) (hb : b ∈ B) :
      ((P.filter (fun a => rel a b)).card:ℝ) ≤ Q*(18*Y/R) := by
    by_cases hz : β b = 0
    · simp only [rel,hz,ne_eq,not_true_eq_false,and_false,Finset.filter_false,
        Finset.card_empty,Nat.cast_zero]
      positivity
    · have he : P.filter (fun a => rel a b) = P.filter (fun a => ¬IsCoprime b a) := by
        ext a
        simp only [Finset.mem_filter,rel,hz,ne_eq,not_false_eq_true,and_true,isCoprime_comm]
      rw [he]
      exact (noncoprime_row_card_le P hY hR hP (hB b hb).1 (hB b hb).2
        (hrough b hb hz)).trans
          (mul_le_mul_of_nonneg_right (hn b hb hz) (by positivity))
  have he := bipartite_sum_sq_le P B rel (fun a => ‖α a‖) (fun b => ‖β b‖)
    (Nat.cast_nonneg _) (show 0 ≤ Q*(18*Y/R) by positivity) hr hc
  have hs : (∑ a ∈ P, ∑ b ∈ B, if rel a b then ‖α a‖*‖β b‖ else 0) =
      ∑ a ∈ P, ∑ b ∈ B, if ¬IsCoprime a b then ‖α a‖*‖β b‖ else 0 := by
    apply Finset.sum_congr rfl
    intro a _ha
    apply Finset.sum_congr rfl
    intro b _hb
    by_cases hz : β b = 0 <;> simp [rel,hz]
  rwa [hs] at he

lemma active_modelOverlap_norm_sq_le (P B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (u : ℝ) {A L Y R Q : ℝ} (hA : 0 < A) (hL : 0 < L)
    (hY : 0 ≤ Y) (hR : 0 < R) (hQ : 0 ≤ Q)
    (hP : ∀ a ∈ P, a ≠ 0 ∧ A ≤ norm a ∧ norm a ≤ Y)
    (hB : ∀ b ∈ B, primary b ∧ Squarefree b ∧ L ≤ norm b)
    (hn : ∀ b ∈ B, β b ≠ 0 → ((primaryPrimeFactors b).card:ℝ) ≤ Q)
    (hrough : ∀ b ∈ B, β b ≠ 0 → ∀ p ∈ primaryPrimeFactors b, R ≤ norm p) :
    ‖modelOverlap P B α β u‖^2 ≤ (cStar*A^(-1/6:ℝ)*L^(-1/6:ℝ))^2*
      (((B.card:ℝ)*∑ a ∈ P, ‖α a‖^2)*(Q*(18*Y/R)*∑ b ∈ B, ‖β b‖^2)) := by
  have hh := norm_modelOverlap_le P B α β u hA hL
    (fun a ha => (hP a ha).2.1) (fun b hb => (hB b hb).2.2)
  have he := active_noncoprime_bipartite_energy P B α β hY hR hQ
    (fun a ha => ⟨(hP a ha).1,(hP a ha).2.2⟩)
    (fun b hb => ⟨(hB b hb).1,(hB b hb).2.1⟩) hn hrough
  apply (pow_le_pow_left₀ (_root_.norm_nonneg _) hh 2).trans
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left he (sq_nonneg _)

end CubicFirstMoment

end

end OAI
