import OAI.NumberTheory.TwoPoint.Walks.SelectedPairCosts

namespace OAI

/-! The raw lower bound for an actual phase-selected family. All losses are
the explicit prime-cost, logarithmic-bin and finite-prefix errors. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma selectedRawMean_lower_bound {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : OneBounded f) (hg : OneBounded g)
    (A : Finset (ℕ × ℕ)) (T : ℕ × ℕ → ℝ) (h : ℕ)
    (X η mass γ : ℝ) (hX : 0 < X) (hη : 0 ≤ η) (hmass : 0 ≤ mass) (hγ : 0 ≤ γ)
    (hpos : ∀ dq ∈ A, 0 < dq.1 * dq.2)
    (hlo : ∀ dq ∈ A, X * Real.exp (-η) ≤ T dq / (dq.1 * dq.2 : ℕ))
    (hhi : ∀ dq ∈ A, T dq / (dq.1 * dq.2 : ℕ) ≤ X)
    (hT : ∀ dq ∈ A, X ≤ T dq)
    (hweight : (∑ dq ∈ A, complexPairWeight dq) ≤ mass)
    (hphase : mass / 8 ≤ ‖selectedRawCoefficient A f g‖)
    (hcost : (∑ dq ∈ A, complexPairWeight dq *
      ∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ)) ≤ γ * mass / 128)
    (hsmall : η ≤ γ / 128)
    (hlong : (mass + ∑ dq ∈ A,
      4 * actualPaddingCoefficient dq.2 * (dq.1 * dq.2).primeFactors.card) / X ≤
        γ * mass / 64)
    (hbias : γ ≤ ‖positivePrefix (fun n => f n * g (n + h)) ⌊X⌋₊ / (X : ℂ)‖) :
    γ * mass / 16 ≤ ‖selectedRawMean A T f g h‖ := by
  apply raw_norm_lower_bound _ (selectedRawCoefficient A f g)
    (positivePrefix (fun n => f n * g (n + h)) ⌊X⌋₊ / (X : ℂ)) mass γ
    hmass hγ hphase hbias
  have hc := (selectedRawMean_comparison hfm hgm hf hg A T h X η hpos hX hη hlo hhi).trans
    (selectedRawComparison_cost_bound A T X η hX hT)
  have hw := mul_le_mul_of_nonneg_left hweight
    (show 0 ≤ 2 * η + 1 / X by positivity)
  have he := mul_le_mul_of_nonneg_right hsmall hmass
  rw [add_div] at hlong
  simp only [div_eq_mul_inv] at hc hw he hcost hlong ⊢
  nlinarith only [hc, hw, he, hcost, hlong]

end TwoPointCorrelations

end OAI
