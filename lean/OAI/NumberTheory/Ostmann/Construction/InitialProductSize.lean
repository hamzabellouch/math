import OAI.NumberTheory.Ostmann.Construction.FillerTargetScale
import OAI.NumberTheory.Ostmann.Construction.PrimeWordProduct

namespace OAI

/-! # The initial product has the prescribed logarithmic size -/

namespace Ostmann

open scoped BigOperators

theorem initial_product_log_error (k : ℕ) (τ Δ₀ J A : ℝ)
    (T e P₁ P₂ : Fin k → ℝ) (W₁ W₂ A₁ A₂ F₁ F₂ eA eF : ℝ)
    (hW₁ : |W₁ - J| ≤ 1) (hW₂ : |W₂ - J| ≤ 1)
    (hP₁ : ∀ i, |P₁ i - T i| ≤ e i) (hP₂ : ∀ i, |P₂ i - T i| ≤ e i)
    (hA₁ : |A₁ - A| ≤ eA) (hA₂ : |A₂ - A| ≤ eA)
    (hF₁ : |F₁ - fillerTarget k τ Δ₀ J A (∑ i, T i)| ≤ eF)
    (hF₂ : |F₂ - fillerTarget k τ Δ₀ J A (∑ i, T i)| ≤ eF) :
    |W₁ + W₂ + (∑ i, P₁ i) + (∑ i, P₂ i) + A₁ + A₂ + F₁ + F₂ -
      (1000 * (4 : ℝ) ^ k * τ + Δ₀)| ≤ 2 + 2 * (∑ i, e i) + 2 * eA + 2 * eF := by
  have hp₁ : |(∑ i, P₁ i) - ∑ i, T i| ≤ ∑ i, e i := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => hP₁ i))
  have hp₂ : |(∑ i, P₂ i) - ∑ i, T i| ≤ ∑ i, e i := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => hP₂ i))
  let d₁ := W₁ - J
  let d₂ := W₂ - J
  let d₃ := (∑ i, P₁ i) - ∑ i, T i
  let d₄ := (∑ i, P₂ i) - ∑ i, T i
  let d₅ := A₁ - A
  let d₆ := A₂ - A
  let d₇ := F₁ - fillerTarget k τ Δ₀ J A (∑ i, T i)
  let d₈ := F₂ - fillerTarget k τ Δ₀ J A (∑ i, T i)
  have heq : W₁ + W₂ + (∑ i, P₁ i) + (∑ i, P₂ i) + A₁ + A₂ + F₁ + F₂ -
      (1000 * (4 : ℝ) ^ k * τ + Δ₀) = d₁ + d₂ + d₃ + d₄ + d₅ + d₆ + d₇ + d₈ := by
    dsimp [d₁, d₂, d₃, d₄, d₅, d₆, d₇, d₈, fillerTarget]
    ring
  rw [heq]
  have h₂ := abs_add_le d₁ d₂
  have h₃ := abs_add_le (d₁ + d₂) d₃
  have h₄ := abs_add_le (d₁ + d₂ + d₃) d₄
  have h₅ := abs_add_le (d₁ + d₂ + d₃ + d₄) d₅
  have h₆ := abs_add_le (d₁ + d₂ + d₃ + d₄ + d₅) d₆
  have h₇ := abs_add_le (d₁ + d₂ + d₃ + d₄ + d₅ + d₆) d₇
  have h₈ := abs_add_le (d₁ + d₂ + d₃ + d₄ + d₅ + d₆ + d₇) d₈
  change |d₁| ≤ 1 at hW₁
  change |d₂| ≤ 1 at hW₂
  change |d₃| ≤ _ at hp₁
  change |d₄| ≤ _ at hp₂
  change |d₅| ≤ _ at hA₁
  change |d₆| ≤ _ at hA₂
  change |d₇| ≤ _ at hF₁
  change |d₈| ≤ _ at hF₂
  linarith

end Ostmann

end OAI
