import OAI.NumberTheory.Ostmann.Preliminaries.DensityStability

namespace OAI

open Erdos970

namespace Ostmann.QuadraticCenter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def GoodBiasApproximation (δ σ eA eD : ℝ) : Prop :=
  1 / 3 ≤ σ ∧ σ ≤ 2 / 3 ∧ eA ≤ δ / 8 ∧ eD ≤ δ / 8

lemma badBiasApproximation_cost {δ : ℝ} (hδ : 0 < δ) (σ eA eD : ℝ)
    (hbad : ¬ GoodBiasApproximation δ σ eA eD) :
    1 ≤ 36 * (σ - 1 / 2) ^ 2 + (64 / δ ^ 2) * (eA ^ 2 + eD ^ 2) := by
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hcost0 : 0 ≤ (64 / δ ^ 2) * (eA ^ 2 + eD ^ 2) := by positivity
  by_cases hlo : 1 / 3 ≤ σ
  · by_cases hhi : σ ≤ 2 / 3
    · have herr : δ / 8 < eA ∨ δ / 8 < eD := by
        by_contra hn
        push Not at hn
        exact hbad ⟨hlo, hhi, hn.1, hn.2⟩
      have hsq : δ ^ 2 ≤ 64 * (eA ^ 2 + eD ^ 2) := by
        rcases herr with he | he
        · nlinarith [sq_nonneg (eA - δ / 8), sq_nonneg eD]
        · nlinarith [sq_nonneg (eD - δ / 8), sq_nonneg eA]
      have hlarge : 1 ≤ (64 / δ ^ 2) * (eA ^ 2 + eD ^ 2) := by
        rw [div_mul_eq_mul_div]
        exact (le_div_iff₀ hδ2).mpr (by simpa using hsq)
      nlinarith [sq_nonneg (σ - 1 / 2)]
    · have hs : 2 / 3 < σ := lt_of_not_ge hhi
      nlinarith [sq_nonneg (σ - 2 / 3)]
  · have hs : σ < 1 / 3 := lt_of_not_ge hlo
    nlinarith [sq_nonneg (σ - 1 / 3)]

theorem goodBiasApproximation_weight {α : Type*} (P : Finset α)
    (w σ eA eD : α → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hw : ∀ p ∈ P, 0 ≤ w p) :
    (∑ p ∈ P, w p) ≤
      (∑ p ∈ P with GoodBiasApproximation δ (σ p) (eA p) (eD p), w p) +
      36 * (∑ p ∈ P, w p * (σ p - 1 / 2) ^ 2) +
      (64 / δ ^ 2) * ((∑ p ∈ P, w p * eA p ^ 2) +
        (∑ p ∈ P, w p * eD p ^ 2)) := by
  classical
  have hpoint : ∀ p ∈ P, w p ≤
      (if GoodBiasApproximation δ (σ p) (eA p) (eD p) then w p else 0) +
      36 * (w p * (σ p - 1 / 2) ^ 2) +
      (64 / δ ^ 2) * (w p * eA p ^ 2) + (64 / δ ^ 2) * (w p * eD p ^ 2) := by
    intro p hp
    have hwp := hw p hp
    by_cases hg : GoodBiasApproximation δ (σ p) (eA p) (eD p)
    · rw [ite_eq_left hg]
      have h1 : 0 ≤ 36 * (w p * (σ p - 1 / 2) ^ 2) := by positivity
      have h2 : 0 ≤ (64 / δ ^ 2) * (w p * eA p ^ 2) := by positivity
      have h3 : 0 ≤ (64 / δ ^ 2) * (w p * eD p ^ 2) := by positivity
      linarith
    · rw [ite_eq_right hg]
      have h := mul_le_mul_of_nonneg_left
        (badBiasApproximation_cost hδ (σ p) (eA p) (eD p) hg) hwp
      convert h using 1 <;> ring
  have h := Finset.sum_le_sum hpoint
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_filter,
    mul_add, add_assoc] using h

end Ostmann.QuadraticCenter

end OAI
