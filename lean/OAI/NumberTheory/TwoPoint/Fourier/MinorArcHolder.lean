import OAI.NumberTheory.TwoPoint.Fourier.MinorArcWindowFourth
import Mathlib.Algebra.Order.Chebyshev

namespace OAI

/-! The finite fourth-power Hölder step for the minor-arc cofactor sum. -/

namespace TwoPointCorrelations

open Finset

lemma minor_arc_sum_fourth {ι : Type*} (S : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ S, a i) ^ 4 ≤ (S.card : ℝ) ^ 3 * ∑ i ∈ S, a i ^ 4 := by
  have h₁ := sq_sum_le_card_mul_sum_sq (s := S) (f := a)
  have h₂ := sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => a i ^ 2)
  calc
    _ = ((∑ i ∈ S, a i) ^ 2) ^ 2 := by ring
    _ ≤ ((S.card : ℝ) * ∑ i ∈ S, a i ^ 2) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) h₁ 2
    _ = (S.card : ℝ) ^ 2 * (∑ i ∈ S, a i ^ 2) ^ 2 := mul_pow _ _ _
    _ ≤ (S.card : ℝ) ^ 2 * ((S.card : ℝ) * ∑ i ∈ S, (a i ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left h₂ (sq_nonneg _)
    _ = _ := by simp only [← pow_mul]; ring

lemma minor_arc_weighted_fourth {ι : Type*} (S : Finset ι) (a b : ι → ℂ)
    (ha : ∀ i ∈ S, ‖a i‖ ≤ 1) :
    ‖∑ i ∈ S, a i * b i‖ ^ 4 ≤ (S.card : ℝ) ^ 3 * ∑ i ∈ S, ‖b i‖ ^ 4 := by
  have hn : ‖∑ i ∈ S, a i * b i‖ ≤ ∑ i ∈ S, ‖b i‖ := by
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro i hi
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (ha i hi) (norm_nonneg (b i))
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 4).trans (minor_arc_sum_fourth S (fun i => ‖b i‖))

/-- Polarizing the finite origin sum produces a coefficient of norm one
at every origin, including origins where the short sum vanishes. -/
lemma minor_arc_norm_sum_duality (S : Finset ℕ) (f : ℕ → ℂ) :
    ∃ θ : ℕ → ℂ, (∀ k, ‖θ k‖ = 1) ∧
      (∑ k ∈ S, ‖f k‖) = ‖∑ k ∈ S, θ k * f k‖ := by
  classical
  choose θ hθnorm hθmul using (fun k => Complex.exists_norm_eq_mul_self (f k))
  refine ⟨θ, hθnorm, ?_⟩
  have he : (∑ k ∈ S, θ k * f k) = ((∑ k ∈ S, ‖f k‖ : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact sum_congr rfl (fun k _ => (hθmul k).symm)
  rw [he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sum_nonneg (fun k _ => norm_nonneg (f k)))]

end TwoPointCorrelations

end OAI
