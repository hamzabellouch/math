import OAI.NumberTheory.TwoPoint.Halasz.HalaszSparseCofactor
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparseSplit
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTGeneralTypical

namespace OAI

/-! The small additional-prime branch, using the proved integer kernel. -/
namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma halasz_sparse_cofactor_bounded (P : Finset ℕ) (F : ℕ → ℂ)
    (hF : OneBounded F) (N : ℕ) {a : ℝ} (ha : 1 ≤ a)
    (hx : 2 ≤ (N:ℝ)/a) {T : ℝ} (hT : 0 ≤ T)
    (S : Finset ℝ) (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|)
    (hcost : (S.card:ℝ)*halaszSparseKernelError ((N:ℝ)/a) T ≤ (N:ℝ)/a) :
    (∑ t ∈ S, ‖mrtCofactorPolynomial P F N a t‖^2) ≤ 297602 := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hN : (0:ℝ) < N := by
    have hh := (le_div_iff₀ ha0).mp hx
    linarith
  apply (halasz_sparse_cofactor_energy P F hF N ha hx hT S hS hsep).trans
  calc
    _ ≤ (148800*((N:ℝ)/a)+(N:ℝ)/a)*(2*a/N) :=
      mul_le_mul_of_nonneg_right (add_le_add_right hcost _) (by positivity)
    _ = 297602 := by field_simp; ring

theorem halasz_small_prime_samples (P : Finset ℕ) (F B : ℕ → ℂ)
    (hB : OneBounded B) (N : ℕ) {a : ℝ} (ha : 1 ≤ a)
    (hx : 2 ≤ (N:ℝ)/a) {T θ : ℝ} (hT : 0 ≤ T)
    (S : Finset ℝ) (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|)
    (hcost : (S.card:ℝ)*halaszSparseKernelError ((N:ℝ)/a) T ≤ (N:ℝ)/a)
    (hsmall : ∀ t ∈ S, ‖mrtExponentialPolynomial P
      (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t‖ ≤ θ) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial P
      (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t *
      mrtCofactorPolynomial P B N a t‖^2) ≤ 297602*θ^2 := by
  calc
    _ ≤ ∑ t ∈ S, θ^2*‖mrtCofactorPolynomial P B N a t‖^2 := by
      apply sum_le_sum
      intro t ht
      rw [norm_mul,mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hsmall t ht) 2) (sq_nonneg _)
    _ = θ^2*∑ t ∈ S, ‖mrtCofactorPolynomial P B N a t‖^2 :=
      (mul_sum _ _ _).symm
    _ ≤ θ^2*297602 := mul_le_mul_of_nonneg_left
      (halasz_sparse_cofactor_bounded P B hB N ha hx hT S hS hsep hcost) (sq_nonneg _)
    _ = _ := by ring

theorem halasz_small_prime_integral (P : Finset ℕ) (F B : ℕ → ℂ)
    (hB : OneBounded B) (N : ℕ) {a : ℝ} (ha : 1 ≤ a)
    (hx : 2 ≤ (N:ℝ)/a) {T θ : ℝ} (hT : 0 ≤ T)
    {E : Set ℝ} (hE : MeasurableSet E) (hET : E ⊆ Set.Ioc (-T) T)
    (hcost : ∀ S : Finset ℝ, (∀ t ∈ S, t ∈ E) →
      (∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) →
      (S.card:ℝ)*halaszSparseKernelError ((N:ℝ)/a) T ≤ (N:ℝ)/a)
    (hsmall : ∀ t ∈ E, ‖mrtExponentialPolynomial P
      (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t‖ ≤ θ) :
    (∫ t in E, ‖mrtExponentialPolynomial P
      (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t *
      mrtCofactorPolynomial P B N a t‖^2) ≤ 1190408*θ^2 := by
  have hh := mrt_set_integral_of_samples
    (fun t => ‖mrtExponentialPolynomial P (fun p => F p/(p:ℂ))
      (fun p => -Real.log (p:ℝ)) t * mrtCofactorPolynomial P B N a t‖^2)
    (((mrtExponentialPolynomial_continuous _ _ _).mul
      (mrtCofactorPolynomial_continuous P B N a)).norm.pow 2)
    (fun _ => sq_nonneg _) hE hT hET (B := 297602*θ^2) (by
      intro S hS hsep
      apply halasz_small_prime_samples P F B hB N ha hx hT S
        (fun t ht => abs_le.mpr ⟨by linarith [(hET (hS t ht)).1],(hET (hS t ht)).2⟩)
        hsep (hcost S hS hsep) (fun t ht => hsmall t (hS t ht)))
  linarith

end TwoPointCorrelations

end OAI
