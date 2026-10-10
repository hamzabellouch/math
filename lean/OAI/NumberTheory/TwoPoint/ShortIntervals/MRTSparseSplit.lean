import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSetSampling

namespace OAI

/-! The extra-prime split in the no-small-band argument. Small values of
the prime polynomial use a cofactor mean square; large values use a
prime-supported mean square and a pointwise cofactor estimate. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

/-- The finite split retains the restricted prime mean square on the
large-prime-polynomial samples. -/
theorem mrt_sparse_product_split (S : Finset ℝ) (Q R : ℝ → ℂ)
    {θ U CR CQ : ℝ}
    (hR : (∑ t ∈ S, ‖R t‖^2) ≤ CR)
    (hQ : (∑ t ∈ S.filter (fun t => θ ≤ ‖Q t‖), ‖Q t‖^2) ≤ CQ)
    (hpoint : ∀ t ∈ S, θ ≤ ‖Q t‖ → ‖R t‖ ≤ U) :
    (∑ t ∈ S, ‖Q t*R t‖^2) ≤ θ^2*CR+U^2*CQ := by
  let L := S.filter (fun t => θ ≤ ‖Q t‖)
  let K := S.filter (fun t => ¬θ ≤ ‖Q t‖)
  have hsmall : (∑ t ∈ K, ‖Q t*R t‖^2) ≤ θ^2*CR := by
    calc
      _ ≤ ∑ t ∈ K, θ^2*‖R t‖^2 := by
        apply sum_le_sum
        intro t ht
        have hqt : ‖Q t‖ ≤ θ := (lt_of_not_ge (mem_filter.mp ht).2).le
        rw [norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) hqt 2) (sq_nonneg _)
      _ = θ^2*∑ t ∈ K, ‖R t‖^2 := (mul_sum _ _ _).symm
      _ ≤ θ^2*∑ t ∈ S, ‖R t‖^2 := mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _))
        (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hR (sq_nonneg _)
  have hlarge : (∑ t ∈ L, ‖Q t*R t‖^2) ≤ U^2*CQ := by
    calc
      _ ≤ ∑ t ∈ L, U^2*‖Q t‖^2 := by
        apply sum_le_sum
        intro t ht
        have hr := hpoint t (mem_filter.mp ht).1 (mem_filter.mp ht).2
        rw [norm_mul, mul_pow, mul_comm]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) hr 2) (sq_nonneg _)
      _ = U^2*∑ t ∈ L, ‖Q t‖^2 := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hQ (sq_nonneg _)
  have he := sum_filter_add_sum_filter_not S (fun t => θ ≤ ‖Q t‖)
    (fun t => ‖Q t*R t‖^2)
  change (∑ t ∈ L, ‖Q t*R t‖^2)+(∑ t ∈ K, ‖Q t*R t‖^2) = _ at he
  linarith

/-- A bound for all separated samples yields the actual integral on the
no-small set, without leaving the set when choosing sample points. -/
theorem mrt_set_product_split (Q R : ℝ → ℂ)
    (hQc : Continuous Q) (hRc : Continuous R)
    {E : Set ℝ} (hE : MeasurableSet E) {T θ U CR CQ : ℝ}
    (hT : 0 ≤ T) (hET : E ⊆ Set.Ioc (-T) T)
    (hR : ∀ S : Finset ℝ, (∀ t ∈ S, t ∈ E) →
      (∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) → (∑ t ∈ S, ‖R t‖^2) ≤ CR)
    (hQ : ∀ S : Finset ℝ, (∀ t ∈ S, t ∈ E ∧ θ ≤ ‖Q t‖) →
      (∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) → (∑ t ∈ S, ‖Q t‖^2) ≤ CQ)
    (hpoint : ∀ t ∈ E, θ ≤ ‖Q t‖ → ‖R t‖ ≤ U) :
    (∫ t in E, ‖Q t*R t‖^2) ≤ 4*(θ^2*CR+U^2*CQ) := by
  apply mrt_set_integral_of_samples (fun t => ‖Q t*R t‖^2)
    ((hQc.mul hRc).norm.pow 2) (fun _ => sq_nonneg _) hE hT hET
  intro S hS hsep
  apply mrt_sparse_product_split S Q R (hR S hS hsep)
  · apply hQ (S.filter (fun t => θ ≤ ‖Q t‖))
    · intro t ht
      exact ⟨hS t (mem_filter.mp ht).1,(mem_filter.mp ht).2⟩
    · intro t ht s hs hts
      exact hsep t (mem_filter.mp ht).1 s (mem_filter.mp hs).1 hts
  · intro t ht hqt
    exact hpoint t (hS t ht) hqt

end TwoPointCorrelations

end OAI
