import OAI.NumberTheory.TwoPoint.Bounds.PaddingDeletionComparison

namespace OAI

/-! Finite families of interval comparisons may use a different integer
length in every bin. No common probability space for the sampled
integer intervals is needed. -/

namespace TwoPointCorrelations

open Finset

lemma finite_interval_family_error {ι β : Type*} [Fintype β]
    (I : Finset ι) (μ : FiniteLaw β) (a N : ι → ℕ)
    (f : ι → ℤ → ℝ) (g : ι → β → ℝ) (ε : ι → ℝ)
    (h : ∀ i ∈ I, |uniformAverage (fun x : Fin (N i) => f i (a i + x.val)) -
      μ.average (g i)| ≤ ε i) :
    |(∑ i ∈ I, uniformAverage (fun x : Fin (N i) => f i (a i + x.val))) -
      μ.average (fun x => ∑ i ∈ I, g i x)| ≤ ∑ i ∈ I, ε i := by
  rw [μ.average_finset_sum, ← sum_sub_distrib]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum h)

lemma finset_sum_error {ι : Type*} (I : Finset ι) (f g ε : ι → ℝ)
    (h : ∀ i ∈ I, |f i - g i| ≤ ε i) :
    |(∑ i ∈ I, f i) - ∑ i ∈ I, g i| ≤ ∑ i ∈ I, ε i := by
  rw [← sum_sub_distrib]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum h)

end TwoPointCorrelations

end OAI
