import OAI.NumberTheory.TwoPoint.Circuits.CircuitBernoulli

namespace OAI

/-! The averaging step that chooses one polynomial approximation from a
finite random construction, for an arbitrary input distribution. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma FiniteLaw.exists_average_le {α : Type*} [Fintype α]
    (μ : FiniteLaw α) (f : α → ℝ) {a : ℝ} (ha : μ.average f ≤ a) :
    ∃ x, f x ≤ a := by
  by_contra hn
  have hf : ∀ x, a < f x := by simpa only [not_exists, not_le] using hn
  have hpos : ∃ x, 0 < μ.weight x := by
    have ht : 0 < ∑ x, μ.weight x := by rw [μ.total]; norm_num
    simpa only [sum_pos_iff_of_nonneg (fun x _ => μ.nonneg x), mem_univ, true_and] using ht
  obtain ⟨x, hx⟩ := hpos
  have hlt : (∑ y, μ.weight y * a) < ∑ y, μ.weight y * f y := by
    apply sum_lt_sum
    · intro y _
      exact mul_le_mul_of_nonneg_left (hf y).le (μ.nonneg y)
    · exact ⟨x, mem_univ _, mul_lt_mul_of_pos_left (hf x) hx⟩
  change μ.average (fun _ => a) < μ.average f at hlt
  rw [μ.average_const] at hlt
  exact (not_lt_of_ge ha) hlt

/-- If every fixed input has small failure probability over random choices,
one fixed choice has small failure probability for the supplied input law. -/
theorem exists_choice_of_pointwise_failure {α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (ν : FiniteLaw β) (E : α → β → Prop) {ε : ℝ}
    (hE : ∀ x, μ.probability (fun a => E a x) ≤ ε) :
    ∃ a, ν.probability (E a) ≤ ε := by
  apply μ.exists_average_le
  unfold FiniteLaw.probability
  rw [μ.average_comm ν]
  exact (ν.average_mono hE).trans_eq (ν.average_const ε)

end TwoPointCorrelations

end OAI
