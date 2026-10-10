import OAI.Probability.ContinuumTransition.KacBlocks

namespace OAI

universe u_1

section
open scoped BigOperators
namespace ContinuumTemperature
open Classical

theorem sum_supported_rows_le {α : Type u_1} [DecidableEq α] (s T : Finset α) (M : ℝ) (hM : 0 ≤ M)
    (J : α → α → ℝ) (hrow : ∀ k : s, (∑ l : s, J k l) ≤ M) :
    (∑ k : s, ∑ l : s, if (k : α) ∈ T then J k l else 0) ≤ T.card*M := by
  have hh : (∑ k : s, ∑ l : s, if (k : α) ∈ T then J k l else 0) ≤
      ∑ k : s, if (k : α) ∈ T then M else 0 := by
    apply Finset.sum_le_sum
    intro k _
    split_ifs with hk
    · simpa only [ite_eq_left hk] using hrow k
    · simp only [Finset.sum_const_zero, le_refl]
  apply hh.trans
  rw [Finset.sum_coe_sort s (fun k : α => if k ∈ T then M else 0), ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hs : s.filter (fun k => k ∈ T) ⊆ T := fun _ hk => (Finset.mem_filter.mp hk).2
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hs) hM

end ContinuumTemperature
end

end OAI
