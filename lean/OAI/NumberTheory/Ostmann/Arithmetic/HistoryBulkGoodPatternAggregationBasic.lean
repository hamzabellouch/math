import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregationSelected

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkGoodPatternAggregation
open scoped BigOperators

theorem norm_sum_mul_le_of_paid {ι : Type*} [Fintype ι]
    (W J : ι→ℂ) (E K T : ℝ) (hE : 0<E) (hK : 0≤K) (hT : 0≤T)
    (hW : ∀i,‖W i‖≤K)
    (hJ : ∀i,(Fintype.card ι:ℝ)*E*‖J i‖≤T) :
    ‖∑i,W i*J i‖ ≤ (T/E)*K := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hi =>
    let := hi
    simp only [Finset.univ_eq_empty,Finset.sum_empty,norm_zero]
    exact mul_nonneg (div_nonneg hT hE.le) hK
  | inr hi =>
    let := hi
    have hn : (0:ℝ)<Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hNE : 0<(Fintype.card ι:ℝ)*E := mul_pos hn hE
    have hJ' (i : ι) : ‖J i‖≤T/((Fintype.card ι:ℝ)*E) := by
      apply (le_div_iff₀ hNE).mpr
      simpa only [mul_comm] using hJ i
    calc
      _ ≤ ∑i,‖W i*J i‖ := norm_sum_le _ _
      _ ≤ ∑_i:ι,K*(T/((Fintype.card ι:ℝ)*E)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        exact mul_le_mul (hW i) (hJ' i) (norm_nonneg _) hK
      _ = (Fintype.card ι:ℝ)*(K*(T/((Fintype.card ι:ℝ)*E))) := by simp
      _ = _ := by field_simp

end Ostmann.Arithmetic.HistoryBulkGoodPatternAggregation

end

end OAI
