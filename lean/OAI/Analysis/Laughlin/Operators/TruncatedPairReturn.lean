import OAI.Analysis.Laughlin.Operators.TruncatedConjugation

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem truncatedScaling_normSq_le (L Q : ℕ) (hQ : 0 < Q) (x : Space Q) :
    occupationNormSq Q (truncatedScaling L Q x) ≤ occupationNormSq Q x := by
  unfold occupationNormSq truncatedScaling
  apply Finset.sum_le_sum
  intro A hA
  rw [exteriorScaling_coordinate,norm_mul,mul_pow]
  have hb : ‖∏ i ∈ A, (truncatedModeFactor L Q i : ℂ)‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one₀
    · intro i hi; exact norm_nonneg _
    · intro i hi
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (truncatedModeFactor_pos L Q hQ i)]
      unfold truncatedModeFactor
      split_ifs
      · exact modeFactor_le_one Q i.val hQ
      · exact le_rfl
  have hsq : ‖∏ i ∈ A, (truncatedModeFactor L Q i : ℂ)‖^2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (norm_nonneg _) hb 2
  exact (mul_le_mul_of_nonneg_right hsq (sq_nonneg _)).trans_eq (one_mul _)

theorem truncated_pair_energy_return (L Q p : ℕ) (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (hL : p+1 ≤ L) (x : Space Q) :
    occupationNormSq Q (limitPairEnd Q p (truncatedScaling L Q x)) ≤
      occupationNormSq Q (sourcePairEnd Q p x) := by
  have he := congrArg (occupationNormSq Q) (truncated_sourcePair_intertwining L Q p hQ hp hL x)
  rw [occupationNormSq_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ pairFactor Q p from Real.sqrt_nonneg _)] at he
  have hr := pairFactor_one_le Q p hp
  have hsq : 1 ≤ (pairFactor Q p)^2 := by nlinarith
  calc
    _ ≤ (pairFactor Q p)^2 * occupationNormSq Q (limitPairEnd Q p (truncatedScaling L Q x)) := by
      simpa using mul_le_mul_of_nonneg_right hsq (occupationNormSq_nonneg Q _)
    _ = occupationNormSq Q (truncatedScaling L Q (sourcePairEnd Q p x)) := he.symm
    _ ≤ _ := truncatedScaling_normSq_le L Q hQ _

theorem truncated_pair_window_return (Q : ℕ) (hQ : 24 ≤ Q) (x : Space Q) :
    limitPairWindow Q (truncatedScaling 24 Q x) ≤ sourcePairWindow Q x := by
  unfold limitPairWindow sourcePairWindow
  apply Finset.sum_le_sum
  intro p hp
  have hp' := Finset.mem_range.mp hp
  exact truncated_pair_energy_return 24 Q p (by omega) (by omega) (by omega) x

end Laughlin.Fock

end OAI
