import OAI.Analysis.Laughlin.Operators.CollectionAnnihilatorBound
import OAI.Analysis.Laughlin.Pair.FactorBounds

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationNormSq_smul (Q : ℕ) (c : ℂ) (x : Space Q) :
    occupationNormSq Q (c • x) = ‖c‖^2 * occupationNormSq Q x := by
  simp [occupationNormSq,mul_pow,Finset.mul_sum]

theorem physicalScaling_normSq_le (Q : ℕ) (hQ : 0 < Q) (x : Space Q) :
    occupationNormSq Q (physicalScaling Q x) ≤ occupationNormSq Q x := by
  unfold occupationNormSq physicalScaling
  apply Finset.sum_le_sum
  intro A hA
  rw [exteriorScaling_coordinate,norm_mul,mul_pow]
  have hb : ‖∏ i ∈ A, (modeFactor Q i.val : ℂ)‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one₀
    · intro i hi
      exact norm_nonneg _
    · intro i hi
      simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (modeFactor_nonneg Q i.val)] using
        modeFactor_le_one Q i.val hQ
  have hsq : ‖∏ i ∈ A, (modeFactor Q i.val : ℂ)‖^2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (norm_nonneg _) hb 2
  exact (mul_le_mul_of_nonneg_right hsq (sq_nonneg _)).trans_eq (one_mul _)

theorem pair_energy_return (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2) (x : Space Q) :
    occupationNormSq Q (limitPairEnd Q p (physicalScaling Q x)) ≤
      occupationNormSq Q (sourcePairEnd Q p x) := by
  have he := congrArg (occupationNormSq Q) (sourcePair_intertwining Q p hQ hp x)
  rw [occupationNormSq_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ pairFactor Q p from Real.sqrt_nonneg _)] at he
  have hr := pairFactor_one_le Q p hp
  have hsq : 1 ≤ (pairFactor Q p)^2 := by nlinarith
  calc
    _ ≤ (pairFactor Q p)^2 * occupationNormSq Q (limitPairEnd Q p (physicalScaling Q x)) := by
      simpa using mul_le_mul_of_nonneg_right hsq (occupationNormSq_nonneg Q _)
    _ = occupationNormSq Q (physicalScaling Q (sourcePairEnd Q p x)) := he.symm
    _ ≤ _ := physicalScaling_normSq_le Q hQ _

theorem pair_window_return (Q : ℕ) (hQ : 24 ≤ Q) (x : Space Q) :
    limitPairWindow Q (physicalScaling Q x) ≤ sourcePairWindow Q x := by
  unfold limitPairWindow sourcePairWindow
  apply Finset.sum_le_sum
  intro p hp
  exact pair_energy_return Q p (by omega)
    (by have h := Finset.mem_range.mp hp; omega) x

end Laughlin.Fock

end OAI
