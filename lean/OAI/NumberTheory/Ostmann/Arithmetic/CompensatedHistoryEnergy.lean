import OAI.NumberTheory.Ostmann.Arithmetic.SampledHistoryEnergy
import OAI.NumberTheory.Ostmann.Construction.CompensatedAdaptiveSupport

namespace OAI

/-! # Original prime sampling with compensation-divided arithmetic pivots -/

namespace Ostmann

open scoped BigOperators Classical

/-- No new support probability is assumed: it is computed from the literal
integer reversal equations of each nonzero sampled history. -/
theorem compensated_history_square_sum_le (P : Finset ℕ) (S : Finset ℤ) (V n k : ℕ)
    (R : FrequencyTree S n → ℕ) [∀ t, NeZero (R t ^ (k + 2))]
    (D : FrequencyTree S n → PivotDependencyScheme (2 ^ n - 1))
    (U : FrequencyTree S n → Fin (2 ^ n - 1) → ℤ)
    (hU : ∀ t i, IsCoprime (U t i) (R t : ℤ))
    (hdepth : ∀ t i, (D t).depth i ≤ k)
    (hs : ∀ t i, ((D t).frequencies i).root ≠ 0)
    (hsR : ∀ t i, ((D t).frequencies i).root.natAbs ∣ R t)
    (T : TreeLeafIndex n → Finset ℕ)
    (hunit : ∀ t, ∀ p : P, (p : ℕ).Coprime (R t ^ (k + 2)))
    (pivots : FrequencyTree S n → (TreeLeafIndex n → P) → Fin (2 ^ n - 1) → ℤ)
    (W : FrequencyTree S n → (TreeLeafIndex n → P) → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hsize : ∀ t x, ‖W t x‖ ^ 2 ≤ B * frequencyLeafWeight (singleFrequencyLeaf S V) n t)
    (hvalid : ∀ t x, W t x ≠ 0 →
      (sampledPrimeHistory P (R t ^ (k + 2)) n (hunit t) x (pivots t x)).compensatedValid (D t) (U t)) :
    (∑ t, ∑ x, (∏ i, primeSubsetPrior P (T i) (x i)) * ‖W t x‖ ^ 2) ≤
      B * harmonicHistorySupportSum P S V n (fun t => R t ^ (k + 2)) T hunit
        (fun t => compensatedAdaptiveData n (R t) k (D t) (U t) (hs t) (hsR t)) := by
  unfold harmonicHistorySupportSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have hμ : 0 ≤ ∏ i, primeSubsetPrior P (T i) (x i) :=
    Finset.prod_nonneg (fun i _ => primeSubsetPrior_nonneg P (T i) (x i))
  by_cases hw : W t x = 0
  · simp only [hw, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact mul_nonneg (mul_nonneg hB (frequencyLeafWeight_nonneg _
      (fun _ => by unfold singleFrequencyLeaf; split_ifs <;> norm_num) n t))
      (mul_nonneg hμ (singleArithmeticLeafSupport_nonneg n _ _))
  · have hp := compensatedAdaptiveData_actual_support n (R t) k (D t) (U t) (hU t) (hdepth t) (hs t) (hsR t)
      (sampledPrimeHistory P (R t ^ (k + 2)) n (hunit t) x (pivots t x)) (hvalid t x hw)
    rw [sampledPrimeHistory_residue] at hp
    rw [hp, mul_one]
    calc
      _ ≤ (∏ i, primeSubsetPrior P (T i) (x i)) *
          (B * frequencyLeafWeight (singleFrequencyLeaf S V) n t) :=
        mul_le_mul_of_nonneg_left (hsize t x) hμ
      _ = _ := by ring

end Ostmann

end OAI
