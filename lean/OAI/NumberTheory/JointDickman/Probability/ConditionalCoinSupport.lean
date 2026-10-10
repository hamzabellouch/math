import OAI.NumberTheory.JointDickman.Probability.ConditionalCoinAverage
import OAI.NumberTheory.JointDickman.Probability.SplitSupport

namespace OAI

/-! # Restrict conditional averages to their actual probability support -/

namespace JointDickman
open Finset

theorem conditionalCoinAverage_le_on_support {P A D : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime)
    (F G : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ)
    (hFG : ∀ I ⊆ A, ∀ J ⊆ D, ∀ R ⊆ P, ∀ Q ⊆ P, ∀ U ⊆ R, ∀ V ⊆ Q,
      Disjoint A R → Disjoint D Q → F R Q I J U V ≤ G R Q I J U V) :
    conditionalCoinAverage P A D F ≤ conditionalCoinAverage P A D G := by
  classical
  unfold conditionalCoinAverage
  apply sum_le_sum
  intro I hI
  apply sum_le_sum
  intro J hJ
  apply sum_le_sum
  intro Q hQ
  apply sum_le_sum
  intro V _
  apply sum_le_sum
  intro R hR
  apply sum_le_sum
  intro U _
  by_cases hAR : Disjoint A R
  · by_cases hDQ : Disjoint D Q
    · by_cases hU : U ⊆ R
      · by_cases hV : V ⊆ Q
        · apply mul_le_mul_of_nonneg_left
            (hFG I (mem_powerset.mp hI) J (mem_powerset.mp hJ) R (mem_powerset.mp hR)
              Q (mem_powerset.mp hQ) U hU V hV hAR hDQ)
          exact mul_nonneg (mul_nonneg (mul_nonneg
            (bernoulliSubsetMass_nonneg (mem_powerset.mp hI) (by intros; norm_num))
            (bernoulliSubsetMass_nonneg (mem_powerset.mp hJ) (by intros; norm_num)))
            (jointRemainingMass_nonneg D hP (mem_powerset.mp hQ)))
            (jointRemainingMass_nonneg A hP (mem_powerset.mp hR))
        · simp only [jointRetentionMass, subsetRetentionMass, hV, ite_false, mul_zero, zero_mul,
            le_refl]
      · simp only [jointRetentionMass, subsetRetentionMass, hU, ite_false, mul_zero, zero_mul,
          le_refl]
    · simp only [jointRetentionMass, remainingSubsetMass_eq_zero hDQ, zero_mul, mul_zero,
        le_refl]
  · simp only [jointRetentionMass, remainingSubsetMass_eq_zero hAR, zero_mul, mul_zero,
      le_refl]

end JointDickman

end OAI
