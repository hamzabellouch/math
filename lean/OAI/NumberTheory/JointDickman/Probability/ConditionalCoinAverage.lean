import OAI.NumberTheory.JointDickman.Probability.TwoSiteConditionalLaw
import OAI.NumberTheory.JointDickman.Probability.OrientedSplitExpansion

namespace OAI

/-! # A common finite expectation for the conditional second split -/

namespace JointDickman
open Finset

theorem bernoulliHalf_eq_retention {P S : Finset ℕ} (hS : S ⊆ P) :
    bernoulliSubsetMass P (fun _ => (1 / 2 : ℝ)) S = subsetRetentionMass P S := by
  classical
  simp only [bernoulliSubsetMass, prod_const, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
    ← pow_add, card_sdiff_of_subset hS, Nat.add_sub_of_le (card_le_card hS),
    subsetRetentionMass, ite_eq_left hS]

noncomputable def conditionalCoinAverage (P A D : Finset ℕ)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) : ℝ :=
  ∑ I ∈ A.powerset, ∑ J ∈ D.powerset,
    ∑ Q ∈ P.powerset, ∑ V ∈ P.powerset, ∑ R ∈ P.powerset, ∑ U ∈ P.powerset,
      bernoulliSubsetMass A (fun _ => (1 / 2 : ℝ)) I *
      bernoulliSubsetMass D (fun _ => (1 / 2 : ℝ)) J *
      jointRetentionMass P (remainingPrimeParameter D) Q V *
      jointRetentionMass P (remainingPrimeParameter A) R U * F R Q I J U V

theorem jointRemainingMass_nonneg {P R U : Finset ℕ} (A : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : R ⊆ P) :
    0 ≤ jointRetentionMass P (remainingPrimeParameter A) R U :=
  mul_nonneg (bernoulliSubsetMass_nonneg hR (fun p hp =>
    remainingPrimeParameter_mem_Icc A (hP p hp).two_le)) (subsetRetentionMass_nonneg _ _)

theorem conditionalCoinAverage_mono {P A D : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime)
    (F G : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ)
    (hFG : ∀ I ⊆ A, ∀ J ⊆ D, ∀ R ⊆ P, ∀ Q ⊆ P, ∀ U ⊆ P, ∀ V ⊆ P,
      F R Q I J U V ≤ G R Q I J U V) :
    conditionalCoinAverage P A D F ≤ conditionalCoinAverage P A D G := by
  unfold conditionalCoinAverage
  apply sum_le_sum
  intro I hI
  apply sum_le_sum
  intro J hJ
  apply sum_le_sum
  intro Q hQ
  apply sum_le_sum
  intro V hV
  apply sum_le_sum
  intro R hR
  apply sum_le_sum
  intro U hU
  apply mul_le_mul_of_nonneg_left
    (hFG I (mem_powerset.mp hI) J (mem_powerset.mp hJ) R (mem_powerset.mp hR)
      Q (mem_powerset.mp hQ) U (mem_powerset.mp hU) V (mem_powerset.mp hV))
  exact mul_nonneg (mul_nonneg (mul_nonneg
    (bernoulliSubsetMass_nonneg (mem_powerset.mp hI) (by intros; norm_num))
    (bernoulliSubsetMass_nonneg (mem_powerset.mp hJ) (by intros; norm_num)))
    (jointRemainingMass_nonneg D hP (mem_powerset.mp hQ)))
    (jointRemainingMass_nonneg A hP (mem_powerset.mp hR))

end JointDickman

end OAI
