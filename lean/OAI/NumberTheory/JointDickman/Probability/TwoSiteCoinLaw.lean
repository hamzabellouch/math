import OAI.NumberTheory.JointDickman.Probability.ConditionalCoinReindex

namespace OAI

/-! # The full two-site law in the common conditional coin average -/

namespace JointDickman
open Finset

theorem twoSplitSiteAverage_coin (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    twoSplitSiteAverage P F =
      ∑ A ∈ P.powerset, bernoulliSubsetMass P (fun p => (1 / 2 : ℝ) / p) A *
      ∑ R ∈ P.powerset, bernoulliSubsetMass P (remainingPrimeParameter A) R *
      ∑ I ∈ A.powerset, ∑ U ∈ P.powerset, subsetRetentionMass A I * subsetRetentionMass R U *
        F A R (I ∪ U) ((A \ I) ∪ (R \ U)) := by
  classical
  rw [twoSplitSiteAverage_conditional P hP]
  apply sum_congr rfl
  intro A _
  congr 1
  apply sum_congr rfl
  intro R hR
  congr 1
  apply sum_congr rfl
  intro I _
  apply sum_subset (powerset_mono.mpr (mem_powerset.mp hR))
  intro U _ hU
  have hn : ¬ U ⊆ R := fun h => hU (mem_powerset.mpr h)
  simp only [subsetRetentionMass, hn, ite_false, mul_zero, zero_mul]

/-- Exact disintegration by the two first coefficients, followed by the
conditional remaining-set and second-coin law. -/
theorem twoSiteSplit_coin_law (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ →
      Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    (∑ x : TwoSiteSplit P, twoSiteSplitMass P x *
      F x.first₁.val (x.site₁.val \ x.first₁.val) x.second₁.val (x.site₁.val \ x.second₁.val)
        x.first₂.val (x.site₂.val \ x.first₂.val) x.second₂.val (x.site₂.val \ x.second₂.val)) =
    ∑ A ∈ P.powerset, bernoulliSubsetMass P (fun p => (1 / 2 : ℝ) / p) A *
    ∑ D ∈ P.powerset, bernoulliSubsetMass P (fun p => (1 / 2 : ℝ) / p) D *
      conditionalCoinAverage P A D (fun R Q I J U V =>
        F A R (I ∪ U) ((A \ I) ∪ (R \ U)) D Q (J ∪ V) ((D \ J) ∪ (Q \ V))) := by
  rw [twoSiteSplit_expectation, twoSplitSiteAverage_coin P hP]
  simp_rw [twoSplitSiteAverage_coin P hP, conditionalCoinAverage_reindex]
  simp only [mul_sum]
  apply sum_congr rfl
  intro A _
  conv_lhs => arg 2; ext R; arg 2; ext I; rw [sum_comm]
  conv_lhs => arg 2; ext R; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro D _
  apply sum_congr rfl
  intro R _
  apply sum_congr rfl
  intro I _
  apply sum_congr rfl
  intro U _
  apply sum_congr rfl
  intro Q _
  apply sum_congr rfl
  intro J _
  apply sum_congr rfl
  intro V _
  ring

end JointDickman

end OAI
