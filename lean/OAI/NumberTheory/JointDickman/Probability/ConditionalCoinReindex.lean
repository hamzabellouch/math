import OAI.NumberTheory.JointDickman.Probability.ConditionalCoinAverage

namespace OAI

/-! # Changing the order of the exact conditional finite averages -/

namespace JointDickman
open Finset

private theorem six_sum_reorder (P A D : Finset ℕ)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    (∑ I ∈ A.powerset, ∑ J ∈ D.powerset, ∑ Q ∈ P.powerset,
      ∑ V ∈ P.powerset, ∑ R ∈ P.powerset, ∑ U ∈ P.powerset, F R Q I J U V) =
    ∑ R ∈ P.powerset, ∑ I ∈ A.powerset, ∑ U ∈ P.powerset,
      ∑ Q ∈ P.powerset, ∑ J ∈ D.powerset, ∑ V ∈ P.powerset, F R Q I J U V := by
  conv_lhs => arg 2; ext I; arg 2; ext J; arg 2; ext Q; rw [sum_comm]
  conv_lhs => arg 2; ext I; arg 2; ext J; rw [sum_comm]
  conv_lhs => arg 2; ext I; rw [sum_comm]
  rw [sum_comm]
  conv_lhs => arg 2; ext R; arg 2; ext I; arg 2; ext J; arg 2; ext Q; rw [sum_comm]
  conv_lhs => arg 2; ext R; arg 2; ext I; arg 2; ext J; rw [sum_comm]
  conv_lhs => arg 2; ext R; arg 2; ext I; rw [sum_comm]
  conv_lhs => arg 2; ext R; arg 2; ext I; arg 2; ext U; rw [sum_comm]

/-- Rewrite the common conditional average in site-first order, with
all retention sums over the common ambient prime set. -/
theorem conditionalCoinAverage_reindex (P A D : Finset ℕ)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    conditionalCoinAverage P A D F =
    ∑ R ∈ P.powerset, bernoulliSubsetMass P (remainingPrimeParameter A) R *
    ∑ I ∈ A.powerset, ∑ U ∈ P.powerset, subsetRetentionMass A I * subsetRetentionMass R U *
    (∑ Q ∈ P.powerset, bernoulliSubsetMass P (remainingPrimeParameter D) Q *
    ∑ J ∈ D.powerset, ∑ V ∈ P.powerset, subsetRetentionMass D J * subsetRetentionMass Q V *
      F R Q I J U V) := by
  unfold conditionalCoinAverage
  rw [six_sum_reorder]
  simp only [mul_sum]
  apply sum_congr rfl
  intro R _
  apply sum_congr rfl
  intro I hI
  apply sum_congr rfl
  intro U _
  apply sum_congr rfl
  intro Q _
  apply sum_congr rfl
  intro J hJ
  apply sum_congr rfl
  intro V _
  rw [bernoulliHalf_eq_retention (mem_powerset.mp hI),
    bernoulliHalf_eq_retention (mem_powerset.mp hJ)]
  unfold jointRetentionMass
  ring

end JointDickman

end OAI
