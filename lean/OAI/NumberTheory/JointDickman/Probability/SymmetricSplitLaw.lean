import OAI.NumberTheory.JointDickman.Probability.SplitReindex

namespace OAI

/-! # The symmetric two-split law and its coefficient-first disintegration -/

namespace JointDickman

open Finset

noncomputable def twoSplitSiteAverage (P : Finset ℕ)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) : ℝ :=
  ∑ S ∈ P.powerset, ∑ A ∈ P.powerset, ∑ D ∈ P.powerset,
    bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) S *
      subsetRetentionMass S A * subsetRetentionMass S D * F A (S \ A) D (S \ D)

/-- Exchangeability of the two conditionally independent fair splits. -/
theorem twoSplitSiteAverage_swap (P : Finset ℕ)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    twoSplitSiteAverage P F = twoSplitSiteAverage P (fun A R D Q => F D Q A R) := by
  unfold twoSplitSiteAverage
  apply sum_congr rfl
  intro S _
  rw [sum_comm]
  apply sum_congr rfl
  intro A _
  apply sum_congr rfl
  intro D _
  ring

theorem subsetRetentionMass_sum_support {P S : Finset ℕ} (hS : S ⊆ P)
    (F : Finset ℕ → ℝ) :
    (∑ D ∈ P.powerset, subsetRetentionMass S D * F D) =
      ∑ D ∈ S.powerset, subsetRetentionMass S D * F D := by
  classical
  symm
  apply sum_subset (powerset_mono.mpr hS)
  intro D _ hD
  have hn : ¬ D ⊆ S := fun h => hD (mem_powerset.mpr h)
  simp only [subsetRetentionMass, hn, ite_false, zero_mul]

/-- First fix the selected coefficient, then sample its actual conditional
remaining set, and finally split each of those two sets by independent fair coins. -/
theorem twoSplitSiteAverage_reindex (P : Finset ℕ)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    twoSplitSiteAverage P F =
      ∑ A ∈ P.powerset, ∑ R ∈ P.powerset, fairSelectedRemainingMass P A R *
        ∑ I ∈ A.powerset, ∑ U ∈ R.powerset,
          subsetRetentionMass A I * subsetRetentionMass R U *
            F A R (I ∪ U) ((A \ I) ∪ (R \ U)) := by
  classical
  unfold twoSplitSiteAverage
  rw [sum_comm]
  apply sum_congr rfl
  intro A hA
  have hAP := mem_powerset.mp hA
  let H : Finset ℕ → ℝ := fun R => ∑ D ∈ P.powerset,
    subsetRetentionMass (A ∪ R) D * F A R D ((A ∪ R) \ D)
  have hpoint (S : Finset ℕ) :
      (∑ D ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) S *
        subsetRetentionMass S A * subsetRetentionMass S D * F A (S \ A) D (S \ D)) =
      bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) S * subsetRetentionMass S A * H (S \ A) := by
    by_cases hAS : A ⊆ S
    · dsimp [H]
      rw [union_sdiff_of_subset hAS, mul_sum]
      apply sum_congr rfl
      intro D _
      ring
    · simp only [subsetRetentionMass, hAS, ite_false, mul_zero, zero_mul, sum_const_zero]
  simp_rw [hpoint]
  rw [first_split_reindex P A hAP H]
  apply sum_congr rfl
  intro R hR
  by_cases hd : Disjoint A R
  · have hARP : A ∪ R ⊆ P := union_subset hAP (mem_powerset.mp hR)
    dsimp [H]
    rw [subsetRetentionMass_sum_support hARP]
    rw [second_split_reindex A R hd]
  · simp only [fairSelectedRemainingMass, hd, ite_false, zero_mul]

/-- The conditional remaining-prime parameters enter by a proved finite
identity; the main two-split law is not assumed. -/
theorem twoSplitSiteAverage_conditional (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    twoSplitSiteAverage P F =
      ∑ A ∈ P.powerset, bernoulliSubsetMass P (fun p => (1 / 2 : ℝ) / p) A *
        ∑ R ∈ P.powerset, bernoulliSubsetMass P (remainingPrimeParameter A) R *
          ∑ I ∈ A.powerset, ∑ U ∈ R.powerset,
            subsetRetentionMass A I * subsetRetentionMass R U *
              F A R (I ∪ U) ((A \ I) ∪ (R \ U)) := by
  rw [twoSplitSiteAverage_reindex]
  apply sum_congr rfl
  intro A hA
  rw [mul_sum]
  apply sum_congr rfl
  intro R hR
  rw [fairSelectedRemainingMass_factor hP (mem_powerset.mp hA) (mem_powerset.mp hR)]
  ring

end JointDickman

end OAI
