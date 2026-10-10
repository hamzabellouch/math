import OAI.NumberTheory.JointDickman.Probability.ConditionalCoinAverage
import OAI.NumberTheory.JointDickman.Probability.NoChangeSplitBound

namespace OAI

/-! # The exact no-change operator on conditional second coins -/

namespace JointDickman
open Finset

theorem keptHighAverage_empty (P : Finset ℕ) (F : Finset ℕ → ℝ) :
    keptHighAverage ∅ P F = (1 / 2 : ℝ)^P.card * F ∅ := by
  rw [keptHighAverage_eq ∅ P (disjoint_empty_left P)]
  simp [subsetAverage, bernoulliSubsetMass]

theorem noHighAdditionAverage_empty (P : Finset ℕ) (q : ℕ → ℝ) (k : ℝ) (F : Finset ℕ → ℝ) :
    noHighAdditionAverage ∅ P q k F = highNoAdditionMass P q k * F ∅ := by
  rw [noHighAdditionAverage_eq ∅ P (disjoint_empty_left P)]
  simp [subsetAverage, bernoulliSubsetMass]

noncomputable def noChangeCoinOperator (P A D : Finset ℕ) (k : ℝ) : ℝ :=
  keptHighAverage ∅ A (fun _ => keptHighAverage ∅ D (fun _ =>
    noHighAdditionAverage ∅ P (remainingPrimeParameter D) k (fun _ =>
      noHighAdditionAverage ∅ P (remainingPrimeParameter A) k (fun _ => 1))))

theorem noChangeCoinOperator_eq (P A D : Finset ℕ) (k : ℝ) :
    noChangeCoinOperator P A D k = (1 / 2 : ℝ)^A.card * (1 / 2 : ℝ)^D.card *
      (highNoAdditionMass P (remainingPrimeParameter D) k *
        highNoAdditionMass P (remainingPrimeParameter A) k) := by
  simp only [noChangeCoinOperator, keptHighAverage_empty, noHighAdditionAverage_empty, mul_one]
  ring

private theorem ite_sum_zero {ι : Type*} (s : Finset ι) (p : Prop) [Decidable p]
    (f : ι → ℝ) : (if p then ∑ i ∈ s, f i else 0) = ∑ i ∈ s, if p then f i else 0 := by
  by_cases hp : p <;> simp [hp]

open Classical in
theorem noChangeCoinOperator_expansion (P A D : Finset ℕ) (k : ℝ) :
    noChangeCoinOperator P A D k = conditionalCoinAverage P A D (fun R Q I J U V =>
      if I = A ∧ J = D ∧ (k ≤ (Q.card : ℝ) ∧ V = ∅) ∧ (k ≤ (R.card : ℝ) ∧ U = ∅)
      then 1 else 0) := by
  unfold noChangeCoinOperator keptHighAverage noHighAdditionAverage conditionalCoinAverage
  simp only [empty_union, ite_sum_zero, mul_sum, mul_ite, mul_zero, mul_one]
  apply sum_congr rfl
  intro I hI
  apply sum_congr rfl
  intro J hJ
  apply sum_congr rfl
  intro Q hQ
  apply sum_congr rfl
  intro V hV
  apply sum_congr rfl
  intro R hR
  apply sum_congr rfl
  intro U hU
  rw [inter_eq_left.mpr (mem_powerset.mp hI), inter_eq_left.mpr (mem_powerset.mp hJ),
    inter_eq_left.mpr (mem_powerset.mp hQ), inter_eq_left.mpr (mem_powerset.mp hV),
    inter_eq_left.mpr (mem_powerset.mp hR), inter_eq_left.mpr (mem_powerset.mp hU)]
  simp only [← ite_and]
  split_ifs <;> ring

end JointDickman

end OAI
