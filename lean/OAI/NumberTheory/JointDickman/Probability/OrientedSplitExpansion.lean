import OAI.NumberTheory.JointDickman.Probability.OrientedSplitBound

namespace OAI

/-! # The conditional oriented operator as one explicit finite event sum -/

namespace JointDickman

open Finset

private theorem ite_sum_zero {ι : Type*} (s : Finset ι) (p : Prop) [Decidable p]
    (f : ι → ℝ) : (if p then ∑ i ∈ s, f i else 0) = ∑ i ∈ s, if p then f i else 0 := by
  by_cases hp : p <;> simp [hp]

open Classical in
theorem orientedSplitMass_expansion (B : ℕ) (A D : Finset ℕ) (Y C T : ℝ)
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    let P := additionPrimes B Y
    let H := upperAdditionPrimes B Y
    let k := (2 / 5 : ℝ) * Real.log ((B : ℝ) / Y) - C
    orientedSplitMass B A D Y C T =
      ∑ I ∈ A.powerset, ∑ J ∈ D.powerset,
      ∑ Q ∈ (auxiliaryPrimes B).powerset, ∑ V ∈ (auxiliaryPrimes B).powerset,
      ∑ R ∈ (auxiliaryPrimes B).powerset, ∑ U ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass A (fun _ => (1 / 2 : ℝ)) I *
        bernoulliSubsetMass D (fun _ => (1 / 2 : ℝ)) J *
        jointRetentionMass (auxiliaryPrimes B) (remainingPrimeParameter D) Q V *
        jointRetentionMass (auxiliaryPrimes B) (remainingPrimeParameter A) R U *
        (if (I ∩ (A ∩ H) = A ∩ H) ∧ (J ∩ (D ∩ H) = D ∩ H) ∧
            (k ≤ ((Q ∩ H).card : ℝ) ∧ V ∩ H = ∅) ∧ (k ≤ ((R ∩ H).card : ℝ) ∧ U ∩ H = ∅) then
          additionRatioTest Y T (∏ p ∈ (I ∩ (A ∩ P)) ∪ (A ∩ H), p : ℕ)
            (∏ p ∈ (J ∩ (D ∩ P)) ∪ (D ∩ H), p : ℕ) (U ∩ P) (V ∩ P) else 0) := by
  dsimp only
  unfold orientedSplitMass keptHighAverage noHighAdditionAverage
  dsimp only
  rw [selected_additionPrimeRanges_union hA, selected_additionPrimeRanges_union hD]
  simp only [additionPrimeRanges_union]
  simp only [ite_sum_zero, mul_sum, mul_ite, mul_zero]
  apply sum_congr rfl
  intro I _
  apply sum_congr rfl
  intro J _
  apply sum_congr rfl
  intro Q _
  apply sum_congr rfl
  intro V _
  apply sum_congr rfl
  intro R _
  apply sum_congr rfl
  intro U _
  simp only [← ite_and]
  split_ifs <;> ring

end JointDickman

end OAI
