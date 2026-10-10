import OAI.Combinatorics.BalancedRyser.Deletion.DeletionDomination
import OAI.Combinatorics.BalancedRyser.Probability.UniformKernel

namespace OAI

namespace Balanced.DeletionLaw

open Finset

variable {q n : ℕ} {κ : Weight q n}

theorem offsetAverage_nonneg (hκ : IsSubprobabilityKernel κ)
    (m₁ : Offset q n) (s : Split q n) : 0 ≤ offsetAverage κ m₁ s := by
  exact div_nonneg (sum_nonneg (fun m₀ _ => hκ.1 m₀ m₁ s)) (by positivity)

theorem offsetAverage_le_of_atom_bound (hq : 0 < q) (b : ℝ)
    (hκ : ∀ m₀ m₁ s, κ m₀ m₁ s ≤ b)
    (m₁ : Offset q n) (s : Split q n) :
    offsetAverage κ m₁ s ≤ b / (q : ℝ) ^ n :=
  UniformKernel.offsetAverage_le hq κ b hκ m₁ s

theorem successMass_nonneg (hκ : IsSubprobabilityKernel κ) :
    0 ≤ successMass κ := by
  exact sum_nonneg (fun m₁ _ => sum_nonneg (fun s _ => offsetAverage_nonneg hκ m₁ s))

theorem successMass_le_one (hq : 0 < q) (hκ : IsSubprobabilityKernel κ) :
    successMass κ ≤ 1 := by
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have h := UniformKernel.totalMass_le_one κ hκ.2
  simpa only [UniformKernel.fiberMass, successMass, offsetAverage, Offset,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, two_mul, pow_add] using h

theorem deletionMass_nonneg (hκ : IsSubprobabilityKernel κ)
    (D : DeletionSet q n) : 0 ≤ deletionMass κ D := by
  apply sum_nonneg
  intro m₁ _
  apply sum_nonneg
  intro s _
  split_ifs
  · exact offsetAverage_nonneg hκ m₁ s
  · exact le_rfl

theorem deletionMass_le_successMass (hκ : IsSubprobabilityKernel κ)
    (D : DeletionSet q n) : deletionMass κ D ≤ successMass κ := by
  apply sum_le_sum
  intro m₁ _
  apply sum_le_sum
  intro s _
  split_ifs
  · exact le_rfl
  · exact offsetAverage_nonneg hκ m₁ s

theorem sum_deletionMass : ∑ D, deletionMass κ D = successMass κ := by
  unfold deletionMass successMass
  calc
    (∑ D, ∑ m₁, ∑ s,
        if deletionSet m₁ s = D then offsetAverage κ m₁ s else 0) =
        ∑ m₁, ∑ s, ∑ D,
        if deletionSet m₁ s = D then offsetAverage κ m₁ s else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro m₁ _
      rw [sum_comm]
    _ = ∑ m₁, ∑ s, offsetAverage κ m₁ s := by simp

theorem deletionMass_eq_zero_of_invalid
    (hκ : IsSubprobabilityKernel κ) (hdistinct : DistinctOutput κ)
    (D : DeletionSet q n) (hD : ¬ ∀ i, (D i).card = 3) :
    deletionMass κ D = 0 := by
  unfold deletionMass
  apply sum_eq_zero
  intro m₁ _
  apply sum_eq_zero
  intro s _
  split_ifs with h
  · have hzero : ∀ m₀, κ m₀ m₁ s = 0 := by
      intro m₀
      apply le_antisymm _ (hκ.1 m₀ m₁ s)
      apply le_of_not_gt
      intro hpos
      exact hD (h ▸ hdistinct m₀ m₁ s hpos)
    simp [offsetAverage, hzero]
  · rfl

theorem conditionedDeletionMass_nonneg
    (hκ : IsSubprobabilityKernel κ) (D : DeletionSet q n) :
    0 ≤ conditionedDeletionMass κ D :=
  div_nonneg (deletionMass_nonneg hκ D) (successMass_nonneg hκ)

theorem sum_conditionedDeletionMass (h : 0 < successMass κ) :
    ∑ D, conditionedDeletionMass κ D = 1 := by
  simp only [conditionedDeletionMass, ← sum_div, sum_deletionMass]
  exact div_self (ne_of_gt h)

theorem conditionedDeletionMass_eq_zero_of_invalid
    (hκ : IsSubprobabilityKernel κ) (hdistinct : DistinctOutput κ)
    (D : DeletionSet q n) (hD : ¬ ∀ i, (D i).card = 3) :
    conditionedDeletionMass κ D = 0 := by
  rw [conditionedDeletionMass, deletionMass_eq_zero_of_invalid hκ hdistinct D hD, zero_div]

end Balanced.DeletionLaw

end OAI
