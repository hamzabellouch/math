import OAI.NumberTheory.JointDickman.Amplification.AmplificationEnvelope

namespace OAI

/-! # Pointwise bounds for the normalized fair-split envelope -/

namespace JointDickman
open Finset

theorem subsetRetentionMass_sum {P S : Finset ℕ} (hS : S ⊆ P) :
    (∑ A ∈ P.powerset, subsetRetentionMass S A) = 1 := by
  have hs := subsetRetentionMass_sum_support hS (fun _ => 1)
  simp only [mul_one] at hs
  rw [hs]
  calc
    _ = ∑ A ∈ S.powerset, bernoulliSubsetMass S (fun _ => (1 / 2 : ℝ)) A := by
      apply sum_congr rfl
      intro A hA
      exact (bernoulliHalf_eq_retention (mem_powerset.mp hA)).symm
    _ = 1 := bernoulliSubsetMass_sum _ _

theorem sitePairSplitAverage_const_one {P S T : Finset ℕ} (hS : S ⊆ P) (hT : T ⊆ P) :
    sitePairSplitAverage P S T (fun _ _ => 1) = 1 := by
  unfold sitePairSplitAverage
  simp only [mul_one, ← sum_mul_sum, subsetRetentionMass_sum hS, subsetRetentionMass_sum hT]

theorem sitePairSplitAverage_mono (P S T : Finset ℕ) (F G : Finset ℕ → Finset ℕ → ℝ)
    (hFG : ∀ A ⊆ P, ∀ D ⊆ P, F A D ≤ G A D) :
    sitePairSplitAverage P S T F ≤ sitePairSplitAverage P S T G := by
  apply sum_le_sum
  intro A hA
  apply sum_le_sum
  intro D hD
  exact mul_le_mul_of_nonneg_left (hFG A (mem_powerset.mp hA) D (mem_powerset.mp hD))
    (mul_nonneg (subsetRetentionMass_nonneg _ _) (subsetRetentionMass_nonneg _ _))

open Classical in
theorem independentAmplificationEnvelope_nonneg (B L T : ℕ) (τ C : ℝ) (S R : Finset ℕ) :
    0 ≤ independentAmplificationEnvelope B L T τ C S R := by
  unfold independentAmplificationEnvelope sitePairSplitAverage
  apply mul_nonneg (Nat.cast_nonneg _)
  apply sum_nonneg
  intro A _
  apply sum_nonneg
  intro D _
  apply mul_nonneg (mul_nonneg (subsetRetentionMass_nonneg _ _) (subsetRetentionMass_nonneg _ _))
  dsimp only
  split_ifs <;> norm_num

open Classical in
theorem independentAmplificationEnvelope_le {B L T : ℕ} {τ C : ℝ} {S R : Finset ℕ}
    (hS : S ⊆ auxiliaryPrimes B) (hR : R ⊆ auxiliaryPrimes B) :
    independentAmplificationEnvelope B L T τ C S R ≤ B := by
  have hh := sitePairSplitAverage_mono (auxiliaryPrimes B) S R
    (fun A D => if amplificationSplitGood B L T τ C S R A D then (1 : ℝ) else 0)
    (fun _ _ => 1) (by intros; split_ifs <;> norm_num)
  rw [sitePairSplitAverage_const_one hS hR] at hh
  exact (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg B)).trans_eq (mul_one _)

end JointDickman

end OAI
