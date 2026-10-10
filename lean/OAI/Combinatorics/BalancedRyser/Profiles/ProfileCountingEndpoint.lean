import OAI.Combinatorics.BalancedRyser.Probability.ScheduledCountingLaw
import OAI.Combinatorics.BalancedRyser.Probability.ScheduledMarksBridge
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileCountingAssembly

namespace OAI

noncomputable section
open scoped BigOperators

namespace Balanced.ProfileCountingAssembly
open scoped _root_.Balanced

universe u
open ProfileWitnessPayment ScheduledCountingExposure

theorem sourceRareTailBound_of_fixedPairTail
    (heq : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (k m : ℕ) (D : DeletionSet F k) (C : Finset (Line F)),
      C.card = m → ∀ η ε ξ : ℝ,
        fixedPairTail (k := k) (m := m) (Real.sqrt 2) η ε
          ((m : ℝ) + (ξ / 2) * Fintype.card F) D C =
        ProfileScheduledMargin.tailProbability D.val C η ε ξ)
    (k : ℕ) (hk : 1 ≤ k) : SourceRareTailBound.{u} k := by
  intro η ε ξ hη _hηone hε hξ
  obtain ⟨L, N, hrare⟩ := uniform_pair_rare_tail.{u} k (by omega)
    (Real.sqrt 2) η ε (ξ / 2) (Real.sqrt_pos.2 (by norm_num)) hη hε (half_pos hξ)
  refine ⟨L, N, ?_⟩
  intro F _ _ _ m hN hkq hm
  apply le_trans ?_ (hrare F m hN hkq hm)
  unfold pairMarkAverage
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro D _
  apply Finset.sum_le_sum
  intro C hC
  rw [heq F k m D C ((mem_witnesses m C).mp hC) η ε ξ]

private theorem fixedPairTail_source (F : Type u) [Field F] [Fintype F]
    [DecidableEq F] (k m : ℕ) (D : DeletionSet F k) (C : Finset (Line F))
    (hC : C.card = m) (η ε ξ : ℝ) :
    fixedPairTail (k := k) (m := m) (Real.sqrt 2) η ε
      ((m : ℝ) + (ξ / 2) * Fintype.card F) D C =
      ProfileScheduledMargin.tailProbability D.val C η ε ξ := by
  classical
  have hD : k * (Fintype.card F + 1) = D.val.card :=
    (FiniteProfile.deletionSet_card D.property).symm
  unfold fixedPairTail
  rw [CountingJointLaw.fixedPairMean_eq_permutation_average _ D C
    (ScheduledMarksBridge.populationOrder D.val hD)
    (ScheduledMarksBridge.populationOrder C hC.symm)]
  unfold ProfileScheduledMargin.tailProbability
  apply Finset.expect_congr rfl
  intro p _
  rw [ScheduledMarksBridge.arrayMarkCount_eq_sourceMarkCount D.val C hD hC.symm]
  have ht : (m : ℝ) + (ξ / 2) * Fintype.card F =
      (C.card : ℝ) + ξ * (Fintype.card F : ℝ) / 2 := by rw [hC]; ring
  rw [ht]

theorem sourceRareTailBound (k : ℕ) (hk : 1 ≤ k) : SourceRareTailBound.{u} k :=
  sourceRareTailBound_of_fixedPairTail fixedPairTail_source k hk

end Balanced.ProfileCountingAssembly

namespace Balanced
open scoped _root_.Balanced
universe u

theorem profileCounting_proof : ProfileCountingResult.{u} :=
  ProfileCountingAssembly.profileCounting_of_sourceRareTailBound
    ProfileCountingAssembly.sourceRareTailBound
end Balanced

end

end OAI
