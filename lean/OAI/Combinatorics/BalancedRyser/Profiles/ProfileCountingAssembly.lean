import OAI.Combinatorics.BalancedRyser.Profiles.ProfileSourceMarkLimit
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileWitnessPayment

namespace OAI

noncomputable section
open scoped BigOperators

namespace Balanced.ProfileCountingAssembly

universe u

open ProfileScheduledMargin ProfileWitnessPayment

def SourceRareTailBound (k : ℕ) : Prop :=
  ∀ η ε ξ : ℝ, 0 < η → η ≤ 1 → 0 < ε → 0 < ξ →
    ∃ L : ℝ, ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
        (m : ℕ), N ≤ Fintype.card F → k ≤ Fintype.card F →
        m ≤ Fintype.card F →
        pairMarkAverage (F := F) k m (fun D C => tailProbability D.val C η ε ξ) ≤
          Real.exp (L * (Fintype.card F : ℝ) -
            (ξ / 2) * (Fintype.card F : ℝ) * Real.log (Fintype.card F : ℝ)) /
              (Fintype.card F : ℝ) ^ m

theorem profileCounting_of_sourceRareTailBound
    (hrare : ∀ k : ℕ, 1 ≤ k → SourceRareTailBound.{u} k) :
    ProfileCountingResult.{u} := by
  intro k hk A hvalid hgap hvisible
  obtain ⟨n, ξ, hξ, N₀, hpositive⟩ :=
    ProfileSourceMarkLimit.exists_uniform_positive_tail k hk A hvalid hgap hvisible
  have hthreshold : threshold n ≤ 1 := by
    unfold threshold
    apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
    linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  obtain ⟨L, N₁, hnegative⟩ := hrare k hk (threshold n) (threshold n) ξ
    (threshold_pos n) hthreshold (threshold_pos n) hξ
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  apply counting_of_mark_bounds k A hvalid (ξ / (4 * (k : ℝ))) L (ξ / 2)
    (by positivity) (half_pos hξ)
  refine ⟨max N₀ N₁, ?_⟩
  intro F _ _ _ hN hkq
  refine ⟨fun _ D C => tailProbability D.val C (threshold n) (threshold n) ξ,
    ?_, ?_, ?_⟩
  · intro m D C
    unfold tailProbability
    apply Finset.expect_nonneg
    intro p _
    split <;> norm_num
  · intro m D C _ hA
    exact hpositive F D.val C hA ((le_max_left N₀ N₁).trans hN)
  · intro m hm
    exact hnegative F m ((le_max_right N₀ N₁).trans hN) hkq hm

end Balanced.ProfileCountingAssembly

end

end OAI
