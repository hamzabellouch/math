import OAI.Combinatorics.BalancedRyser.Deletion.UniformDeletionTolerance
import OAI.Combinatorics.BalancedRyser.Probability.RobustMultiplicity
import OAI.Combinatorics.BalancedRyser.Selection.OccupancyFailureClass
import OAI.Combinatorics.BalancedRyser.Selection.OccupancyWitness

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Filter
open scoped Topology

universe u

theorem robustOccupancy_of_profileCounting_of_visible
    (hcounting : ProfileCountingResult.{u})
    (k : ℕ) (hk : 1 ≤ k) (K lam η : ℝ)
    (hη : 0 < η) (hηone : η ≤ 1)
    (hvisible : ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) → ∀ high : Bool,
      ProfileVisibleExcess (occupancyFailureClass.{u} k (η / 4) lam ε high)) :
    UniformDeletionVanishing.{u} k K
      (fun F _ _ _ D => η * (Fintype.card F : ℝ) ≤
        ((exceptionalOccupancyLines k lam D.val).card : ℝ)) := by
  obtain ⟨ε, _hpos, _hanti, hlim, hbadTV⟩ := exists_uniform_poisson_tolerance k K
    (fun τ hτ => robustMultiplicity_of_profileCounting hcounting k hk K τ hτ)
  have hclass (high : Bool) : UniformDeletionVanishing.{u} k K
      (fun F _ _ _ D => ∃ C : Finset (Line F),
        occupancyFailureClass k (η / 4) lam ε high F D.val C) :=
    uniformDeletionVanishing_of_profileCounting hcounting k hk K _
      (occupancyFailureClass_valid k (η / 4) lam ε high)
      ⟨η / 4, by positivity, occupancyFailureClass_sizeGap k (η / 4) lam ε high⟩
      (hvisible ε hlim high)
  have hsigns := uniformDeletionVanishing_or k K _ _ (hclass false) (hclass true)
  have hall := uniformDeletionVanishing_or k K _ _ hbadTV hsigns
  apply uniformDeletionVanishing_eventually_mono k K _ _ _ hall
  obtain ⟨N, hN⟩ := exists_order_for_occupancy_gap η hη
  refine ⟨N, ?_⟩
  intro F _ _ _ hn D hbad
  by_cases hTV : ε (Fintype.card F) ≤ deletionMultiplicityTV k D.val
  · exact Or.inl hTV
  · obtain ⟨high, C, hC⟩ := occupancyFailureClass_witness_of_exceptional
      k hη.le hηone ε F D (hN _ hn) hbad (le_of_not_ge hTV)
    cases high
    · exact Or.inr (Or.inl ⟨C, hC⟩)
    · exact Or.inr (Or.inr ⟨C, hC⟩)

theorem robustOccupancy_extend_fraction
    (k : ℕ) (K lam : ℝ)
    (hsmall : ∀ η : ℝ, 0 < η → η ≤ 1 → UniformDeletionVanishing.{u} k K
      (fun F _ _ _ D => η * (Fintype.card F : ℝ) ≤
        ((exceptionalOccupancyLines k lam D.val).card : ℝ))) :
    ∀ η : ℝ, 0 < η → UniformDeletionVanishing.{u} k K
      (fun F _ _ _ D => η * (Fintype.card F : ℝ) ≤
        ((exceptionalOccupancyLines k lam D.val).card : ℝ)) := by
  intro η hη
  apply uniformDeletionVanishing_mono k K _ _ _
    (hsmall (min η 1) (lt_min hη (by norm_num)) (min_le_right _ _))
  intro F _ _ _ D hD
  exact (mul_le_mul_of_nonneg_right (min_le_left η 1)
    (Nat.cast_nonneg (Fintype.card F))).trans hD

end Balanced

end OAI
