import OAI.Combinatorics.BalancedRyser.Deletion.DeletionAsymptotics
import OAI.Combinatorics.BalancedRyser.Probability.SlowThreshold

namespace OAI

open Filter
open scoped Topology

namespace Balanced
open scoped _root_.Balanced

universe u

theorem exists_uniform_deletion_tolerance (k : ℕ) (K : ℝ)
    (E : ℝ → ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      DeletionSet F k → Prop)
    (hE : ∀ δ : ℝ, 0 < δ → UniformDeletionVanishing k K (E δ)) :
    ∃ ε : ℕ → ℝ, (∀ q, 0 < ε q) ∧ Antitone ε ∧
      Tendsto ε atTop (𝓝 0) ∧
      UniformDeletionVanishing k K
        (fun F _ _ _ D => E (ε (Fintype.card F)) F D) := by
  let R : ℕ → ℕ → Prop := fun n t =>
    ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      n ≤ Fintype.card F → k ≤ Fintype.card F →
      ∀ Q : PMF (DeletionSet F k), DeletionDominated k K Q →
        deletionEventProbability Q (E (1 / ((t : ℝ) + 1)) F) <
          1 / ((t : ℝ) + 1)
  have hR : ∀ t, ∀ᶠ n in atTop, R n t := by
    intro t
    have ht : (0 : ℝ) < 1 / ((t : ℝ) + 1) := by positivity
    obtain ⟨N, hN⟩ := hE _ ht _ ht
    filter_upwards [eventually_ge_atTop N] with n hn
    intro F _ _ _ hcard hk Q hQ
    exact hN F (hn.trans hcard) hk Q hQ
  obtain ⟨t, htmono, ht, hbound⟩ := SlowThreshold.exists_monotone_slow_sequence R hR
  let ε : ℕ → ℝ := fun q => 1 / ((t q : ℝ) + 1)
  have hpos : ∀ q, 0 < ε q := by intro q; dsimp [ε]; positivity
  have hanti : Antitone ε := by
    intro m n hmn
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right (htmono hmn) 1
  have hlim : Tendsto ε atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0)).comp ht
  refine ⟨ε, hpos, hanti, hlim, ?_⟩
  intro η hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hbound.and (hlim.eventually_lt_const hη))
  refine ⟨N, ?_⟩
  intro F _ _ _ hcard hk Q hQ
  have hb := (hN (Fintype.card F) hcard).1 (t (Fintype.card F)) le_rfl
  exact (hb F le_rfl hk Q hQ).trans (hN (Fintype.card F) hcard).2

theorem exists_uniform_poisson_tolerance (k : ℕ) (K : ℝ)
    (hTV : ∀ τ : ℝ, 0 < τ → UniformDeletionVanishing.{u} k K
      (fun _ _ _ _ D => τ ≤ deletionMultiplicityTV k D.val)) :
    ∃ ε : ℕ → ℝ, (∀ q, 0 < ε q) ∧ Antitone ε ∧
      Tendsto ε atTop (𝓝 0) ∧
      UniformDeletionVanishing.{u} k K
        (fun F _ _ _ D => ε (Fintype.card F) ≤ deletionMultiplicityTV k D.val) :=
  exists_uniform_deletion_tolerance k K
    (fun τ _ _ _ _ D => τ ≤ deletionMultiplicityTV k D.val) hTV

theorem exists_uniform_occupancy_tolerance (k : ℕ) (K : ℝ)
    (hOcc : ∀ lam η : ℝ, 0 < lam → 0 < η → UniformDeletionVanishing.{u} k K
      (fun F _ _ _ D => η * (Fintype.card F : ℝ) ≤
        ((exceptionalOccupancyLines k lam D.val).card : ℝ))) :
    ∃ ε : ℕ → ℝ, (∀ q, 0 < ε q) ∧ Antitone ε ∧
      Tendsto ε atTop (𝓝 0) ∧
      UniformDeletionVanishing.{u} k K
        (fun F _ _ _ D => ε (Fintype.card F) * (Fintype.card F : ℝ) ≤
          ((exceptionalOccupancyLines k (ε (Fintype.card F)) D.val).card : ℝ)) :=
  exists_uniform_deletion_tolerance k K
    (fun δ F _ _ _ D => δ * (Fintype.card F : ℝ) ≤
      ((exceptionalOccupancyLines k δ D.val).card : ℝ))
    (fun δ hδ => hOcc δ δ hδ hδ)

theorem exists_uniform_poisson_occupancy_tolerance (k : ℕ) (K : ℝ)
    (hTV : ∀ τ : ℝ, 0 < τ → UniformDeletionVanishing.{u} k K
      (fun _ _ _ _ D => τ ≤ deletionMultiplicityTV k D.val))
    (hOcc : ∀ lam η : ℝ, 0 < lam → 0 < η → UniformDeletionVanishing.{u} k K
      (fun F _ _ _ D => η * (Fintype.card F : ℝ) ≤
        ((exceptionalOccupancyLines k lam D.val).card : ℝ))) :
    ∃ ε : ℕ → ℝ, (∀ q, 0 < ε q) ∧ Antitone ε ∧
      Tendsto ε atTop (𝓝 0) ∧
      UniformDeletionVanishing.{u} k K
        (fun F _ _ _ D =>
          ε (Fintype.card F) ≤ deletionMultiplicityTV k D.val ∨
          ε (Fintype.card F) * (Fintype.card F : ℝ) ≤
            ((exceptionalOccupancyLines k (ε (Fintype.card F)) D.val).card : ℝ)) := by
  apply exists_uniform_deletion_tolerance k K
    (fun δ F _ _ _ D => δ ≤ deletionMultiplicityTV k D.val ∨
      δ * (Fintype.card F : ℝ) ≤ ((exceptionalOccupancyLines k δ D.val).card : ℝ))
  intro δ hδ
  exact uniformDeletionVanishing_or k K _ _ (hTV δ hδ) (hOcc δ δ hδ hδ)

end Balanced

end OAI
