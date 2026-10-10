import OAI.Combinatorics.BalancedRyser.Deletion.DeletionProbability
import OAI.Combinatorics.BalancedRyser.Deletion.ExponentialDomination

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Filter
open scoped Topology

universe u

theorem uniformDeletionVanishing_of_superexponential_count
    (k : ℕ) (K : ℝ)
    (E : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      DeletionSet F k → Prop)
    {b : ℝ} (hb : 0 < b)
    (hcount : ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        N ≤ Fintype.card F → k ≤ Fintype.card F →
        (deletionEventCard (E F) : ℝ) / (Fintype.card (DeletionSet F k) : ℝ) ≤
          Real.exp (-b * (Fintype.card F : ℝ) * Real.log (Fintype.card F))) :
    UniformDeletionVanishing k K E := by
  intro ε hε
  have ht := BalancedRyser.tendsto_exp_linear_mul_exp_neg_mul_log K hb
  have hsmall : ∀ᶠ q : ℕ in atTop,
      Real.exp (K * q) * Real.exp (-b * q * Real.log q) < ε :=
    (tendsto_order.1 ht).2 ε hε
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hsmall
  obtain ⟨N₀, hN₀⟩ := hcount
  refine ⟨max N₀ N₁, ?_⟩
  intro F _ _ _ hN hk Q hdom
  have hn₀ : N₀ ≤ Fintype.card F := (le_max_left _ _).trans hN
  have hn₁ : N₁ ≤ Fintype.card F := (le_max_right _ _).trans hN
  calc
    deletionEventProbability Q (E F) ≤
        Real.exp (K * (Fintype.card F : ℝ)) * (deletionEventCard (E F) : ℝ) /
          (Fintype.card (DeletionSet F k) : ℝ) :=
      deletionEventProbability_le_uniform Q hdom (E F)
    _ = Real.exp (K * (Fintype.card F : ℝ)) *
        ((deletionEventCard (E F) : ℝ) / (Fintype.card (DeletionSet F k) : ℝ)) := by
      ring
    _ ≤ Real.exp (K * (Fintype.card F : ℝ)) *
        Real.exp (-b * (Fintype.card F : ℝ) * Real.log (Fintype.card F)) :=
      mul_le_mul_of_nonneg_left (hN₀ F hn₀ hk) (Real.exp_nonneg _)
    _ < ε := hN₁ (Fintype.card F) hn₁

theorem uniformDeletionVanishing_mono
    (k : ℕ) (K : ℝ)
    (E G : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      DeletionSet F k → Prop)
    (hEG : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      ∀ D, E F D → G F D)
    (hG : UniformDeletionVanishing k K G) :
    UniformDeletionVanishing k K E := by
  intro ε hε
  obtain ⟨N, hN⟩ := hG ε hε
  refine ⟨N, ?_⟩
  intro F _ _ _ hn hk Q hdom
  exact (deletionEventProbability_mono Q (hEG F)).trans_lt (hN F hn hk Q hdom)

theorem uniformDeletionVanishing_eventually_mono
    (k : ℕ) (K : ℝ)
    (E G : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      DeletionSet F k → Prop)
    (hEG : ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        N ≤ Fintype.card F → ∀ D, E F D → G F D)
    (hG : UniformDeletionVanishing k K G) :
    UniformDeletionVanishing k K E := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hEG
  obtain ⟨N₁, hN₁⟩ := hG ε hε
  refine ⟨max N₀ N₁, ?_⟩
  intro F _ _ _ hn hk Q hdom
  exact (deletionEventProbability_mono Q
    (hN₀ F ((le_max_left _ _).trans hn))).trans_lt
      (hN₁ F ((le_max_right _ _).trans hn) hk Q hdom)

theorem uniformDeletionVanishing_or
    (k : ℕ) (K : ℝ)
    (E G : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      DeletionSet F k → Prop)
    (hE : UniformDeletionVanishing k K E)
    (hG : UniformDeletionVanishing k K G) :
    UniformDeletionVanishing k K (fun F _ _ _ D => E F D ∨ G F D) := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨N₀, hN₀⟩ := hE (ε / 2) hhalf
  obtain ⟨N₁, hN₁⟩ := hG (ε / 2) hhalf
  refine ⟨max N₀ N₁, ?_⟩
  intro F _ _ _ hN hk Q hdom
  have hn₀ : N₀ ≤ Fintype.card F := (le_max_left _ _).trans hN
  have hn₁ : N₁ ≤ Fintype.card F := (le_max_right _ _).trans hN
  have he := hN₀ F hn₀ hk Q hdom
  have hg := hN₁ F hn₁ hk Q hdom
  have hu := deletionEventProbability_or_le Q (E F) (G F)
  linarith

end Balanced

end OAI
