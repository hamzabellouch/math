import OAI.Combinatorics.BalancedRyser.Probability.CountingJointLaw
import OAI.Combinatorics.BalancedRyser.Probability.ScheduledCountingExposure

namespace OAI

namespace Balanced.ScheduledCountingExposure

noncomputable section
open scoped BigOperators Classical
open CountingJointLaw ProfileWitnessPayment

universe u

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k m : ℕ}

def fixedPairTail (γ η ε a : ℝ) (D : DeletionSet F k) (C : Finset (Line F)) : ℝ :=
  fixedPairMean (m := m) (fun d c =>
    if a ≤ (arrayMarkCount (k := k) d c γ η ε : ℝ) then (1 : ℝ) else 0) D C

theorem tail_expect_eq_pairMarkAverage (c : Fin m ↪ Line F)
    (hk : k ≤ Fintype.card F) (γ η ε a : ℝ) :
    (𝔼 ω : Sample F k, if a ≤ (markCount c γ η ε ω : ℝ) then (1 : ℝ) else 0) =
      pairMarkAverage (F := F) k m (fixedPairTail (F := F) (k := k) (m := m) γ η ε a) := by
  simp_rw [markCount_eq_arrayMarkCount]
  exact expect_product_eq_pairMarkAverage hk c (fun d c =>
    if a ≤ (arrayMarkCount (k := k) d c γ η ε : ℝ) then (1 : ℝ) else 0)

def coverPositions (hm : m ≤ Fintype.card F) : Fin m ↪ Line F :=
  ((Fin.castLEEmb hm).trans (Fintype.equivFin F).symm.toEmbedding).trans
    ⟨fun a => ((none : Direction F), a), fun _ _ h => congrArg Prod.snd h⟩

theorem uniform_pair_rare_tail (k : ℕ) (hk : 0 < k) (γ η ε ξ : ℝ)
    (hγ : 0 < γ) (hη : 0 < η) (hε : 0 < ε) (hξ : 0 < ξ) :
    ∃ L : ℝ, ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
        (m : ℕ), N ≤ Fintype.card F → k ≤ Fintype.card F → m ≤ Fintype.card F →
        pairMarkAverage (F := F) k m
          (fixedPairTail (F := F) (k := k) (m := m) γ η ε ((m : ℝ) + ξ * Fintype.card F)) ≤
          Real.exp (L * Fintype.card F - ξ * Fintype.card F *
            Real.log (Fintype.card F)) / (Fintype.card F : ℝ) ^ m := by
  obtain ⟨L, N, htail⟩ := uniform_rare_mark_bound.{u} k hk γ η ε ξ hγ hη hε hξ
  refine ⟨L, N, ?_⟩
  intro F _ _ _ m hN hkq hm
  rw [← tail_expect_eq_pairMarkAverage (coverPositions hm) hkq]
  exact htail F m (coverPositions hm) hN hm

end
end Balanced.ScheduledCountingExposure

end OAI
