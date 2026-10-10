import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExhaustionOrientation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RankOneEndomorphisms

namespace OAI

/-! # Rank-one top homology at every nilpotent exhaustion stage -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule

theorem exists_nilpotent_rankOne_homology_exhaustion {G : Type} [Group G]
    [Countable G] [Group.IsNilpotent G]
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ n : ℕ, ∃ S : ℕ → Subgroup G, ∃ R : Rep ℤ G,
      Monotone S ∧ (∀ i, (S i).FG) ∧ (∀ g, ∃ i, g ∈ S i) ∧
      Nonempty (R.V ≃ₗ[ℤ] ℤ) ∧
      (∀ i j, ((S i).subgroupOf (S j)).FiniteIndex) ∧
      (∀ i, Nonempty (groupHomology (Rep.res (S i).subtype R) n ≃ₗ[ℤ] ℤ)) := by
  obtain ⟨n, S, R, hS, hfg, hcover, ⟨eR⟩, hindex, htop⟩ :=
    exists_nilpotent_oriented_exhaustion hG
  refine ⟨n, S, R, hS, hfg, hcover, ⟨eR⟩, hindex, ?_⟩
  intro i
  obtain ⟨e⟩ := htop i (Rep.res (S i).subtype R)
  exact ⟨e.trans (rankOneEndomorphismsEquiv (Rep.res (S i).subtype R) eR)⟩

end PolycyclicRecognition

end

end OAI
