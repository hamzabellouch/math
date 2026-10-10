import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieConjugationDifferential
import Mathlib.Algebra.Lie.Ideal

namespace OAI

/-! # Normality of exponential subgroups

The manifold differential of conjugation relates invariant Lie ideals to
normal exponential subgroups.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [T2Space G]

theorem exponential_subgroup_normal_of_adjoint_invariant
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (I : LieIdeal ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) (S : Subgroup G)
    (hS : (S : Set G) = Exp '' (I : Set (GroupLieAlgebra (𝓘(ℝ, E)) G)))
    (hI : ∀ (g : G) (v : GroupLieAlgebra (𝓘(ℝ, E)) G),
      v ∈ I → conjugationDifferentialHom g v ∈ I) : S.Normal := by
  constructor
  intro x hx g
  change x ∈ (S : Set G) at hx
  change g * x * g⁻¹ ∈ (S : Set G)
  rw [hS] at hx ⊢
  obtain ⟨v, hv, rfl⟩ := hx
  rw [conjugation_exponential hExp]
  exact ⟨conjugationDifferentialHom g v, hI g v hv, rfl⟩

theorem integrated_range_normal_of_adjoint_invariant
    {L N : Type*} [Group N]
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (ExpN : L → N) (hN : Function.Surjective ExpN)
    (I : LieIdeal ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (j : L → GroupLieAlgebra (𝓘(ℝ, E)) G) (ι : N →* G)
    (hj : Set.range j = (I : Set (GroupLieAlgebra (𝓘(ℝ, E)) G)))
    (hι : ∀ x, ι (ExpN x) = Exp (j x))
    (hI : ∀ (g : G) (v : GroupLieAlgebra (𝓘(ℝ, E)) G),
      v ∈ I → conjugationDifferentialHom g v ∈ I) : ι.range.Normal := by
  apply exponential_subgroup_normal_of_adjoint_invariant hExp I ι.range _ hI
  ext g
  constructor
  · rintro ⟨n, rfl⟩
    obtain ⟨x, rfl⟩ := hN n
    exact ⟨j x, hj ▸ ⟨x, rfl⟩, (hι x).symm⟩
  · rintro ⟨v, hv, rfl⟩
    rw [← hj] at hv
    obtain ⟨x, rfl⟩ := hv
    exact ⟨ExpN x, hι x⟩

end PolycyclicRecognition

end

end OAI
