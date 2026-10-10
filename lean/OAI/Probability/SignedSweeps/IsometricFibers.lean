import OAI.Probability.SignedSweeps.EmbeddedImprimitivity

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G H E F : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

lemma isometric_fiber_of_intertwiner
    {G H E F : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (i : H →* G) (τ : Representation ℂ H E) (σ : Representation ℂ G F)
    [τ.IsIrreducible] [Nontrivial E]
    (hτ : ∀ g x, ‖τ g x‖ = ‖x‖) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖)
    (f : Representation.IntertwiningMap τ (σ.comp i)) (hf : f ≠ 0)
    (hoff : ∀ g ∉ Set.range i, ∀ x y, inner ℂ (f x) (σ g (f y)) = 0) :
    ∃ j : E →ₗᵢ[ℂ] F,
      (∀ g, σ (i g) ∘ₗ j.toLinearMap = j.toLinearMap ∘ₗ τ g) ∧
      (∀ g ∉ Set.range i, ∀ x y, inner ℂ (j x) (σ g (j y)) = 0) := by
  obtain ⟨j,⟨c,hc⟩,hj⟩ := intertwiner_isometric_scaling τ (σ.comp i)
    hτ (fun g x => hσ (i g) x) f hf
  refine ⟨⟨j.toLinearMap,hj⟩, ?_, ?_⟩
  · intro g
    apply LinearMap.ext
    intro x
    exact (Representation.IntertwiningMap.isIntertwining τ (σ.comp i) j g x).symm
  · intro g hg x y
    change inner ℂ (j x) (σ g (j y)) = 0
    rw [hc]
    change inner ℂ (c • f x) (σ g (c • f y)) = 0
    rw [map_smul, inner_smul_left, inner_smul_right, hoff g hg x y, mul_zero, mul_zero]

lemma isometric_fiber_adjoint_off
    {G H E F : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (i : H →* G) (σ : Representation ℂ G F) (j : E →ₗᵢ[ℂ] F)
    (hoff : ∀ g ∉ Set.range i, ∀ x y, inner ℂ (j x) (σ g (j y)) = 0) :
    ∀ g ∉ Set.range i, j.toLinearMap.adjoint ∘ₗ σ g ∘ₗ j.toLinearMap = 0 := by
  intro g hg
  apply LinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  change inner ℂ x (j.toLinearMap.adjoint (σ g (j y))) = inner ℂ x 0
  rw [LinearMap.adjoint_inner_right, inner_zero_right]
  exact hoff g hg x y

lemma nonzero_fiber_multiplicity_le
    (i : H →* G) (hi : Function.Injective i)
    (τ : Representation ℂ H E) (σ : Representation ℂ G F)
    [τ.IsIrreducible] [Nontrivial E]
    (hτ : ∀ g x, ‖τ g x‖ = ‖x‖) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖)
    (f : Representation.IntertwiningMap τ (σ.comp i)) (hf : f ≠ 0)
    (hoff : ∀ g ∉ Set.range i, ∀ x y, inner ℂ (f x) (σ g (f y)) = 0)
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]
    (ρ : Representation ℂ G L) :
    finrank ℂ (Representation.IntertwiningMap (ρ.comp i) τ) ≤
      finrank ℂ (Representation.IntertwiningMap ρ σ) := by
  obtain ⟨j,hj,hjoff⟩ := isometric_fiber_of_intertwiner i τ σ hτ hσ f hf hoff
  exact embedded_fiber_multiplicity_le i hi ρ τ σ j.toLinearMap j.toLinearMap.adjoint
    (isometric_adjoint_comp j) hj (isometric_fiber_adjoint_off i σ j hjoff)

end SignedSweeps
end

end OAI
