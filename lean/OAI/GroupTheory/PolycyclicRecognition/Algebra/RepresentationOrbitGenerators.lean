import OAI.GroupTheory.PolycyclicRecognition.Algebra.MonoidRingOrbitSpan
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PositiveCharacterOrbitSpan

namespace OAI

/-! # Positive annihilators give finite generation over a character monoid -/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra
variable {Q M : Type} [CommGroup Q] [AddCommGroup M]

theorem representation_finite_orbit_generators (ρ : Representation ℤ Q M)
    [Module.Finite ℤ[Q] ρ.asModule] :
    ∃ s : Finset M, Submodule.span ℤ (representationOrbitSet ρ (s : Set M)) = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := exists_finite_monoidOrbitSpan (Q := Q) (M := ρ.asModule)
  let t := s.image ρ.asModuleEquiv
  let W := Submodule.span ℤ (representationOrbitSet ρ (t : Set M))
  have ho : monoidOrbitSet (Q := Q) (s : Set ρ.asModule) ⊆
      W.comap ρ.asModuleEquiv.toLinearMap := by
    rintro y ⟨q, x, hx, rfl⟩
    change ρ.asModuleEquiv (MonoidAlgebra.of ℤ Q q • x) ∈ W
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
    exact Submodule.subset_span ⟨q, ρ.asModuleEquiv x,
      Finset.mem_image_of_mem ρ.asModuleEquiv hx, rfl⟩
  have hle : (⊤ : Submodule ℤ ρ.asModule) ≤ W.comap ρ.asModuleEquiv.toLinearMap := by
    rw [← hs]
    exact Submodule.span_le.mpr ho
  refine ⟨t, top_unique ?_⟩
  intro x _
  have hx := hle (x := ρ.asModuleEquiv.symm x) Submodule.mem_top
  change ρ.asModuleEquiv (ρ.asModuleEquiv.symm x) ∈ W at hx
  simpa only [LinearEquiv.apply_symm_apply] using hx

/-- The sufficient positive-annihilator criterion. The relation is an actual
identity on the module, not an assumed finiteness or solvability conclusion. -/
theorem finite_characterMonoidModule_of_positive_relation
    (ρ : Representation ℤ Q M) [Module.Finite ℤ[Q] ρ.asModule]
    (χ : Q →* Multiplicative ℝ) (a : Finset Q) (c : Q → ℤ)
    {δ : ℝ} (hδ : 0 < δ) (ha : ∀ g ∈ a, δ ≤ (χ g).toAdd)
    (hrec : ∀ x : M, x = ∑ g ∈ a, c g • ρ g x) :
    Module.Finite ℤ[characterNonnegativeMonoid χ] (characterMonoidRepresentation ρ χ).asModule := by
  obtain ⟨s, hs⟩ := representation_finite_orbit_generators ρ
  exact finite_characterMonoidModule_of_orbitSpan ρ χ s
    (positiveCharacterOrbitSpan_eq_top ρ χ (s : Set M) hs a c hδ ha hrec)

end PolycyclicRecognition

end

end OAI
