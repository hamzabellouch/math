import Mathlib
import OAI.RepresentationTheory.PartialPermutation.Model
import OAI.RepresentationTheory.PartialPermutation.ModuleTransport

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators

namespace PartialPermutation
noncomputable section
section Components
variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma componentSimple_simple (c : isotypicComponents ℂ[G] ρ.asModule) :
    IsSimpleModule ℂ[G] (componentSimple ρ c) := c.property.choose_spec.1

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma componentSimple_component (c : isotypicComponents ℂ[G] ρ.asModule) :
    c.val = isotypicComponent ℂ[G] ρ.asModule (componentSimple ρ c) :=
  c.property.choose_spec.2

noncomputable def componentCharacter (c : isotypicComponents ℂ[G] ρ.asModule) : OccurringTypes ρ :=
  ⟨(Subrepresentation.ofSubmodule' (componentSimple ρ c)).toRepresentation.character,
    Subrepresentation.ofSubmodule' (componentSimple ρ c),
    (subrep_irreducible_iff ρ _).mpr (componentSimple_simple ρ c), rfl⟩

lemma componentCharacter_injective : Function.Injective (componentCharacter ρ) := by
  intro c d h
  let σ := Subrepresentation.ofSubmodule' (componentSimple ρ c)
  let τ := Subrepresentation.ofSubmodule' (componentSimple ρ d)
  have : Representation.IsIrreducible σ.toRepresentation :=
    (subrep_irreducible_iff ρ σ).mpr (componentSimple_simple ρ c)
  have : Representation.IsIrreducible τ.toRepresentation :=
    (subrep_irreducible_iff ρ τ).mpr (componentSimple_simple ρ d)
  obtain ⟨e⟩ := irreducible_equiv_of_character_eq σ.toRepresentation τ.toRepresentation
    (congrArg Subtype.val h)
  apply Subtype.ext
  rw [componentSimple_component ρ c, componentSimple_component ρ d]
  exact (moduleEquivOfSubrepEquiv ρ τ σ e).symm.isotypicComponent_eq

omit [Fintype G] in
lemma componentCharacter_surjective : Function.Surjective (componentCharacter ρ) := by
  intro χ
  obtain ⟨σ, hirr, hχ⟩ := χ.property
  have := hirr
  have : IsSimpleModule ℂ[G] σ.asSubmodule := (subrep_irreducible_iff ρ σ).mp hirr
  let c : isotypicComponents ℂ[G] ρ.asModule :=
    ⟨isotypicComponent ℂ[G] ρ.asModule σ.asSubmodule, σ.asSubmodule, inferInstance, rfl⟩
  have := componentSimple_simple ρ c
  have hs : σ.asSubmodule ≤ c.val := σ.asSubmodule.le_isotypicComponent
  rw [componentSimple_component ρ c] at hs
  obtain ⟨e⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent ℂ[G] ρ.asModule (componentSimple ρ c))
    σ.asSubmodule hs
  refine ⟨c, Subtype.ext ?_⟩
  change (Subrepresentation.ofSubmodule' (componentSimple ρ c)).toRepresentation.character = χ.val
  rw [hχ]
  exact Representation.char_iso
    (subrepEquivOfModuleEquiv ρ (Subrepresentation.ofSubmodule' (componentSimple ρ c)) σ e.symm)

noncomputable def componentTypeEquiv : isotypicComponents ℂ[G] ρ.asModule ≃ OccurringTypes ρ :=
  Equiv.ofBijective (componentCharacter ρ)
    ⟨componentCharacter_injective ρ, componentCharacter_surjective ρ⟩

instance occurringTypes_finite : Finite (OccurringTypes ρ) :=
  Finite.of_surjective (componentCharacter ρ) (componentCharacter_surjective ρ)

lemma card_components_eq_types :
    Nat.card (isotypicComponents ℂ[G] ρ.asModule) = Nat.card (OccurringTypes ρ) :=
  Nat.card_congr (componentTypeEquiv ρ)

end Components

end
end PartialPermutation

end

end OAI
