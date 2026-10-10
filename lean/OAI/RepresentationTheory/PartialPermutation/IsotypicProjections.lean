import Mathlib
import OAI.RepresentationTheory.PartialPermutation.CompleteKernels
import OAI.RepresentationTheory.PartialPermutation.ComponentGeometry

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
namespace PartialPermutation
noncomputable section
section FullProjection
variable {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)

omit [FiniteDimensional ℂ V] in
lemma linearMap_eq_on_simples (A B : Module.End ℂ V)
    (h : ∀ (σ : Subrepresentation ρ) [Representation.IsIrreducible σ.toRepresentation],
      ∀ x : σ, A x = B x) : A = B := by
  let E (S : {S : Submodule ℂ[G] ρ.asModule // IsSimpleModule ℂ[G] S}) : Submodule ℂ V :=
    S.val.restrictScalars ℂ
  have htop : (⨆ S, E S) = ⊤ := by
    change (⨆ S : {S : Submodule ℂ[G] ρ.asModule // IsSimpleModule ℂ[G] S},
      S.val.restrictScalars ℂ) = ⊤
    rw [← Submodule.restrictScalars_iSup]
    have ht : (⨆ S : {S : Submodule ℂ[G] ρ.asModule // IsSimpleModule ℂ[G] S}, S.val) = ⊤ :=
      (sSup_eq_iSup' {S : Submodule ℂ[G] ρ.asModule | IsSimpleModule ℂ[G] S}).symm.trans
        (IsSemisimpleModule.sSup_simples_eq_top ℂ[G] ρ.asModule)
    rw [ht, Submodule.restrictScalars_top]
  have hker : (⊤ : Submodule ℂ V) ≤ LinearMap.ker (A - B) := by
    rw [← htop]
    refine iSup_le fun S => ?_
    intro x hx
    let σ := Subrepresentation.ofSubmodule' S.val
    have : Representation.IsIrreducible σ.toRepresentation :=
      (subrep_irreducible_iff ρ σ).mpr S.property
    exact sub_eq_zero.mpr (h σ ⟨x, hx⟩)
  apply LinearMap.ext
  intro x
  have hx := hker (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ V))
  simpa only [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] using hx

lemma component_kernel_eq_projection (hρ : IsUnitary ρ)
    (c : isotypicComponents ℂ[G] ρ.asModule) :
    complexFourier ρ (centralCharacterKernel (componentRep ρ c)) =
      (componentSpace ρ c).starProjection.toLinearMap := by
  apply linearMap_eq_on_simples ρ
  intro σ hσ x
  have := hσ
  have : IsSimpleModule ℂ[G] σ.asSubmodule := (subrep_irreducible_iff ρ σ).mp hσ
  let d : isotypicComponents ℂ[G] ρ.asModule :=
    ⟨isotypicComponent ℂ[G] ρ.asModule σ.asSubmodule, σ.asSubmodule, inferInstance, rfl⟩
  have hx : (x : V) ∈ componentSpace ρ d :=
    σ.asSubmodule.le_isotypicComponent x.property
  have he : Nonempty (Representation.Equiv (componentRep ρ d) σ.toRepresentation) := by
    have := componentSimple_simple ρ d
    have hs : σ.asSubmodule ≤ d.val := σ.asSubmodule.le_isotypicComponent
    rw [componentSimple_component ρ d] at hs
    obtain ⟨e⟩ := isIsotypicOfType_submodule_iff.mp
      (IsIsotypicOfType.isotypicComponent ℂ[G] ρ.asModule (componentSimple ρ d))
      σ.asSubmodule hs
    exact ⟨subrepEquivOfModuleEquiv ρ _ σ e.symm⟩
  have hi : Nonempty (Representation.Equiv (componentRep ρ c) σ.toRepresentation) ↔ c = d := by
    constructor
    · rintro ⟨e⟩
      obtain ⟨ed⟩ := he
      exact (componentRep_equiv_iff ρ c d).mp ⟨e.trans ed.symm⟩
    · rintro rfl
      exact he
  rw [← complexFourier_subrep ρ σ]
  have ht := centralCharacterKernel_fourier (componentRep ρ c) σ.toRepresentation
  by_cases hcd : c = d
  · subst c
    rw [ite_eq_left he] at ht
    rw [ht]
    exact ((componentSpace ρ d).starProjection_eq_self_iff.mpr hx).symm
  · rw [ite_eq_right (mt hi.mp hcd)] at ht
    rw [ht]
    change 0 = (componentSpace ρ c).starProjection (x : V)
    symm
    apply (Submodule.starProjection_apply_eq_zero_iff (K := componentSpace ρ c)).mpr
    intro y hy
    exact componentSpace_orthogonal ρ hρ hcd ⟨y, hy⟩ ⟨x, hx⟩

end FullProjection
end
end PartialPermutation

end

end OAI
