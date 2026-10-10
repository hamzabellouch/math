import Mathlib

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators

namespace PartialPermutation
noncomputable section

section ModuleTransport
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)

noncomputable def subrepModuleEquiv (σ : Subrepresentation ρ) :
    σ.toRepresentation.asModule ≃ₗ[ℂ[G]] σ.asSubmodule where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    apply Subtype.ext
    change ((σ.toRepresentation.asAlgebraHom a) x).val =
      (ρ.asAlgebraHom a) x.val
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp only [map_zero]; rfl
    | add a b ha hb =>
      simp only [map_add]
      change ((σ.toRepresentation.asAlgebraHom a) x).val +
        ((σ.toRepresentation.asAlgebraHom b) x).val = _ + _
      rw [ha, hb]
    | single g c =>
      rw [Representation.asAlgebraHom_single, Representation.asAlgebraHom_single]
      rfl

lemma subrep_irreducible_iff (σ : Subrepresentation ρ) :
    Representation.IsIrreducible σ.toRepresentation ↔ IsSimpleModule ℂ[G] σ.asSubmodule := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact ⟨fun _ => IsSimpleModule.congr (subrepModuleEquiv ρ σ).symm,
    fun _ => IsSimpleModule.congr (subrepModuleEquiv ρ σ)⟩

noncomputable def subrepEquivOfModuleEquiv (σ τ : Subrepresentation ρ)
    (e : σ.asSubmodule ≃ₗ[ℂ[G]] τ.asSubmodule) :
    Representation.Equiv σ.toRepresentation τ.toRepresentation := by
  let e' := (subrepModuleEquiv ρ σ).trans (e.trans (subrepModuleEquiv ρ τ).symm)
  exact ((Representation.IntertwiningMap.equivLinearMapAsModule _ _).symm
    e'.toLinearMap).ofBijective e'.bijective

noncomputable def moduleEquivOfSubrepEquiv (σ τ : Subrepresentation ρ)
    (e : Representation.Equiv σ.toRepresentation τ.toRepresentation) :
    σ.asSubmodule ≃ₗ[ℂ[G]] τ.asSubmodule := by
  let f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ e.toIntertwiningMap
  let e' := LinearEquiv.ofBijective f e.bijective
  exact (subrepModuleEquiv ρ σ).symm.trans (e'.trans (subrepModuleEquiv ρ τ))

end ModuleTransport

lemma irreducible_equiv_of_character_eq {G V W : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ]
    (h : ρ.character = σ.character) : Nonempty (Representation.Equiv σ ρ) := by
  classical
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := G)).ne')
  have hself := Representation.char_orthonormal ρ ρ
  have hother := Representation.char_orthonormal ρ σ
  rw [h] at hself
  rw [h] at hother
  have he : Nonempty (ρ.Equiv ρ) := ⟨Representation.Equiv.refl ρ⟩
  simp only [he, ite_eq_left] at hself
  by_contra hn
  simp only [hn] at hother
  exact one_ne_zero (hself.symm.trans hother)

def OccurringTypes {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :=
  {χ : G → ℂ // ∃ σ : Subrepresentation ρ,
    Representation.IsIrreducible σ.toRepresentation ∧ χ = σ.toRepresentation.character}

end
end PartialPermutation
end

end OAI
