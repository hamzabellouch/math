import OAI.Algebra.Finitistic.Dimension.PDCovers
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Artinian.Instances

namespace OAI
noncomputable section
namespace LittleFinitistic.PDCovers
open Module LinearMap Submodule
universe u
variable {A : Type u} [Ring A]
variable {E N : Type u} [AddCommGroup E] [Module A E]
  [AddCommGroup N] [Module A N]

/-- A projective right-minimal epimorphism has a superfluous kernel. -/
theorem eq_top_of_sup_ker [Module.Projective A E]
    (p : E →ₗ[A] N) (hp : Function.Surjective p) (hm : RightMinimal p)
    (L : Submodule A E) (hL : L ⊔ LinearMap.ker p = ⊤) : L = ⊤ := by
  have hsurj : Function.Surjective (p.comp L.subtype) := by
    intro y
    obtain ⟨x, hx⟩ := hp y
    have hm : x ∈ L ⊔ LinearMap.ker p := hL.symm ▸ mem_top
    obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.mp hm
    refine ⟨⟨z, hz⟩, ?_⟩
    have hw0 : p w = 0 := hw
    change p z = y
    rw [← hx, ← hzw, map_add, hw0, add_zero]
  obtain ⟨g, hg⟩ := Module.projective_lifting_property (p.comp L.subtype) p hsurj
  have hfg : p.comp (L.subtype.comp g) = p := by rwa [← LinearMap.comp_assoc]
  have hfgsurj := hm (L.subtype.comp g) hfg
  apply top_unique
  intro x _
  obtain ⟨z, hz⟩ := hfgsurj x
  rw [← hz]
  exact (g z).property

/-- Projective-cover kernels lie in the actual module Jacobson radical. -/
theorem ker_le_jacobson [Module.Projective A E]
    (p : E →ₗ[A] N) (hp : Function.Surjective p) (hm : RightMinimal p) :
    LinearMap.ker p ≤ Module.jacobson A E := by
  apply le_sInf
  intro L hL
  by_contra h
  have hlt : L < L ⊔ LinearMap.ker p := lt_of_le_of_ne le_sup_left (fun he => h (he ▸ le_sup_right))
  have htop : L ⊔ LinearMap.ker p = ⊤ := hL.2 _ hlt
  exact hL.1 (eq_top_of_sup_ker p hp hm L htop)

/-- Over a finite-dimensional algebra every finite-dimensional module has an
actual finitely generated projective cover, constructed inside a finite free module. -/
theorem exists_finite_projective_cover
    {k : Type u} [Field k] [Algebra k A] [FiniteDimensional k A]
    [Module k N] [IsScalarTower k A N] [FiniteDimensional k N] :
    ∃ (n : ℕ) (S : Submodule A (Fin n → A)) (p : S →ₗ[A] N),
      Module.Projective A S ∧ Function.Surjective p ∧
      RightMinimal p ∧ LinearMap.ker p ≤ Module.jacobson A S := by
  have : Module.Finite A N := Module.Finite.of_restrictScalars_finite k A N
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' A N
  have : IsArtinian A (Fin n → A) := isArtinian_of_tower k inferInstance
  have : IsNoetherian A (Fin n → A) := isNoetherian_of_tower k inferInstance
  obtain ⟨S, hS, hs, hm⟩ := exists_rightMinimal p hp
  have := hS
  exact ⟨n, S, p.comp S.subtype, hS, hs, hm, ker_le_jacobson _ hs hm⟩
end LittleFinitistic.PDCovers

end

end OAI
