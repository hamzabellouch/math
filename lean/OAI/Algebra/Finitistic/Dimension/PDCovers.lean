import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.Jacobson.Radical

namespace OAI
noncomputable section
namespace LittleFinitistic.PDCovers
open Module LinearMap Submodule
universe u v
variable {A : Type u} [Ring A]
variable {E N : Type v} [AddCommGroup E] [Module A E]
  [AddCommGroup N] [Module A N]

/-- An epimorphism is right minimal if every endomorphism over it is surjective. -/
def RightMinimal (p : E →ₗ[A] N) : Prop :=
  ∀ f : Module.End A E, p.comp f = p → Function.Surjective f

lemma comp_pow_eq {p : E →ₗ[A] N} {f : Module.End A E}
    (h : p.comp f = p) (n : ℕ) : p.comp (f ^ n) = p := by
  induction n with
  | zero => ext x; rfl
  | succ n ih => rw [pow_succ, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ih, h]

/-- Fitting decomposition upgrades minimality among projective submodules to
right minimality of an actual epimorphism. -/
theorem rightMinimal_of_minimal [IsArtinian A E] [IsNoetherian A E]
    (p : E →ₗ[A] N) (S : Submodule A E)
    (hS : Minimal (fun T : Submodule A E =>
      Module.Projective A T ∧ Function.Surjective (p.comp T.subtype)) S) :
    RightMinimal (p.comp S.subtype) := by
  have : Module.Projective A S := hS.1.1
  intro f hf
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp f.eventually_isCompl_ker_pow_range_pow
  let r := f ^ (n+1)
  have hc : IsCompl (LinearMap.range r) (LinearMap.ker r) :=
    (hn (n+1) (by omega)).symm
  let R := LinearMap.range r
  have : Module.Projective A R := Module.Projective.of_split R.subtype
    (R.projectionOnto (LinearMap.ker r) hc) (Submodule.projectionOnto_comp_subtype hc)
  let T := R.map S.subtype
  let i : R →ₗ[A] E := S.subtype.comp R.subtype
  have hi : Function.Injective i := S.injective_subtype.comp R.injective_subtype
  have he : LinearMap.range i = T := by simp [i, T, LinearMap.range_comp]
  let e : R ≃ₗ[A] T := (LinearEquiv.ofInjective i hi).trans (LinearEquiv.ofEq _ _ he)
  have : Module.Projective A T := Module.Projective.of_equiv e
  have hpr : (p.comp S.subtype).comp r = p.comp S.subtype := comp_pow_eq hf _
  have hTsurj : Function.Surjective (p.comp T.subtype) := by
    intro y
    obtain ⟨x, hx⟩ := hS.1.2 y
    refine ⟨⟨S.subtype (r x), ⟨r x, mem_range_self r x, rfl⟩⟩, ?_⟩
    exact (DFunLike.congr_fun hpr x).trans hx
  have hTS : T ≤ S := by
    rintro x ⟨z, hz, rfl⟩
    exact z.property
  have hST : S ≤ T := hS.2 ⟨inferInstance, hTsurj⟩ hTS
  have hr : Function.Surjective r := by
    intro x
    obtain ⟨z, ⟨w, hw⟩, hz⟩ := hST x.property
    refine ⟨w, ?_⟩
    exact hw.trans (Subtype.ext hz)
  intro x
  obtain ⟨y, hy⟩ := hr x
  refine ⟨(f ^ n) y, ?_⟩
  simpa [r, pow_succ', Module.End.mul_eq_comp] using hy

/-- Every projective epimorphism from a finite-length module contains a
projective cover. This proves existence rather than assuming covers. -/
theorem exists_rightMinimal [IsArtinian A E] [IsNoetherian A E]
    [Module.Projective A E] (p : E →ₗ[A] N) (hp : Function.Surjective p) :
    ∃ S : Submodule A E, Module.Projective A S ∧
      Function.Surjective (p.comp S.subtype) ∧ RightMinimal (p.comp S.subtype) := by
  have : Module.Projective A (⊤ : Submodule A E) :=
    Module.Projective.of_equiv (Submodule.topEquiv : (⊤ : Submodule A E) ≃ₗ[A] E).symm
  obtain ⟨S, hS⟩ := WellFoundedLT.exists_minimal (inferInstance : WellFoundedLT (Submodule A E))
    {T : Submodule A E | Module.Projective A T ∧ Function.Surjective (p.comp T.subtype)}
    ⟨⊤, inferInstance, fun y => by obtain ⟨x, hx⟩ := hp y; exact ⟨⟨x, mem_top⟩, hx⟩⟩
  exact ⟨S, hS.1.1, hS.1.2, rightMinimal_of_minimal p S hS⟩
end LittleFinitistic.PDCovers

end

end OAI
