import Mathlib.RepresentationTheory.Irreducible

namespace OAI

/-! # A simple algebra action fills all endomorphisms

Schur's lemma identifies the commutant with the scalar field. Jacobson
density then gives the full endomorphism algebra in finite dimension.
-/

noncomputable section
namespace PolycyclicRecognition

theorem simple_algebra_action_surjective
    {K A V : Type*} [Field K] [IsAlgClosed K] [Ring A] [Algebra K A]
    [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
    [IsSimpleModule A V] [FiniteDimensional K V] :
    Function.Surjective (Module.toModuleEnd K (S := A) V) := by
  let : Module.Finite (Module.End A V) V :=
    Module.Finite.of_restrictScalars_finite K (Module.End A V) V
  intro f
  let F : Module.End (Module.End A V) V := {
    toFun := f
    map_add' := f.map_add
    map_smul' := by
      intro t x
      obtain ⟨c, rfl⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed K).surjective t
      change f (c • x) = c • f x
      exact f.map_smul c x }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := V) F
  refine ⟨a, LinearMap.ext fun x => ?_⟩
  exact congrArg (fun T : Module.End (Module.End A V) V => T x) ha

theorem irreducible_algebra_span_surjective
    {K G V : Type*} [Field K] [IsAlgClosed K] [Monoid G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) [ρ.IsIrreducible] : Function.Surjective ρ.asAlgebraHom := by
  intro f
  let fM : Module.End K ρ.asModule :=
    ρ.asModuleEquiv.symm.toLinearMap.comp (f.comp ρ.asModuleEquiv.toLinearMap)
  obtain ⟨a, ha⟩ := simple_algebra_action_surjective (A := MonoidAlgebra K G) (V := ρ.asModule) fM
  refine ⟨a, LinearMap.ext fun x => ?_⟩
  have hx := congrArg (fun T : Module.End K ρ.asModule => T (ρ.asModuleEquiv.symm x)) ha
  have hh := congrArg ρ.asModuleEquiv hx
  change ρ.asModuleEquiv (a • ρ.asModuleEquiv.symm x) =
    ρ.asModuleEquiv (fM (ρ.asModuleEquiv.symm x)) at hh
  rw [Representation.asModuleEquiv_map_smul] at hh
  simpa only [Representation.asModuleEquiv_map_smul, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, fM] using hh

theorem irreducible_linear_span_eq_top
    {K G V : Type*} [Field K] [IsAlgClosed K] [Monoid G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) [ρ.IsIrreducible] :
    Submodule.span K (Set.range ρ) = ⊤ := by
  apply top_unique
  intro T hT
  clear hT
  obtain ⟨a, rfl⟩ := irreducible_algebra_span_surjective ρ T
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    rw [Representation.asAlgebraHom_of]
    exact Submodule.subset_span (Set.mem_range_self g)
  | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul c a ha => simpa only [map_smul] using Submodule.smul_mem _ c ha

end PolycyclicRecognition

end

end OAI
