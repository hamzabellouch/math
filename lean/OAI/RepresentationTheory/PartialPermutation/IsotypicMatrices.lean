import Mathlib

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace PartialPermutation

section Burnside
variable {R S : Type*} [Ring R] [Algebra ℂ R] [AddCommGroup S]
    [Module ℂ S] [Module R S] [IsScalarTower ℂ R S]
    [IsSimpleModule R S] [FiniteDimensional ℂ S]

lemma simple_action_surjective : Function.Surjective (Algebra.lsmul ℂ ℂ S (A := R)) := by
  intro f
  let E := Module.End R S
  let f' : Module.End E S :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun c x => by
        obtain ⟨t, rfl⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed ℂ
          (A := R) (V := S)).surjective c
        change f (t • x) = t • f x
        exact f.map_smul t x }
  have : Module.Finite E S := Module.Finite.of_restrictScalars_finite ℂ E S
  obtain ⟨r, hr⟩ := (Module.Finite.toModuleEnd_moduleEnd_surjective (R := R) (M := S)) f'
  refine ⟨r, ?_⟩
  ext x
  exact congrArg (fun A : Module.End E S => A x) hr

end Burnside

def diagonalEnd {S : Type*} [AddCommGroup S] [Module ℂ S] (m : ℕ) :
    Module.End ℂ S →ₐ[ℂ] Module.End ℂ (Fin m → S) where
  toFun A := LinearMap.pi fun i => A.comp (LinearMap.proj i)
  map_zero' := by ext; rfl
  map_one' := by ext; rfl
  map_add' := by intros; ext; rfl
  map_mul' := by intros; ext; rfl
  commutes' := by intro; ext; rfl

section Isotypic
variable {R M S : Type*} [Ring R] [Algebra ℂ R]
    [AddCommGroup M] [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
    [AddCommGroup S] [Module ℂ S] [Module R S] [IsScalarTower ℂ R S]

noncomputable def isotypicLift {m : ℕ} (e : M ≃ₗ[R] Fin m → S) :
    Module.End ℂ S →ₐ[ℂ] Module.End ℂ M :=
  (e.restrictScalars ℂ).symm.conjAlgEquiv ℂ |>.toAlgHom.comp (diagonalEnd m)

lemma isotypicLift_action {m : ℕ} (e : M ≃ₗ[R] Fin m → S) (r : R) :
    isotypicLift e (Algebra.lsmul ℂ ℂ S r) = Algebra.lsmul ℂ ℂ M r := by
  ext x
  apply (e.restrictScalars ℂ).injective
  simp [isotypicLift, diagonalEnd, LinearEquiv.conjAlgEquiv_apply, map_smul]
  ext i
  rfl

lemma isotypicLift_range [IsSimpleModule R S] [FiniteDimensional ℂ S]
    {m : ℕ} (e : M ≃ₗ[R] Fin m → S) (A : Module.End ℂ S) :
    ∃ r : R, isotypicLift e A = Algebra.lsmul ℂ ℂ M r := by
  obtain ⟨r, rfl⟩ := simple_action_surjective (R := R) A
  exact ⟨r, isotypicLift_action e r⟩

noncomputable def isotypicOrbitMap {m : ℕ} (e : M ≃ₗ[R] Fin m → S) (v : M) :
    Module.End ℂ S →ₗ[ℂ] M where
  toFun A := isotypicLift e A v
  map_add' A B := by simp
  map_smul' c A := by simp

lemma mem_isotypicOrbitMap_range {m : ℕ} (e : M ≃ₗ[R] Fin m → S) (v : M) :
    v ∈ LinearMap.range (isotypicOrbitMap e v) := by
  refine ⟨1, ?_⟩
  simp [isotypicOrbitMap]

lemma isotypicOrbitMap_range_invariant {m : ℕ} (e : M ≃ₗ[R] Fin m → S)
    (v : M) (r : R) (x : M) (hx : x ∈ LinearMap.range (isotypicOrbitMap e v)) :
    r • x ∈ LinearMap.range (isotypicOrbitMap e v) := by
  obtain ⟨A, rfl⟩ := hx
  refine ⟨Algebra.lsmul ℂ ℂ S r * A, ?_⟩
  change isotypicLift e (_ * A) v = r • (isotypicLift e A v)
  rw [map_mul, Module.End.mul_apply, isotypicLift_action]
  rfl

lemma finrank_isotypicOrbitMap_range [FiniteDimensional ℂ S] {m : ℕ}
    (e : M ≃ₗ[R] Fin m → S) (v : M) :
    Module.finrank ℂ (LinearMap.range (isotypicOrbitMap e v)) ≤
      (Module.finrank ℂ S) ^ 2 := by
  calc
    _ ≤ Module.finrank ℂ (Module.End ℂ S) := LinearMap.finrank_range_le _
    _ = _ := by rw [Module.finrank_linearMap]; ring

end Isotypic

structure IsotypicMatrixModel (R M : Type*) [Ring R] [Algebra ℂ R]
    [AddCommGroup M] [Module ℂ M] [Module R M] [IsScalarTower ℂ R M] where
  degree : ℕ
  degree_pos : 0 < degree
  lift : Matrix (Fin degree) (Fin degree) ℂ →ₐ[ℂ] Module.End ℂ M
  lift_image : ∀ A, ∃ r : R, lift A = Algebra.lsmul ℂ ℂ M r
  orbit : ∀ v : M, ∃ W : Submodule ℂ M, v ∈ W ∧
    (∀ r : R, ∀ x ∈ W, r • x ∈ W) ∧ Module.finrank ℂ W ≤ degree ^ 2

lemma exists_isotypicMatrixModel {R M : Type*} [Ring R] [Algebra ℂ R]
    [AddCommGroup M] [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
    [FiniteDimensional ℂ M] [Nontrivial M] [IsSemisimpleModule R M]
    (h : IsIsotypic R M) : Nonempty (IsotypicMatrixModel R M) := by
  have : Module.Finite R M := Module.Finite.of_restrictScalars_finite ℂ R M
  obtain ⟨m, hm, S, hS, ⟨e⟩⟩ := h.linearEquiv_fun
  let : IsSimpleModule R S := hS
  have : Nontrivial S := IsSimpleModule.nontrivial R S
  have : FiniteDimensional ℂ S :=
    Module.Finite.of_injective (S.subtype.restrictScalars ℂ) S.subtype_injective
  let F := (isotypicLift e).comp (Matrix.toLinAlgEquiv (Module.finBasis ℂ S)).toAlgHom
  refine ⟨{ degree := Module.finrank ℂ S
            degree_pos := Module.finrank_pos
            lift := F
            lift_image := ?_
            orbit := ?_ }⟩
  · intro A
    exact isotypicLift_range e _
  · intro v
    exact ⟨LinearMap.range (isotypicOrbitMap e v), mem_isotypicOrbitMap_range e v,
      isotypicOrbitMap_range_invariant e v, finrank_isotypicOrbitMap_range e v⟩

end PartialPermutation

end

end OAI
