import Mathlib
import OAI.RepresentationTheory.PartialPermutation.Characters
import OAI.RepresentationTheory.PartialPermutation.IsotypicMatrices

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open scoped MonoidAlgebra BigOperators

namespace PartialPermutation
open scoped MonoidAlgebra BigOperators ComplexConjugate

noncomputable section
variable {G M : Type*} [Group G]
    [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M]

lemma ofModule'_algebra : (Representation.ofModule' (k := ℂ) (G := G) M).asAlgebraHom =
    Algebra.lsmul ℂ ℂ M := by
  exact (MonoidAlgebra.lift ℂ (Module.End ℂ M) G).apply_symm_apply _

lemma ofModule'_apply (g : G) (x : M) :
    Representation.ofModule' (k := ℂ) (G := G) M g x =
      (MonoidAlgebra.single g (1 : ℂ)) • x := by
  rw [← Representation.asAlgebraHom_single_one, ofModule'_algebra]
  rfl

noncomputable def ofModule'ModuleEquiv :
    (Representation.ofModule' (k := ℂ) (G := G) M).asModule ≃ₗ[ℂ[G]] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change (Representation.ofModule' (k := ℂ) (G := G) M).asAlgebraHom a x = a • (show M from x)
    rw [ofModule'_algebra]
    rfl

lemma ofModule'_irreducible [IsSimpleModule ℂ[G] M] :
    Representation.IsIrreducible (Representation.ofModule' (k := ℂ) (G := G) M) := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact IsSimpleModule.congr (ofModule'ModuleEquiv (G := G) (M := M))

structure IsotypicKernelModel (G M : Type*) [Group G] [Fintype G]
    [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M] extends IsotypicMatrixModel ℂ[G] M where
  kernel : G → ℂ
  kernel_norm : ∑ g, ‖kernel g‖^2 = (degree : ℝ)^2 / Fintype.card G
  kernel_inv : ∀ g, kernel g⁻¹ = conj (kernel g)
  kernel_action : ∀ x : M, ∑ g, kernel g • (MonoidAlgebra.single g (1 : ℂ)) • x = x

variable [Fintype G]

lemma exists_isotypicKernelModel [FiniteDimensional ℂ M] [Nontrivial M]
    (h : IsIsotypic ℂ[G] M)
    (hu : ∀ (g : G) (x y : M), inner ℂ ((MonoidAlgebra.single g (1 : ℂ)) • x)
      ((MonoidAlgebra.single g (1 : ℂ)) • y) = inner ℂ x y) :
    Nonempty (IsotypicKernelModel G M) := by
  have : Module.Finite ℂ[G] M := Module.Finite.of_restrictScalars_finite ℂ ℂ[G] M
  obtain ⟨m, hm, S, hS, ⟨e⟩⟩ := h.linearEquiv_fun
  let : IsSimpleModule ℂ[G] S := hS
  have : Nontrivial S := IsSimpleModule.nontrivial ℂ[G] S
  have : FiniteDimensional ℂ S :=
    Module.Finite.of_injective (S.subtype.restrictScalars ℂ) S.subtype_injective
  let : NormedAddCommGroup S := inferInstanceAs (NormedAddCommGroup (S.restrictScalars ℂ))
  let : InnerProductSpace ℂ S := inferInstanceAs (InnerProductSpace ℂ (S.restrictScalars ℂ))
  let σ := Representation.ofModule' (k := ℂ) (G := G) S
  have : Representation.IsIrreducible σ := ofModule'_irreducible
  have hσ : IsUnitary σ := by
    intro g x y
    change inner ℂ (Representation.ofModule' (k := ℂ) (G := G) S g x)
      (Representation.ofModule' (k := ℂ) (G := G) S g y) = _
    rw [ofModule'_apply, ofModule'_apply]
    exact hu g x.val y.val
  let k : G → ℂ := fun g => ((Module.finrank ℂ S : ℂ) / Fintype.card G) * conj (σ.character g)
  let F := (isotypicLift e).comp (Matrix.toLinAlgEquiv (Module.finBasis ℂ S)).toAlgHom
  refine ⟨{ degree := Module.finrank ℂ S
            degree_pos := Module.finrank_pos
            lift := F
            lift_image := fun A => isotypicLift_range e _
            orbit := fun v => ⟨LinearMap.range (isotypicOrbitMap e v),
              mem_isotypicOrbitMap_range e v, isotypicOrbitMap_range_invariant e v,
              finrank_isotypicOrbitMap_range e v⟩
            kernel := k
            kernel_norm := ?_
            kernel_inv := ?_
            kernel_action := ?_ }⟩
  · have hN : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [k, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_conj,
      mul_pow, ← Finset.mul_sum, character_norm_sq_sum σ hσ]
    field_simp
  · intro g
    simp [k, unitary_character_inv σ hσ]
  · have he' := congrArg (isotypicLift e) (character_kernel_identity σ hσ)
    have ha (g : G) : isotypicLift e (σ g) =
        Algebra.lsmul ℂ ℂ M (MonoidAlgebra.single g (1 : ℂ)) := by
      change isotypicLift e (Representation.ofModule' (k := ℂ) (G := G) S g) = _
      rw [← Representation.asAlgebraHom_single_one, ofModule'_algebra, isotypicLift_action]
    change isotypicLift e (complexFourier σ k) = isotypicLift e 1 at he'
    simp only [complexFourier, map_sum, map_smul, map_one, ha] at he'
    intro x
    have ht := congrArg (fun A : Module.End ℂ M => A x) he'
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, Algebra.lsmul_apply,
      Module.End.one_apply] using ht

end
end PartialPermutation

end

end OAI
