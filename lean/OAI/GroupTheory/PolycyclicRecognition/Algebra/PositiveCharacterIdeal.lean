import OAI.GroupTheory.PolycyclicRecognition.Algebra.PositiveAnnihilatorCriterion
import Mathlib.Algebra.MonoidAlgebra.Ideal
import Mathlib.RingTheory.Finiteness.Nakayama

namespace OAI

/-! # The positive character ideal and the determinant trick

Finite generation over a character monoid forces an identity supported in its
strictly positive part. This is the reverse of the positive identity criterion.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra

section Nakayama
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem ideal_identity_of_surjective_scalar [Module.Finite R V]
    (I : Ideal R) (r : R) (hr : r ∈ I)
    (hsurj : Function.Surjective (fun x : V => r • x)) :
    ∃ a ∈ I, ∀ x : V, a • x = x := by
  have hle : (⊤ : Submodule R V) ≤ I • (⊤ : Submodule R V) := by
    intro x _
    obtain ⟨y, rfl⟩ := hsurj x
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  obtain ⟨a, ha, hax⟩ :=
    Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I ⊤ Module.Finite.fg_top hle
  exact ⟨a, ha, fun x => hax x Submodule.mem_top⟩
end Nakayama

theorem representation_mapDomain {Q M : Type} [Monoid Q] [AddCommGroup M]
    (ρ : Representation ℤ Q M) {P : Type} [Monoid P]
    (f : P →* Q) (a : ℤ[P]) :
    ρ.asAlgebraHom (MonoidAlgebra.mapDomain f a) = Representation.asAlgebraHom (ρ.comp f) a := by
  induction a using MonoidAlgebra.induction_on with
  | of q =>
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.mapDomain_single,
      Representation.asAlgebraHom_single_one]
    rfl
  | add a b ha hb =>
    simp only [MonoidAlgebra.mapDomain_add, map_add, ha, hb]
  | smul r a ha =>
    simp only [MonoidAlgebra.mapDomain_smul, map_smul, ha]

variable {Q M : Type} [CommGroup Q] [AddCommGroup M]

def characterPositiveIdeal (χ : Q →* Multiplicative ℝ) :
    Ideal ℤ[characterNonnegativeMonoid χ] :=
  Ideal.span (MonoidAlgebra.of ℤ (characterNonnegativeMonoid χ) ''
    {q | 0 < (χ (q : Q)).toAdd})

theorem mem_characterPositiveIdeal_iff (χ : Q →* Multiplicative ℝ)
    (a : ℤ[characterNonnegativeMonoid χ]) :
    a ∈ characterPositiveIdeal χ ↔
      ∀ q ∈ a.coeff.support, 0 < (χ (q : Q)).toAdd := by
  rw [characterPositiveIdeal, MonoidAlgebra.mem_ideal_span_of_image]
  constructor
  · intro h q hq
    obtain ⟨r, hr, d, rfl⟩ := h q hq
    change 0 < (χ ((d : Q) * (r : Q))).toAdd
    rw [map_mul]
    exact add_pos_of_nonneg_of_pos d.property hr
  · intro h q hq
    exact ⟨q, h q hq, 1, (one_mul q).symm⟩

theorem positive_monomial_mem_characterPositiveIdeal (χ : Q →* Multiplicative ℝ)
    (t : Q) (ht : 0 < (χ t).toAdd) :
    MonoidAlgebra.of ℤ (characterNonnegativeMonoid χ) ⟨t, ht.le⟩ ∈
      characterPositiveIdeal χ := by
  exact Ideal.subset_span ⟨⟨t, ht.le⟩, ht, rfl⟩

theorem characterMonoid_positive_identity (ρ : Representation ℤ Q M)
    (χ : Q →* Multiplicative ℝ)
    [Module.Finite ℤ[characterNonnegativeMonoid χ] (characterMonoidRepresentation ρ χ).asModule]
    (t : Q) (ht : 0 < (χ t).toAdd) :
    ∃ a : ℤ[characterNonnegativeMonoid χ], a ∈ characterPositiveIdeal χ ∧
      (characterMonoidRepresentation ρ χ).asAlgebraHom a = 1 := by
  let σ := characterMonoidRepresentation ρ χ
  let r := MonoidAlgebra.of ℤ (characterNonnegativeMonoid χ) ⟨t, ht.le⟩
  have hsurj : Function.Surjective (fun x : σ.asModule => r • x) := by
    intro x
    refine ⟨σ.asModuleEquiv.symm (ρ t⁻¹ (σ.asModuleEquiv x)), ?_⟩
    apply σ.asModuleEquiv.injective
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of,
      LinearEquiv.apply_symm_apply]
    exact ρ.self_inv_apply t (σ.asModuleEquiv x)
  obtain ⟨a, ha, hax⟩ := ideal_identity_of_surjective_scalar
    (characterPositiveIdeal χ) r (positive_monomial_mem_characterPositiveIdeal χ t ht) hsurj
  refine ⟨a, ha, ?_⟩
  ext x
  change σ.asAlgebraHom a x = x
  have h := congrArg σ.asModuleEquiv (hax (σ.asModuleEquiv.symm x))
  simpa only [Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply] using h

/-- A nonzero character direction with finite monoid generation admits an
actual group-ring identity whose support lies in the strict positive half-space. -/
theorem positive_identity_of_finite_characterMonoidModule
    (ρ : Representation ℤ Q M) (χ : Q →* Multiplicative ℝ)
    [Module.Finite ℤ[characterNonnegativeMonoid χ] (characterMonoidRepresentation ρ χ).asModule]
    (t : Q) (ht : 0 < (χ t).toAdd) :
    ∃ a : ℤ[Q], (∀ q ∈ a.coeff.support, 0 < (χ q).toAdd) ∧ ρ.asAlgebraHom a = 1 := by
  classical
  obtain ⟨b, hb, hid⟩ := characterMonoid_positive_identity ρ χ t ht
  refine ⟨MonoidAlgebra.mapDomain (characterNonnegativeMonoid χ).subtype b, ?_, ?_⟩
  · intro q hq
    have hq' : q ∈ b.coeff.support.image (characterNonnegativeMonoid χ).subtype :=
      Finsupp.mapDomain_support hq
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq'
    exact (mem_characterPositiveIdeal_iff χ b).mp hb r hr
  · rw [representation_mapDomain]
    exact hid

/-- The positive identity criterion, with both directions proved. -/
theorem finite_characterMonoidModule_iff_positive_identity
    (ρ : Representation ℤ Q M) [Module.Finite ℤ[Q] ρ.asModule]
    (χ : Q →* Multiplicative ℝ) (t : Q) (ht : 0 < (χ t).toAdd) :
    Module.Finite ℤ[characterNonnegativeMonoid χ] (characterMonoidRepresentation ρ χ).asModule ↔
      ∃ a : ℤ[Q], (∀ q ∈ a.coeff.support, 0 < (χ q).toAdd) ∧ ρ.asAlgebraHom a = 1 := by
  constructor
  · intro h
    let := h
    exact positive_identity_of_finite_characterMonoidModule ρ χ t ht
  · rintro ⟨a, ha, hid⟩
    exact finite_characterMonoidModule_of_positive_identity ρ χ a ha hid

end PolycyclicRecognition

end

end OAI
