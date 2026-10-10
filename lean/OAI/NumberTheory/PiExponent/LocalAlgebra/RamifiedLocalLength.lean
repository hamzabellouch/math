import Mathlib

namespace OAI

open IsLocalRing TensorProduct

namespace PiExponent.RamifiedLocalLength

theorem residueField_map_surjective_of_mod_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    (P : Ideal R) [P.IsPrime] (Q : Ideal S) [Q.IsMaximal]
    (f : R →+* S) (hPQ : P = Q.comap f)
    (hs : ∀ y : S, ∃ x : R, y - f x ∈ Q) :
    Function.Surjective (Ideal.ResidueField.map P Q f hPQ) := by
  intro z
  obtain ⟨y, rfl⟩ := Q.algebraMap_residueField_surjective z
  obtain ⟨x, hx⟩ := hs y
  refine ⟨algebraMap R P.ResidueField x, ?_⟩
  rw [Ideal.ResidueField.map_algebraMap]
  have hz := (Ideal.algebraMap_residueField_eq_zero (I := Q)).mpr hx
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

variable {A B : Type*} [CommRing A] [CommRing B]
  [IsLocalRing A] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)] [Module.Free A B] [Module.Finite A B]

theorem closed_fibre_length_eq_finrank
    (hres : Function.Surjective (algebraMap (ResidueField A) (ResidueField B))) :
    Module.length B (B ⧸ (maximalIdeal A).map (algebraMap A B)) =
      (Module.finrank A B : ℕ∞) := by
  let I : Ideal B := (maximalIdeal A).map (algebraMap A B)
  have hreslen : Module.length (ResidueField A) (ResidueField B) = 1 := by
    rw [Module.length_eq_of_surjective hres]
    exact Module.length_eq_one _ _
  have hrestrict := IsLocalRing.length_restrictScalars A B (B ⧸ I)
  rw [hreslen, mul_one] at hrestrict
  rw [← hrestrict]
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  let : Module.Finite (A ⧸ maximalIdeal A) (B ⧸ I) :=
    Module.Finite.of_restrictScalars_finite A _ _
  calc
    Module.length A (B ⧸ I) = Module.length (A ⧸ maximalIdeal A) (B ⧸ I) :=
      Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
    _ = (Module.finrank (A ⧸ maximalIdeal A) (B ⧸ I) : ℕ∞) :=
      Module.length_eq_finrank _ _
    _ = (Module.finrank A B : ℕ∞) := by
      rw [IsLocalRing.finrank_quotient_map]

theorem length_baseChange_eq_finrank_mul
    (hres : Function.Surjective (algebraMap (ResidueField A) (ResidueField B)))
    (M : Type*) [AddCommGroup M] [Module A M] :
    Module.length B (B ⊗[A] M) =
      Module.length A M * (Module.finrank A B : ℕ∞) := by
  rw [IsLocalRing.length_baseChange, closed_fibre_length_eq_finrank hres]

theorem length_quotient_map_eq_finrank_mul
    (hres : Function.Surjective (algebraMap (ResidueField A) (ResidueField B)))
    (I : Ideal A) :
    Module.length B (B ⧸ I.map (algebraMap A B)) =
      Module.length A (A ⧸ I) * (Module.finrank A B : ℕ∞) := by
  rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.length_eq]
  exact length_baseChange_eq_finrank_mul hres (A ⧸ I)

end PiExponent.RamifiedLocalLength

end OAI
