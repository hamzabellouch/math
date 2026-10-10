import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.TensorProduct.Quotient

namespace OAI

namespace SiegelZeros

section

noncomputable section
open Polynomial IsLocalRing

namespace W58

variable (k : Type*) [Field k]

def parameterIdeal : Ideal k[X] := RingHom.ker Polynomial.constantCoeff

instance parameterIdeal_isMaximal : (parameterIdeal k).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective Polynomial.constantCoeff
    Polynomial.constantCoeff_surjective

abbrev ParameterLocalRing := Localization.AtPrime (parameterIdeal k)

lemma parameterIdeal_eq_span_X : parameterIdeal k = Ideal.span {(X : k[X])} :=
  Polynomial.ker_constantCoeff

lemma parameterIdeal_mem_iff (f : k[X]) : f ∈ parameterIdeal k ↔ f.coeff 0 = 0 :=
  Iff.rfl

variable {k} {R : Type*} [CommRing R] [IsDomain R] [Algebra k R]

lemma nonunit_transcendental {π : R} (hπ0 : π ≠ 0) (hπu : ¬ IsUnit π) :
    Transcendental k π := by
  intro h
  exact hπu (h.isIntegral.isUnit hπ0)

lemma uniformizer_aeval_injective {π : R} (hπ : Irreducible π) :
    Function.Injective (Polynomial.aeval π : k[X] →ₐ[k] R) :=
  transcendental_iff_injective.mp (nonunit_transcendental hπ.ne_zero hπ.not_isUnit)

variable [IsDiscreteValuationRing R]

lemma uniformizer_residue_zero {π : R} (hπ : Irreducible π) :
    residue R π = 0 := by
  apply (residue_eq_zero_iff π).mpr
  rw [hπ.maximalIdeal_eq]
  exact Ideal.subset_span (Set.mem_singleton π)

lemma residue_aeval_uniformizer {π : R} (hπ : Irreducible π) (f : k[X]) :
    residue R (Polynomial.aeval π f) =
      algebraMap k (ResidueField R) (f.coeff 0) := by
  change residue R (f.eval₂ (algebraMap k R) π) = _
  rw [Polynomial.hom_eval₂, uniformizer_residue_zero hπ, Polynomial.eval₂_at_zero]
  rfl

lemma uniformizer_aeval_isUnit_iff {π : R} (hπ : Irreducible π) (f : k[X]) :
    IsUnit (Polynomial.aeval π f) ↔ f.coeff 0 ≠ 0 := by
  rw [← residue_ne_zero_iff_isUnit, residue_aeval_uniformizer hπ]
  constructor
  · intro h hz
    exact h (by simp [hz])
  · intro h hz
    exact h ((algebraMap k (ResidueField R)).injective (hz.trans (map_zero _).symm))

lemma uniformizer_denominators_units {π : R} (hπ : Irreducible π)
    (f : (parameterIdeal k).primeCompl) : IsUnit (Polynomial.aeval π f.val) := by
  apply (uniformizer_aeval_isUnit_iff hπ f.val).mpr
  exact f.property

def uniformizerLocalMap {π : R} (hπ : Irreducible π) : ParameterLocalRing k →ₐ[k] R :=
  IsLocalization.liftAlgHom (uniformizer_denominators_units (k := k) hπ)

@[simp]
lemma uniformizerLocalMap_algebraMap {π : R} (hπ : Irreducible π) (f : k[X]) :
    uniformizerLocalMap (k := k) hπ (algebraMap k[X] (ParameterLocalRing k) f) =
      Polynomial.aeval π f :=
  IsLocalization.lift_eq (uniformizer_denominators_units (k := k) hπ) f

lemma uniformizerLocalMap_injective {π : R} (hπ : Irreducible π) :
    Function.Injective (uniformizerLocalMap (k := k) hπ) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (parameterIdeal k).primeCompl (uniformizerLocalMap (k := k) hπ).toRingHom).mpr
  intro f g
  constructor
  · intro h
    exact congrArg (uniformizerLocalMap (k := k) hπ).toRingHom h
  · intro h
    have heval : Polynomial.aeval π f = Polynomial.aeval π g := by
      calc
        Polynomial.aeval π f = uniformizerLocalMap (k := k) hπ
            (algebraMap k[X] (ParameterLocalRing k) f) :=
          (uniformizerLocalMap_algebraMap (k := k) hπ f).symm
        _ = uniformizerLocalMap (k := k) hπ
            (algebraMap k[X] (ParameterLocalRing k) g) := h
        _ = Polynomial.aeval π g := uniformizerLocalMap_algebraMap (k := k) hπ g
    exact congrArg (algebraMap k[X] (ParameterLocalRing k))
      (uniformizer_aeval_injective (k := k) hπ heval)

lemma uniformizerLocalMap_maximalIdeal {π : R} (hπ : Irreducible π) :
    (maximalIdeal (ParameterLocalRing k)).map (uniformizerLocalMap (k := k) hπ).toRingHom =
      maximalIdeal R := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
    (parameterIdeal k) (ParameterLocalRing k), Ideal.map_map]
  have hcomp : (uniformizerLocalMap (k := k) hπ).toRingHom.comp
      (algebraMap k[X] (ParameterLocalRing k)) = (Polynomial.aeval π).toRingHom := by
    apply RingHom.ext
    intro f
    exact uniformizerLocalMap_algebraMap (k := k) hπ f
  rw [hcomp, parameterIdeal_eq_span_X, Ideal.map_span, Set.image_singleton]
  simpa using hπ.maximalIdeal_eq.symm

lemma uniformizerLocalMap_isLocalHom {π : R} (hπ : Irreducible π) :
    IsLocalHom (uniformizerLocalMap (k := k) hπ).toRingHom := by
  apply ((IsLocalRing.local_hom_TFAE (uniformizerLocalMap (k := k) hπ).toRingHom).out 3 1).mp
  exact le_of_eq (uniformizerLocalMap_maximalIdeal (k := k) hπ)

abbrev uniformizerLocalAlgebra {π : R} (hπ : Irreducible π) :
    Algebra (ParameterLocalRing k) R := (uniformizerLocalMap (k := k) hπ).toRingHom.toAlgebra

lemma uniformizerLocalAlgebra_flat {π : R} (hπ : Irreducible π) :
    letI := uniformizerLocalAlgebra (k := k) hπ
    Module.Flat (ParameterLocalRing k) R := by
  let := uniformizerLocalAlgebra (k := k) hπ
  let : Module.IsTorsionFree (ParameterLocalRing k) R :=
    Module.IsTorsionFree.of_smul_eq_zero fun a r har ↦ by
      change uniformizerLocalMap (k := k) hπ a * r = 0 at har
      rcases mul_eq_zero.mp har with ha | hr
      · exact Or.inl (uniformizerLocalMap_injective (k := k) hπ (ha.trans (map_zero _).symm))
      · exact Or.inr hr
  infer_instance

lemma formallySmooth_of_essFiniteType_flat_smoothFiber
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B] [Module.Flat A B]
    [Algebra.FormallySmooth (ResidueField A)
      (TensorProduct A (ResidueField A) B)] : Algebra.FormallySmooth A B := by
  let P := Algebra.EssFiniteType.subalgebra A B
  let : Algebra.FinitePresentation A P :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
    (Algebra.EssFiniteType.submonoid A B)

lemma formallySmooth_of_flat_map_maximalIdeal
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B] [Module.Flat A B]
    [PerfectField (ResidueField A)]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    Algebra.FormallySmooth A B := by
  have : ((maximalIdeal A).map (algebraMap A B)).IsMaximal := by
    rw [h]
    infer_instance
  let : Field (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    Ideal.Quotient.field ((maximalIdeal A).map (algebraMap A B))
  let : Algebra (ResidueField A)
      (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (R := A) (A := B) (p := maximalIdeal A)
      (P := (maximalIdeal A).map (algebraMap A B)) Ideal.le_comap_map
  let : IsScalarTower A (ResidueField A)
      (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.EssFiniteType A
      (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    Algebra.EssFiniteType.comp A B _
  let : Algebra.EssFiniteType (ResidueField A)
      (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    Algebra.EssFiniteType.of_comp A (ResidueField A) _
  let : Algebra.FormallySmooth (ResidueField A)
      (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    Algebra.FormallySmooth.of_perfectField
  let : Algebra.FormallySmooth (ResidueField A)
      (TensorProduct A (ResidueField A) B) :=
    Algebra.FormallySmooth.of_equiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal A))
  exact formallySmooth_of_essFiniteType_flat_smoothFiber A B

theorem dvr_formallySmooth_of_essFiniteType [CharZero k] [Algebra.EssFiniteType k R] :
    Algebra.FormallySmooth k R := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let A := ParameterLocalRing k
  let := uniformizerLocalAlgebra (k := k) hπ
  let : IsScalarTower k A R := IsScalarTower.of_algHom (uniformizerLocalMap (k := k) hπ)
  let : IsLocalHom (algebraMap A R) := uniformizerLocalMap_isLocalHom (k := k) hπ
  let : Module.Flat A R := uniformizerLocalAlgebra_flat (k := k) hπ
  let : Algebra.EssFiniteType A R := Algebra.EssFiniteType.of_comp k A R
  let : CharZero (ResidueField A) :=
    charZero_of_injective_algebraMap (algebraMap k (ResidueField A)).injective
  let : Algebra.FormallySmooth A R :=
    formallySmooth_of_flat_map_maximalIdeal A R (uniformizerLocalMap_maximalIdeal (k := k) hπ)
  exact Algebra.FormallySmooth.comp k A R

end W58

end

end

end SiegelZeros

end OAI
