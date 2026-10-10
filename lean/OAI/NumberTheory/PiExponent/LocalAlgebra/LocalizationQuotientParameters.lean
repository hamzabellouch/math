import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedLengthEquivalence

namespace OAI

noncomputable section
namespace PiExponentSiegel.W23

variable {A : Type*} [CommRing A]

def quotientParameterPrime (I m : Ideal A) (_hI : I ≤ m) : Ideal (A ⧸ I) :=
  m.map (Ideal.Quotient.mk I)

instance quotientParameterPrime_isPrime (I m : Ideal A) [m.IsPrime] (hI : I ≤ m) :
    (quotientParameterPrime I m hI).IsPrime :=
  Ideal.map_isPrime_of_surjective (f := Ideal.Quotient.mk I) (I := m)
    Ideal.Quotient.mk_surjective
    (by simpa only [Ideal.mk_ker] using hI)

instance quotientParameterPrime_isMaximal (I m : Ideal A) [m.IsMaximal] (hI : I ≤ m) :
    (quotientParameterPrime I m hI).IsMaximal :=
  Ideal.IsMaximal.map_of_surjective_of_ker_le (f := Ideal.Quotient.mk I) (m := m)
    Ideal.Quotient.mk_surjective
    (by simpa only [Ideal.mk_ker] using hI)

@[simp] theorem mem_quotientParameterPrime_mk (I m : Ideal A) (hI : I ≤ m) (a : A) :
    Ideal.Quotient.mk I a ∈ quotientParameterPrime I m hI ↔ a ∈ m :=
  Ideal.mem_quotient_iff_mem hI

def parameterLocalizedIdeal (I m : Ideal A) [m.IsPrime] :
    Ideal (Localization.AtPrime m) :=
  I.map (algebraMap A (Localization.AtPrime m))

variable (I m : Ideal A) [m.IsPrime] (hI : I ≤ m)

def parameterLocalizationMap :
    Localization.AtPrime m →+* Localization.AtPrime (quotientParameterPrime I m hI) :=
  IsLocalization.map (Localization.AtPrime (quotientParameterPrime I m hI))
    (Ideal.Quotient.mk I) (M := m.primeCompl)
    (S := Localization.AtPrime m)
    (T := (quotientParameterPrime I m hI).primeCompl) (by
      intro a ha
      change Ideal.Quotient.mk I a ∉ quotientParameterPrime I m hI
      exact fun h => ha ((mem_quotientParameterPrime_mk I m hI a).mp h))

@[simp] theorem parameterLocalizationMap_algebraMap (a : A) :
    parameterLocalizationMap I m hI (algebraMap A (Localization.AtPrime m) a) =
      algebraMap (A ⧸ I) (Localization.AtPrime (quotientParameterPrime I m hI))
        (Ideal.Quotient.mk I a) :=
  IsLocalization.map_eq _ a

theorem parameterLocalizedIdeal_le_ker :
    parameterLocalizedIdeal I m ≤ RingHom.ker (parameterLocalizationMap I m hI) := by
  rw [parameterLocalizedIdeal, Ideal.map_le_iff_le_comap]
  intro a ha
  change parameterLocalizationMap I m hI (algebraMap A (Localization.AtPrime m) a) = 0
  rw [parameterLocalizationMap_algebraMap,
    (Ideal.Quotient.eq_zero_iff_mem).mpr ha, map_zero]

def parameterLocalQuotientForward :
    (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) →+*
      Localization.AtPrime (quotientParameterPrime I m hI) :=
  Ideal.Quotient.lift _ (parameterLocalizationMap I m hI)
    (fun x hx => (RingHom.mem_ker (f := parameterLocalizationMap I m hI) (r := x)).mp
      (parameterLocalizedIdeal_le_ker I m hI hx))

@[simp] theorem parameterLocalQuotientForward_mk (x : Localization.AtPrime m) :
    parameterLocalQuotientForward I m hI (Ideal.Quotient.mk _ x) =
      parameterLocalizationMap I m hI x := rfl

def parameterQuotientToLocalQuotient :
    (A ⧸ I) →+* (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) :=
  Ideal.Quotient.lift I
    ((Ideal.Quotient.mk (parameterLocalizedIdeal I m)).comp
      (algebraMap A (Localization.AtPrime m)))
    (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha))

@[simp] theorem parameterQuotientToLocalQuotient_mk (a : A) :
    parameterQuotientToLocalQuotient I m (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (parameterLocalizedIdeal I m)
        (algebraMap A (Localization.AtPrime m) a) := rfl

theorem parameterQuotientToLocalQuotient_units
    (s : (quotientParameterPrime I m hI).primeCompl) :
    IsUnit (parameterQuotientToLocalQuotient I m (s : A ⧸ I)) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (s : A ⧸ I)
  have ham : a ∉ m := by
    intro ham
    apply s.property
    change (s : A ⧸ I) ∈ m.map (Ideal.Quotient.mk I)
    rw [← ha]
    exact Ideal.mem_map_of_mem _ ham
  rw [← ha, parameterQuotientToLocalQuotient_mk]
  exact (IsLocalization.map_units (Localization.AtPrime m) (⟨a, ham⟩ : m.primeCompl)).map
    (Ideal.Quotient.mk (parameterLocalizedIdeal I m))

def parameterLocalQuotientReverse :
    Localization.AtPrime (quotientParameterPrime I m hI) →+*
      (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) :=
  IsLocalization.lift (M := (quotientParameterPrime I m hI).primeCompl)
    (S := Localization.AtPrime (quotientParameterPrime I m hI))
    (parameterQuotientToLocalQuotient_units I m hI)

@[simp] theorem parameterLocalQuotientReverse_algebraMap (x : A ⧸ I) :
    parameterLocalQuotientReverse I m hI
      (algebraMap (A ⧸ I) (Localization.AtPrime (quotientParameterPrime I m hI)) x) =
      parameterQuotientToLocalQuotient I m x :=
  IsLocalization.lift_eq _ x

theorem parameterLocalQuotient_reverse_forward :
    (parameterLocalQuotientReverse I m hI).comp (parameterLocalQuotientForward I m hI) =
      RingHom.id (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) := by
  apply Ideal.Quotient.ringHom_ext
  apply IsLocalization.ringHom_ext m.primeCompl
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply, RingHom.id_apply, parameterLocalQuotientForward_mk,
    parameterLocalizationMap_algebraMap, parameterLocalQuotientReverse_algebraMap,
    parameterQuotientToLocalQuotient_mk]

theorem parameterLocalQuotient_forward_reverse :
    (parameterLocalQuotientForward I m hI).comp (parameterLocalQuotientReverse I m hI) =
      RingHom.id (Localization.AtPrime (quotientParameterPrime I m hI)) := by
  apply IsLocalization.ringHom_ext (quotientParameterPrime I m hI).primeCompl
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply, RingHom.id_apply, parameterLocalQuotientReverse_algebraMap,
    parameterQuotientToLocalQuotient_mk, parameterLocalQuotientForward_mk,
    parameterLocalizationMap_algebraMap]

def localizationQuotientParametersEquiv :
    (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) ≃+*
      Localization.AtPrime (quotientParameterPrime I m hI) where
  toFun := parameterLocalQuotientForward I m hI
  invFun := parameterLocalQuotientReverse I m hI
  left_inv x := RingHom.congr_fun (parameterLocalQuotient_reverse_forward I m hI) x
  right_inv x := RingHom.congr_fun (parameterLocalQuotient_forward_reverse I m hI) x
  map_mul' := (parameterLocalQuotientForward I m hI).map_mul
  map_add' := (parameterLocalQuotientForward I m hI).map_add

@[simp] theorem localizationQuotientParametersEquiv_mk_algebraMap (a : A) :
    localizationQuotientParametersEquiv I m hI
      (Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime m) a)) =
    algebraMap (A ⧸ I) (Localization.AtPrime (quotientParameterPrime I m hI))
      (Ideal.Quotient.mk I a) :=
  parameterLocalizationMap_algebraMap I m hI a

include hI in

theorem parameterLocalQuotient_isLocalRing :
    IsLocalRing (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) :=
  (localizationQuotientParametersEquiv I m hI).symm.isLocalRing

theorem localizationQuotientParametersEquiv_maximalIdeal :
    letI := parameterLocalQuotient_isLocalRing I m hI
    (IsLocalRing.maximalIdeal (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m)).map
      (localizationQuotientParametersEquiv I m hI).toRingHom =
      IsLocalRing.maximalIdeal (Localization.AtPrime (quotientParameterPrime I m hI)) := by
  let := parameterLocalQuotient_isLocalRing I m hI
  exact IsLocalRing.map_ringEquiv_maximalIdeal (localizationQuotientParametersEquiv I m hI)

def localizationQuotientParametersResidueEquiv :
    letI := parameterLocalQuotient_isLocalRing I m hI
    IsLocalRing.ResidueField (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) ≃+*
      IsLocalRing.ResidueField (Localization.AtPrime (quotientParameterPrime I m hI)) := by
  letI := parameterLocalQuotient_isLocalRing I m hI
  exact IsLocalRing.ResidueField.mapEquiv (localizationQuotientParametersEquiv I m hI)

theorem localizationQuotientParametersResidueEquiv_residue
    (x : Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) :
    letI := parameterLocalQuotient_isLocalRing I m hI
    localizationQuotientParametersResidueEquiv I m hI (IsLocalRing.residue _ x) =
      IsLocalRing.residue _ (localizationQuotientParametersEquiv I m hI x) := by
  let := parameterLocalQuotient_isLocalRing I m hI
  let : IsLocalHom (localizationQuotientParametersEquiv I m hI).toRingHom :=
    IsLocalHom.of_surjective (localizationQuotientParametersEquiv I m hI).toRingHom
      (localizationQuotientParametersEquiv I m hI).surjective
  exact IsLocalRing.ResidueField.map_residue
    (localizationQuotientParametersEquiv I m hI).toRingHom x

theorem parameterLocalizedIdeal_span_singleton (x : A) :
    parameterLocalizedIdeal (Ideal.span {x}) m =
      Ideal.span {algebraMap A (Localization.AtPrime m) x} := by
  simp only [parameterLocalizedIdeal, Ideal.map_span, Set.image_singleton]

variable {B : Type*} [CommRing B]

local instance parameterEquivImage_isPrime (e : A ≃+* B) (P : Ideal A) [P.IsPrime] :
    (P.map e.toRingHom).IsPrime :=
  Ideal.map_isPrime_of_equiv e

theorem atPrimeImage_comap (e : A ≃+* B) (P : Ideal A) :
    P = (P.map e.toRingHom).comap e.toRingHom := by
  ext a
  change a ∈ P ↔ e a ∈ P.map e.toRingHom
  exact Ideal.apply_mem_of_equiv_iff.symm

def atPrimeEquivOfRingEquiv (e : A ≃+* B) (P : Ideal A) [P.IsPrime] :
    Localization.AtPrime P ≃+* Localization.AtPrime (P.map e.toRingHom) :=
  PiExponentJets.W22.primeLocalizationEquiv e P (P.map e.toRingHom)
    (atPrimeImage_comap e P)

@[simp] theorem atPrimeEquivOfRingEquiv_algebraMap
    (e : A ≃+* B) (P : Ideal A) [P.IsPrime] (a : A) :
    atPrimeEquivOfRingEquiv e P (algebraMap A (Localization.AtPrime P) a) =
      algebraMap B (Localization.AtPrime (P.map e.toRingHom)) (e a) :=
  IsLocalization.ringEquivOfRingEquiv_eq
    (PiExponentJets.W22.primeCompl_map_eq_of_comap e P (P.map e.toRingHom)
      (atPrimeImage_comap e P)) a

def localizationQuotientParametersEquivTrans (e : (A ⧸ I) ≃+* B) :
    (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) ≃+*
      Localization.AtPrime ((quotientParameterPrime I m hI).map e.toRingHom) :=
  (localizationQuotientParametersEquiv I m hI).trans
    (atPrimeEquivOfRingEquiv e (quotientParameterPrime I m hI))

@[simp] theorem localizationQuotientParametersEquivTrans_mk_algebraMap
    (e : (A ⧸ I) ≃+* B) (a : A) :
    localizationQuotientParametersEquivTrans I m hI e
      (Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime m) a)) =
      algebraMap B
        (Localization.AtPrime ((quotientParameterPrime I m hI).map e.toRingHom))
        (e (Ideal.Quotient.mk I a)) := by
  simp only [localizationQuotientParametersEquivTrans, RingEquiv.trans_apply,
    localizationQuotientParametersEquiv_mk_algebraMap, atPrimeEquivOfRingEquiv_algebraMap]

end PiExponentSiegel.W23

end

end OAI
