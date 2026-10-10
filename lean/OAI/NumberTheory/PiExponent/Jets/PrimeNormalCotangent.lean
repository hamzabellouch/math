import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential
import OAI.NumberTheory.PiExponent.Jets.ResidueConormalPairing

namespace OAI

noncomputable section

namespace PiExponent

open KaehlerDifferential
open scoped TensorProduct

def extendModuleDerivation
    {C R A E : Type*} [CommRing C] [CommRing R] [CommRing A] [CommRing E]
    [Algebra C R] [Algebra C A] [Algebra C E]
    [Algebra R A] [Algebra R E] [Algebra A E]
    [IsScalarTower C R A] [IsScalarTower C R E] [IsScalarTower C A E]
    [IsScalarTower R A E] [Algebra.FormallyEtale R A]
    (d : Derivation C R E) : Derivation C A E :=
  ((LinearMap.liftBaseChange A d.liftKaehlerDifferential).comp
    (tensorKaehlerEquivOfFormallyEtale C R A).symm.toLinearMap).compDer (D C A)

@[simp]
theorem extendModuleDerivation_algebraMap
    {C R A E : Type*} [CommRing C] [CommRing R] [CommRing A] [CommRing E]
    [Algebra C R] [Algebra C A] [Algebra C E]
    [Algebra R A] [Algebra R E] [Algebra A E]
    [IsScalarTower C R A] [IsScalarTower C R E] [IsScalarTower C A E]
    [IsScalarTower R A E] [Algebra.FormallyEtale R A]
    (d : Derivation C R E) (r : R) :
    extendModuleDerivation (A := A) d (algebraMap R A r) = d r := by
  simp [extendModuleDerivation, LinearMap.compDer,
    tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Derivation.liftKaehlerDifferential_comp_D]

variable {C ι : Type*} [Field C] [Fintype ι]
variable (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime]

abbrev PrimeLocalCotangent := IsLocalRing.CotangentSpace (Localization.AtPrime Q)

def primeResidueMap : MvPolynomial ι C →ₐ[C] Q.ResidueField :=
  IsScalarTower.toAlgHom C (MvPolynomial ι C) Q.ResidueField

def primeLocalPartial (i : ι) : Derivation C (Localization.AtPrime Q) Q.ResidueField := by
  let : Algebra.FormallyEtale (MvPolynomial ι C) (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.of_isLocalization Q.primeCompl
  exact extendModuleDerivation
    ((Algebra.linearMap (MvPolynomial ι C) Q.ResidueField).compDer (MvPolynomial.pderiv i))

omit [Fintype ι] in
@[simp]
theorem primeLocalPartial_polynomial (i : ι) (p : MvPolynomial ι C) :
    primeLocalPartial Q i (algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p) =
      algebraMap (MvPolynomial ι C) Q.ResidueField (MvPolynomial.pderiv i p) := by
  let : Algebra.FormallyEtale (MvPolynomial ι C) (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.of_isLocalization Q.primeCompl
  change extendModuleDerivation _ (algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p) = _
  rw [extendModuleDerivation_algebraMap]
  rfl

def primePartialNormal (i : ι) : PrimeLocalCotangent Q →ₗ[Q.ResidueField] Q.ResidueField :=
  PiExponentSiegel.W58.residueConormalPairing
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) (primeLocalPartial Q i)

def primeNormalPairing : (ι → Q.ResidueField) →ₗ[Q.ResidueField]
    (PrimeLocalCotangent Q →ₗ[Q.ResidueField] Q.ResidueField) where
  toFun v := ∑ i, v i • primePartialNormal Q i
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum, smul_smul]

def primePolynomialCotangent (p : Q) : PrimeLocalCotangent Q :=
  (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).toCotangent
    ⟨algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p.1,
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q p.1).mpr p.2⟩

@[simp]
theorem primeNormalPairing_polynomial (v : ι → Q.ResidueField) (p : Q) :
    primeNormalPairing Q v (primePolynomialCotangent Q p) =
      ∑ i, v i * primeResidueMap Q (MvPolynomial.pderiv i p.1) := by
  change (∑ i, v i • primePartialNormal Q i) (primePolynomialCotangent Q p) = _
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  change v i * primeLocalPartial Q i
    (algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p.1) = _
  rw [primeLocalPartial_polynomial]
  rfl

theorem primeNormalPairing_ker_le_tangent :
    LinearMap.ker (primeNormalPairing Q) ≤ polynomialTangent (primeResidueMap Q) Q := by
  intro v hv
  change primeNormalPairing Q v = 0 at hv
  change polynomialJacobian (primeResidueMap Q) Q v = 0
  ext p
  have h := LinearMap.congr_fun hv (primePolynomialCotangent Q p)
  simpa only [primeNormalPairing_polynomial, LinearMap.zero_apply,
    polynomialJacobian, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, mul_comm] using h

def primeLocalDirectional (v : ι → Q.ResidueField) :
    Derivation C (Localization.AtPrime Q) Q.ResidueField :=
  ∑ i, v i • primeLocalPartial Q i

@[simp]
theorem primeNormalPairing_toCotangent (v : ι → Q.ResidueField)
    (x : IsLocalRing.maximalIdeal (Localization.AtPrime Q)) :
    primeNormalPairing Q v ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).toCotangent x) =
      primeLocalDirectional Q v x := by
  change (∑ i, v i • primePartialNormal Q i) _ = _
  rw [LinearMap.sum_apply]
  change (∑ i, v i * primeLocalPartial Q i x.1) = _
  change (∑ i, v i * primeLocalPartial Q i x.1) =
    (Derivation.coeFnAddMonoidHom (∑ i, v i • primeLocalPartial Q i)) x.1
  rw [map_sum, Finset.sum_apply]
  rfl

theorem primeNormalPairing_linearIndependent {σ : Type*} [Fintype σ]
    (v : σ → ι → Q.ResidueField)
    (hv : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ (v j))) :
    LinearIndependent Q.ResidueField (fun j => primeNormalPairing Q (v j)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  have hp : primeNormalPairing Q (∑ j, a j • v j) = 0 := by
    simpa only [map_sum, map_smul] using ha
  have hm := primeNormalPairing_ker_le_tangent Q hp
  have hq : (polynomialTangent (primeResidueMap Q) Q).mkQ (∑ j, a j • v j) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hm
  have hsum : ∑ j, a j • (polynomialTangent (primeResidueMap Q) Q).mkQ (v j) = 0 := by
    simpa only [map_sum, map_smul] using hq
  exact Fintype.linearIndependent_iff.mp hv a hsum j

theorem prime_cotangent_evaluation_surjective {σ : Type*} [Fintype σ]
    (v : σ → ι → Q.ResidueField)
    (hv : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ (v j))) :
    Function.Surjective
      (fun x : PrimeLocalCotangent Q => fun j => primeNormalPairing Q (v j) x) := by
  classical
  let f := fun j => primeNormalPairing Q (v j)
  have hf : LinearIndependent Q.ResidueField f := primeNormalPairing_linearIndependent Q v hv
  intro a
  obtain ⟨g, hg⟩ := LinearMap.dualMap_surjective_of_injective
    hf.finsuppLinearCombination_injective (Finsupp.linearCombination Q.ResidueField a)
  refine ⟨(Module.evalEquiv Q.ResidueField (PrimeLocalCotangent Q)).symm g, ?_⟩
  funext j
  change f j ((Module.evalEquiv Q.ResidueField (PrimeLocalCotangent Q)).symm g) = a j
  rw [Module.apply_evalEquiv_symm_apply]
  have hj := LinearMap.congr_fun hg (Finsupp.single j (1 : Q.ResidueField))
  simpa only [LinearMap.dualMap_apply, Finsupp.linearCombination_single, one_smul] using hj

end PiExponent

end

end OAI
