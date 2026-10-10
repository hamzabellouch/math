import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.LocalizationLocalization
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.TriangularLocalParametersTransport
import OAI.NumberTheory.SiegelZeros.Structure.SplitClosedPointCompatibility

namespace OAI

namespace SiegelZeros

section

noncomputable section
namespace WeightedTorusJets.PolynomialLocalResidueResolution

variable (K α β : Type*) [Field K]
variable (Q : Ideal (MvPolynomial (α ⊕ β) K)) [Q.IsPrime]
variable (hB : IsTranscendenceBasis K (splitResidueBeta K α β Q))

def coefficientClosedPoint :
    Ideal (SiegelZerosAwei.W09.PolynomialCoefficientLocalization K α β) :=
  RingHom.ker ((closedPointEvaluationRingHom K α β Q hB).comp
    (SiegelZerosAwei.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom)

instance coefficientClosedPoint_isMaximal :
    (coefficientClosedPoint K α β Q hB).IsMaximal := by
  change ((RingHom.ker (closedPointEvaluationRingHom K α β Q hB)).comap
    (SiegelZerosAwei.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom).IsMaximal
  let := closedPointEvaluation_kernel_maximal K α β Q hB
  exact Ideal.comap_isMaximal_of_surjective _
    (SiegelZerosAwei.W09.polynomialCoefficientLocalizationEquiv K α β).surjective

abbrev CoefficientClosedLocal := Localization.AtPrime (coefficientClosedPoint K α β Q hB)

theorem closedLocal_isLocalizationAtOriginal :
    IsLocalization.AtPrime (CoefficientClosedLocal K α β Q hB) Q := by
  have h : IsLocalization.AtPrime (CoefficientClosedLocal K α β Q hB)
      ((coefficientClosedPoint K α β Q hB).comap
        (algebraMap (MvPolynomial (α ⊕ β) K)
          (SiegelZerosAwei.W09.PolynomialCoefficientLocalization K α β))) := by
    infer_instance
  have hQ : (coefficientClosedPoint K α β Q hB).comap
      (algebraMap (MvPolynomial (α ⊕ β) K)
        (SiegelZerosAwei.W09.PolynomialCoefficientLocalization K α β)) = Q :=
    coefficientClosedPoint_comap K α β Q hB
  have transport (J : Ideal (MvPolynomial (α ⊕ β) K)) [J.IsPrime]
      (he : J = Q) :
      IsLocalization.AtPrime (CoefficientClosedLocal K α β Q hB) J →
        IsLocalization.AtPrime (CoefficientClosedLocal K α β Q hB) Q := by
    subst J
    exact id
  exact transport _ hQ h

def originalLocalCoefficientLocalEquiv :
    Localization.AtPrime Q ≃+* CoefficientClosedLocal K α β Q hB := by
  letI := closedLocal_isLocalizationAtOriginal K α β Q hB
  exact (IsLocalization.algEquiv Q.primeCompl
    (Localization.AtPrime Q) (CoefficientClosedLocal K α β Q hB)).toRingEquiv

def closedPolynomialIdeal : Ideal (MvPolynomial α (SplitCoefficientField K β)) :=
  (coefficientClosedPoint K α β Q hB).map
    (SiegelZerosAwei.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom

instance closedPolynomialIdeal_isMaximal :
    (closedPolynomialIdeal K α β Q hB).IsMaximal := by
  exact (inferInstance : (coefficientClosedPoint K α β Q hB).IsMaximal).map_bijective
    (SiegelZerosAwei.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom
    (SiegelZerosAwei.W09.polynomialCoefficientLocalizationEquiv K α β).bijective

def polynomialPrimeClosedPointEquiv :
    Localization.AtPrime Q ≃+*
      Localization.AtPrime (closedPolynomialIdeal K α β Q hB) :=
  (originalLocalCoefficientLocalEquiv K α β Q hB).trans
    (SiegelZeros.W23.atPrimeEquivOfRingEquiv
      (SiegelZerosAwei.W09.polynomialCoefficientLocalizationEquiv K α β).toRingEquiv
      (coefficientClosedPoint K α β Q hB))

def polynomialPrimeClosedPointResidueEquiv :
    Q.ResidueField ≃+* (closedPolynomialIdeal K α β Q hB).ResidueField :=
  IsLocalRing.ResidueField.mapEquiv (polynomialPrimeClosedPointEquiv K α β Q hB)

end WeightedTorusJets.PolynomialLocalResidueResolution

end

end

end SiegelZeros

section

noncomputable section
namespace SiegelZeros.W23
open SiegelZerosAwei.W09
open WeightedTorusJets.PolynomialLocalResidueResolution

variable (K α β : Type*) [Field K]

def affineCoefficientAlgHom :
    SplitPolynomial K α β →ₐ[K] FractionCoefficientPolynomial K α β :=
  (polynomialCoefficientLocalizationEquiv K α β).toAlgHom.comp
    (IsScalarTower.toAlgHom K (SplitPolynomial K α β)
      (PolynomialCoefficientLocalization K α β))

abbrev affineCoefficientMap :
    SplitPolynomial K α β →+* FractionCoefficientPolynomial K α β :=
  (affineCoefficientAlgHom K α β).toRingHom

@[reducible] def affineCoefficientAlgebra :
    Algebra (SplitPolynomial K α β) (FractionCoefficientPolynomial K α β) :=
  (affineCoefficientMap K α β).toAlgebra

attribute [local instance] affineCoefficientAlgebra

instance affineCoefficient_isLocalization :
    IsLocalization (coefficientDenominators K α β) (FractionCoefficientPolynomial K α β) := by
  exact (IsLocalization.isLocalization_iff_of_ringEquiv
    (coefficientDenominators K α β)
    (polynomialCoefficientLocalizationEquiv K α β).toRingEquiv).mp inferInstance

def affineMappedIdeal (P : Ideal (SplitPolynomial K α β)) :
    Ideal (FractionCoefficientPolynomial K α β) :=
  P.map (affineCoefficientMap K α β)

variable (Q : Ideal (SplitPolynomial K α β)) [Q.IsPrime]
variable (hB : IsTranscendenceBasis K (splitResidueBeta K α β Q))

theorem affineCoefficientMap_comap_closedPoint :
    (closedPolynomialIdeal K α β Q hB).comap (affineCoefficientMap K α β) = Q := by
  change ((coefficientClosedPoint K α β Q hB).map
      (polynomialCoefficientLocalizationEquiv K α β).toRingHom).comap
      ((polynomialCoefficientLocalizationEquiv K α β).toRingHom.comp
        (algebraMap (SplitPolynomial K α β) (PolynomialCoefficientLocalization K α β))) = Q
  rw [← Ideal.comap_comap, ← atPrimeImage_comap]
  exact coefficientClosedPoint_comap K α β Q hB

include hB in

theorem affineDenominators_disjoint (P : Ideal (SplitPolynomial K α β)) (hPQ : P ≤ Q) :
    Disjoint (coefficientDenominators K α β : Set (SplitPolynomial K α β)) (P : Set _) := by
  have hd : Disjoint (coefficientDenominators K α β : Set (SplitPolynomial K α β))
      (Q : Set _) := by
    rw [← affineCoefficientMap_comap_closedPoint K α β Q hB]
    exact (IsLocalization.disjoint_under_iff (coefficientDenominators K α β)
      (FractionCoefficientPolynomial K α β) (closedPolynomialIdeal K α β Q hB)).mpr
      (Ideal.IsMaximal.ne_top inferInstance)
  exact Set.disjoint_left.mpr fun x hx hxP => Set.disjoint_left.mp hd hx (hPQ hxP)

include hB in

theorem affineMappedIdeal_isPrime (P : Ideal (SplitPolynomial K α β)) [P.IsPrime]
    (hPQ : P ≤ Q) : (affineMappedIdeal K α β P).IsPrime := by
  exact IsLocalization.isPrime_of_isPrime_disjoint (coefficientDenominators K α β)
    (FractionCoefficientPolynomial K α β) P inferInstance
    (affineDenominators_disjoint K α β Q hB P hPQ)

theorem affineMappedIdeal_le_closedPoint (P : Ideal (SplitPolynomial K α β)) (hPQ : P ≤ Q) :
    affineMappedIdeal K α β P ≤ closedPolynomialIdeal K α β Q hB := by
  apply Ideal.map_le_iff_le_comap.mpr
  rw [affineCoefficientMap_comap_closedPoint]
  exact hPQ

include hB in

theorem affineMappedIdeal_comap (P : Ideal (SplitPolynomial K α β)) [P.IsPrime]
    (hPQ : P ≤ Q) :
    (affineMappedIdeal K α β P).comap (affineCoefficientMap K α β) = P :=
  IsLocalization.under_map_of_isPrime_disjoint (coefficientDenominators K α β)
    (FractionCoefficientPolynomial K α β) inferInstance
    (affineDenominators_disjoint K α β Q hB P hPQ)

theorem originalLocalCoefficientLocalEquiv_algebraMap (a : SplitPolynomial K α β) :
    originalLocalCoefficientLocalEquiv K α β Q hB
      (algebraMap (SplitPolynomial K α β) (Localization.AtPrime Q) a) =
      algebraMap (SplitPolynomial K α β) (CoefficientClosedLocal K α β Q hB) a := by
  let := closedLocal_isLocalizationAtOriginal K α β Q hB
  exact (IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q)
    (CoefficientClosedLocal K α β Q hB)).commutes a

theorem closedPointLocalEquiv_algebraMap (a : SplitPolynomial K α β) :
    polynomialPrimeClosedPointEquiv K α β Q hB
      (algebraMap (SplitPolynomial K α β) (Localization.AtPrime Q) a) =
      algebraMap (FractionCoefficientPolynomial K α β)
        (Localization.AtPrime (closedPolynomialIdeal K α β Q hB))
        (affineCoefficientMap K α β a) := by
  have : ((coefficientClosedPoint K α β Q hB).map
      (polynomialCoefficientLocalizationEquiv K α β).toRingHom).IsPrime :=
    Ideal.map_isPrime_of_equiv (polynomialCoefficientLocalizationEquiv K α β).toRingEquiv
  change atPrimeEquivOfRingEquiv
      (polynomialCoefficientLocalizationEquiv K α β).toRingEquiv
      (coefficientClosedPoint K α β Q hB)
      (originalLocalCoefficientLocalEquiv K α β Q hB
        (algebraMap (SplitPolynomial K α β) (Localization.AtPrime Q) a)) =
    algebraMap (FractionCoefficientPolynomial K α β)
      (Localization.AtPrime ((coefficientClosedPoint K α β Q hB).map
        (polynomialCoefficientLocalizationEquiv K α β).toRingHom))
      (affineCoefficientMap K α β a)
  rw [originalLocalCoefficientLocalEquiv_algebraMap,
    IsScalarTower.algebraMap_apply (SplitPolynomial K α β)
      (PolynomialCoefficientLocalization K α β) (CoefficientClosedLocal K α β Q hB)]
  exact atPrimeEquivOfRingEquiv_algebraMap
    (polynomialCoefficientLocalizationEquiv K α β).toRingEquiv
    (coefficientClosedPoint K α β Q hB)
    (algebraMap (SplitPolynomial K α β) (PolynomialCoefficientLocalization K α β) a)

theorem closedPointLocalEquiv_map_ideal (P : Ideal (SplitPolynomial K α β)) :
    (parameterLocalizedIdeal P Q).map
      (polynomialPrimeClosedPointEquiv K α β Q hB).toRingHom =
    parameterLocalizedIdeal (affineMappedIdeal K α β P)
      (closedPolynomialIdeal K α β Q hB) := by
  unfold parameterLocalizedIdeal affineMappedIdeal
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro a
  exact closedPointLocalEquiv_algebraMap K α β Q hB a

def affineLocalQuotientEquiv (P : Ideal (SplitPolynomial K α β)) :
    (Localization.AtPrime Q ⧸ parameterLocalizedIdeal P Q) ≃+*
      (Localization.AtPrime (closedPolynomialIdeal K α β Q hB) ⧸
        parameterLocalizedIdeal (affineMappedIdeal K α β P)
          (closedPolynomialIdeal K α β Q hB)) :=
  Ideal.quotientEquiv _ _ (polynomialPrimeClosedPointEquiv K α β Q hB)
    (closedPointLocalEquiv_map_ideal K α β Q hB P).symm

def affineClosedQuotientLocalEquiv (P : Ideal (SplitPolynomial K α β)) (hPQ : P ≤ Q) :
    Localization.AtPrime (quotientParameterPrime P Q hPQ) ≃+*
      Localization.AtPrime
        (R := FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P)
        (quotientParameterPrime (affineMappedIdeal K α β P)
        (closedPolynomialIdeal K α β Q hB)
        (affineMappedIdeal_le_closedPoint K α β Q hB P hPQ)) :=
  ((localizationQuotientParametersEquiv P Q hPQ).symm.trans
    (affineLocalQuotientEquiv K α β Q hB P)).trans
    (localizationQuotientParametersEquiv (affineMappedIdeal K α β P)
      (closedPolynomialIdeal K α β Q hB)
      (affineMappedIdeal_le_closedPoint K α β Q hB P hPQ))

def affineQuotientMap (P : Ideal (SplitPolynomial K α β)) :
    (SplitPolynomial K α β ⧸ P) →+*
      (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P) :=
  Ideal.quotientMap _ (affineCoefficientMap K α β) Ideal.le_comap_map

@[reducible] def affineQuotientAlgebra (P : Ideal (SplitPolynomial K α β)) :
    Algebra (SplitPolynomial K α β ⧸ P)
      (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P) :=
  RingHom.toAlgebra'
    (R := SplitPolynomial K α β ⧸ P)
    (S := FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P)
    (affineQuotientMap K α β P) (fun x y =>
      (Ideal.Quotient.commSemiring (affineMappedIdeal K α β P)).mul_comm
        (affineQuotientMap K α β P x) y)

attribute [local instance] affineQuotientAlgebra

@[simp] theorem affineQuotientMap_mk (P : Ideal (SplitPolynomial K α β))
    (a : SplitPolynomial K α β) :
    affineQuotientMap K α β P (Ideal.Quotient.mk P a) =
      Ideal.Quotient.mk _ (affineCoefficientMap K α β a) := rfl

instance affineQuotient_scalarTower (P : Ideal (SplitPolynomial K α β)) :
    IsScalarTower K (SplitPolynomial K α β ⧸ P)
      (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P) := by
  apply IsScalarTower.of_algebraMap_eq
    (R := K) (S := SplitPolynomial K α β ⧸ P)
    (A := FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P)
  intro k
  change Ideal.Quotient.mk _ (algebraMap K (FractionCoefficientPolynomial K α β) k) =
    affineQuotientMap K α β P (Ideal.Quotient.mk P (algebraMap K (SplitPolynomial K α β) k))
  rw [affineQuotientMap_mk]
  exact congrArg (Ideal.Quotient.mk (affineMappedIdeal K α β P))
    ((affineCoefficientAlgHom K α β).commutes k).symm

include hB in

theorem affineQuotientMap_injective (P : Ideal (SplitPolynomial K α β)) [P.IsPrime]
    (hPQ : P ≤ Q) : Function.Injective (affineQuotientMap K α β P) :=
  Ideal.quotientMap_injective' (affineMappedIdeal_comap K α β Q hB P hPQ).le

include hB in

theorem affineQuotient_faithfulSMul (P : Ideal (SplitPolynomial K α β)) [P.IsPrime]
    (hPQ : P ≤ Q) :
    FaithfulSMul (SplitPolynomial K α β ⧸ P)
      (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (affineQuotientMap_injective K α β Q hB P hPQ)

include hB in

theorem affineQuotient_isDomain (P : Ideal (SplitPolynomial K α β)) [P.IsPrime]
    (hPQ : P ≤ Q) :
    IsDomain (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P) := by
  let := affineMappedIdeal_isPrime K α β Q hB P hPQ
  infer_instance

theorem affineQuotient_finiteType [Finite α] (P : Ideal (SplitPolynomial K α β)) :
    Algebra.FiniteType (SplitCoefficientField K β)
      (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P) :=
  Algebra.FiniteType.of_surjective
    (Ideal.Quotient.mkₐ (SplitCoefficientField K β) (affineMappedIdeal K α β P))
    Ideal.Quotient.mk_surjective

include hB in

theorem affineQuotient_isLocalization (P : Ideal (SplitPolynomial K α β)) [P.IsPrime]
    (hPQ : P ≤ Q) :
    IsLocalization ((coefficientDenominators K α β).map (Ideal.Quotient.mk P))
      (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P) := by
  apply (isLocalization_iff
    ((coefficientDenominators K α β).map (Ideal.Quotient.mk P))
    (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P)).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro s
    obtain ⟨a, ha, he⟩ := s.property
    change IsUnit (affineQuotientMap K α β P (s : SplitPolynomial K α β ⧸ P))
    rw [← he, affineQuotientMap_mk]
    exact (IsLocalization.map_units (FractionCoefficientPolynomial K α β)
      (⟨a, ha⟩ : coefficientDenominators K α β)).map
        (Ideal.Quotient.mk (affineMappedIdeal K α β P))
  · intro z
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (coefficientDenominators K α β) t
    refine ⟨⟨Ideal.Quotient.mk P a,
      ⟨Ideal.Quotient.mk P (s : SplitPolynomial K α β),
        Submonoid.mem_map_of_mem (Ideal.Quotient.mk P) s.property⟩⟩, ?_⟩
    change Ideal.Quotient.mk _ t *
      affineQuotientMap K α β P (Ideal.Quotient.mk P (s : SplitPolynomial K α β)) =
      affineQuotientMap K α β P (Ideal.Quotient.mk P a)
    rw [affineQuotientMap_mk, affineQuotientMap_mk, ← map_mul]
    exact congrArg (Ideal.Quotient.mk (affineMappedIdeal K α β P)) hs
  · intro x y hxy
    refine ⟨1, ?_⟩
    simpa only [Submonoid.coe_one, one_mul] using
      (affineQuotientMap_injective K α β Q hB P hPQ hxy)

theorem affineClosedQuotientLocalEquiv_mk_algebraMap
    (P : Ideal (SplitPolynomial K α β)) (hPQ : P ≤ Q) (a : SplitPolynomial K α β) :
    affineClosedQuotientLocalEquiv K α β Q hB P hPQ
      (algebraMap (SplitPolynomial K α β ⧸ P)
        (Localization.AtPrime (quotientParameterPrime P Q hPQ)) (Ideal.Quotient.mk P a)) =
      @algebraMap (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P)
        (Localization.AtPrime
        (R := FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P)
        (quotientParameterPrime (affineMappedIdeal K α β P)
          (closedPolynomialIdeal K α β Q hB)
          (affineMappedIdeal_le_closedPoint K α β Q hB P hPQ)))
        (Ideal.Quotient.commRing (affineMappedIdeal K α β P)).toCommSemiring _ _
        (affineQuotientMap K α β P (Ideal.Quotient.mk P a)) := by
  have hleft : (localizationQuotientParametersEquiv P Q hPQ).symm
      (algebraMap (SplitPolynomial K α β ⧸ P)
        (Localization.AtPrime (quotientParameterPrime P Q hPQ)) (Ideal.Quotient.mk P a)) =
      Ideal.Quotient.mk (parameterLocalizedIdeal P Q)
        (algebraMap (SplitPolynomial K α β) (Localization.AtPrime Q) a) := by
    apply (localizationQuotientParametersEquiv P Q hPQ).injective
    rw [RingEquiv.apply_symm_apply]
    exact (localizationQuotientParametersEquiv_mk_algebraMap P Q hPQ a).symm
  simp only [affineClosedQuotientLocalEquiv, RingEquiv.trans_apply]
  rw [hleft]
  change localizationQuotientParametersEquiv (affineMappedIdeal K α β P)
      (closedPolynomialIdeal K α β Q hB)
      (affineMappedIdeal_le_closedPoint K α β Q hB P hPQ)
      (Ideal.Quotient.mk _ (polynomialPrimeClosedPointEquiv K α β Q hB
        (algebraMap (SplitPolynomial K α β) (Localization.AtPrime Q) a))) = _
  rw [closedPointLocalEquiv_algebraMap,
    localizationQuotientParametersEquiv_mk_algebraMap, affineQuotientMap_mk]

end SiegelZeros.W23

end

end

end OAI
