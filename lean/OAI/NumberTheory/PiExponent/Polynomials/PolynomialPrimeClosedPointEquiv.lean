import Mathlib.RingTheory.Localization.LocalizationLocalization
import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters
import OAI.NumberTheory.PiExponent.LocalAlgebra.SplitClosedPointCompatibility

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable (K α β : Type*) [Field K]
variable (Q : Ideal (MvPolynomial (α ⊕ β) K)) [Q.IsPrime]
variable (hB : IsTranscendenceBasis K (splitResidueBeta K α β Q))

def coefficientClosedPoint :
    Ideal (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β) :=
  RingHom.ker ((closedPointEvaluationRingHom K α β Q hB).comp
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom)

instance coefficientClosedPoint_isMaximal :
    (coefficientClosedPoint K α β Q hB).IsMaximal := by
  change ((RingHom.ker (closedPointEvaluationRingHom K α β Q hB)).comap
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom).IsMaximal
  let := closedPointEvaluation_kernel_maximal K α β Q hB
  exact Ideal.comap_isMaximal_of_surjective _
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).surjective

abbrev CoefficientClosedLocal := Localization.AtPrime (coefficientClosedPoint K α β Q hB)

theorem closedLocal_isLocalizationAtOriginal :
    IsLocalization.AtPrime (CoefficientClosedLocal K α β Q hB) Q := by
  have h : IsLocalization.AtPrime (CoefficientClosedLocal K α β Q hB)
      ((coefficientClosedPoint K α β Q hB).comap
        (algebraMap (MvPolynomial (α ⊕ β) K)
          (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β))) := by
    infer_instance
  have hQ : (coefficientClosedPoint K α β Q hB).comap
      (algebraMap (MvPolynomial (α ⊕ β) K)
        (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β)) = Q :=
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
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom

instance closedPolynomialIdeal_isMaximal :
    (closedPolynomialIdeal K α β Q hB).IsMaximal := by
  exact (inferInstance : (coefficientClosedPoint K α β Q hB).IsMaximal).map_bijective
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).bijective

def polynomialPrimeClosedPointEquiv :
    Localization.AtPrime Q ≃+*
      Localization.AtPrime (closedPolynomialIdeal K α β Q hB) :=
  (originalLocalCoefficientLocalEquiv K α β Q hB).trans
    (PiExponentSiegel.W23.atPrimeEquivOfRingEquiv
      (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingEquiv
      (coefficientClosedPoint K α β Q hB))

def polynomialPrimeClosedPointResidueEquiv :
    Q.ResidueField ≃+* (closedPolynomialIdeal K α β Q hB).ResidueField :=
  IsLocalRing.ResidueField.mapEquiv (polynomialPrimeClosedPointEquiv K α β Q hB)

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
