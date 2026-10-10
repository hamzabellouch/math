import OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable (K α β : Type*) [Field K]
variable (Q : Ideal (MvPolynomial (α ⊕ β) K)) [Q.IsPrime]
variable (hB : IsTranscendenceBasis K (splitResidueBeta K α β Q))

theorem closedPointEvaluation_original :
    ((closedPointEvaluationRingHom K α β Q hB).comp
      (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom).comp
      (algebraMap (MvPolynomial (α ⊕ β) K)
        (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β)) =
      algebraMap (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change closedPointEvaluation K α β Q hB
      (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β
        (algebraMap (MvPolynomial (α ⊕ β) K)
          (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β)
          (MvPolynomial.C a))) = _
    have h := closedPointEvaluation_coefficient K α β Q hB (MvPolynomial.C a)
    rw [← PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv_coefficient] at h
    simpa only [RingHom.comp_apply, MvPolynomial.rename_C, MvPolynomial.aeval_C,
      IsScalarTower.algebraMap_apply K (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q),
      MvPolynomial.algebraMap_eq] using h
  · intro i
    cases i with
    | inl i =>
      let := splitCoefficientResidueAlgebra K α β Q hB
      change closedPointEvaluation K α β Q hB
        (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β
          (algebraMap (MvPolynomial (α ⊕ β) K)
            (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β)
            (MvPolynomial.X (Sum.inl i)))) = _
      rw [PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv_X_inl,
        closedPointEvaluation, MvPolynomial.aeval_X]
    | inr j =>
      let := splitCoefficientResidueAlgebra K α β Q hB
      change closedPointEvaluation K α β Q hB
        (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β
          (algebraMap (MvPolynomial (α ⊕ β) K)
            (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β)
            (MvPolynomial.X (Sum.inr j)))) = _
      rw [PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv_X_inr,
        closedPointEvaluation_coefficient, MvPolynomial.aeval_X]
      rfl

include hB in

theorem coefficientLocalization_extendedPrime_maximal :
    (Q.map (algebraMap (MvPolynomial (α ⊕ β) K)
      (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β))).IsMaximal := by
  have hker := extended_kernel_eq
    (PiExponentSiegelAux.W09.coefficientDenominators K α β)
    (algebraMap (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q))
    ((closedPointEvaluationRingHom K α β Q hB).comp
      (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom)
    (closedPointEvaluation_original K α β Q hB)
  rw [Ideal.ker_algebraMap_residueField] at hker
  rw [hker]
  change ((RingHom.ker (closedPointEvaluationRingHom K α β Q hB)).comap
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom).IsMaximal
  let := closedPointEvaluation_kernel_maximal K α β Q hB
  exact Ideal.comap_isMaximal_of_surjective _
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).surjective

theorem coefficientClosedPoint_comap :
    (RingHom.ker ((closedPointEvaluationRingHom K α β Q hB).comp
      (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom)).comap
      (algebraMap (MvPolynomial (α ⊕ β) K)
        (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β)) = Q := by
  ext f
  change closedPointEvaluation K α β Q hB
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β
      (algebraMap _ (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β) f)) = 0 ↔ f ∈ Q
  have h := RingHom.congr_fun (closedPointEvaluation_original K α β Q hB) f
  change closedPointEvaluation K α β Q hB
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β
      (algebraMap _ (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β) f)) =
        algebraMap (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q) f at h
  rw [h]
  exact Ideal.algebraMap_residueField_eq_zero

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
