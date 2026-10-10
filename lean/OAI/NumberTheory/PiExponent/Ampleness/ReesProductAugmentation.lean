import OAI.NumberTheory.PiExponent.Ampleness.ReesProductPower

namespace OAI

namespace PiExponent.ReesProductAugmentation
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact PiExponent.GradedCech
open PiExponent.ReesLocalizedIntersections PiExponent.ReesProductChart PiExponent.ReesProductPower
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

def ordinaryFraction (s : Finset J) (n : ℕ) (b : ↥(I ^ n : Ideal R)) : Piece I a s n := by
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  exact ⟨fraction (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s)
    (ordinaryPowerEquivIntegerPiece I n b).val 0,
      0, (ordinaryPowerEquivIntegerPiece I n b).val,
      by simpa only [Nat.cast_zero, zero_mul, add_zero] using
        (ordinaryPowerEquivIntegerPiece I n b).property, rfl⟩

theorem ordinaryFraction_evaluation (s : Finset J) (n : ℕ) (b : ↥(I ^ n : Ideal R)) :
    pieceEvaluation I a s n (ordinaryFraction I a s n b) =
      algebraMap R (Localization.Away (coefficientProduct I a s)) b.val := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  change localizationEvaluation I a s
    (fraction (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s)
      (ordinaryPowerEquivIntegerPiece I n b).val 0) = _
  rw [localizationEvaluation_fraction, powerDenominator_zero, IsLocalization.mk'_one]
  congr 1
  change evaluation I (ReesPushdown.ordinaryPowerEquivPiece I n b).val = b.val
  rw [evaluation_piece I (ReesPushdown.ordinaryPowerEquivPiece I n b)]
  exact ReesPushdown.ordinaryPowerEquivPiece_apply_coeff I n b

theorem chartPowerMap_ordinaryFraction {s : Finset J} {j : J} (hj : j ∈ s)
    (n : ℕ) (b : ↥(I ^ n : Ideal R)) :
    (chartPowerMap I a hj n (ordinaryFraction I a s n b)).val =
      ReesProductChart.chartBase I a s b.val := by
  apply ReesProductChart.chartMap_injective I a s
  rw [chartPowerMap_evaluation I a hj, ordinaryFraction_evaluation,
    ReesProductChart.chartMap_base]

theorem augmentation_eq_ordinaryFraction (n : ℕ) (b : ↥(I ^ n : Ideal R)) (t : Fin 1 → J) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    augmentation (grading (J := J) (R := R)) (integerPiece I) MvPolynomial.X variable_mem n
      (ordinaryPowerEquivIntegerPiece I n b) t = ordinaryFraction I a (tupleSet t) n b := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  apply Subtype.ext
  rfl

end
end PiExponent.ReesProductAugmentation

end OAI
