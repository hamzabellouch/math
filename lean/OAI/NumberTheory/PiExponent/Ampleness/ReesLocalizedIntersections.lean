import OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedChart
import OAI.NumberTheory.PiExponent.Cohomology.GradedCech

namespace OAI

namespace PiExponent.ReesLocalizedIntersections
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact PiExponent.GradedCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

def coefficientProduct (s : Finset J) : R := ∏ j ∈ s, (a j).val

omit [Fintype J] [DecidableEq J] in
theorem evaluation_presentation_product (s : Finset J) :
    evaluation I (presentation I a (coverProduct MvPolynomial.X s)) = coefficientProduct I a s := by
  simp only [coverProduct, coefficientProduct, map_prod, presentation_X, evaluation_generator]

abbrev LocalizationModule (s : Finset J) :=
  letI := presentationAlgebra I a
  LocalizedModule (Submonoid.powers (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s))
    (reesAlgebra I)

def localizationEvaluation (s : Finset J) :
    LocalizationModule I a s →+ Localization.Away (coefficientProduct I a s) := by
  letI := presentationAlgebra I a
  exact LocalizedAlgebraEvaluation.evaluation (Submonoid.powers (coverProduct MvPolynomial.X s))
    (Submonoid.powers (coefficientProduct I a s)) (evaluation I) (by
      rintro ⟨_, k, rfl⟩
      refine ⟨k, ?_⟩
      change coefficientProduct I a s ^ k =
        evaluation I (presentation I a (coverProduct MvPolynomial.X s ^ k))
      rw [map_pow, map_pow, evaluation_presentation_product])

omit [Fintype J] [DecidableEq J] in
theorem localizationEvaluation_fraction (s : Finset J) (m : reesAlgebra I) (k : ℕ) :
    letI := presentationAlgebra I a
    localizationEvaluation I a s (fraction
      (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s) m k) =
      IsLocalization.mk' (Localization.Away (coefficientProduct I a s)) (evaluation I m)
        (powerDenominator (coefficientProduct I a s) k) := by
  let := presentationAlgebra I a
  unfold localizationEvaluation fraction
  rw [LocalizedAlgebraEvaluation.evaluation_mk]
  congr 1
  apply Subtype.ext
  change evaluation I (presentation I a (coverProduct MvPolynomial.X s ^ k)) =
    coefficientProduct I a s ^ k
  rw [map_pow, map_pow, evaluation_presentation_product]

omit [Fintype J] [DecidableEq J] in
theorem localizationEvaluation_smul (s : Finset J) (p : MvPolynomial J R)
    (z : LocalizationModule I a s) :
    letI := presentationAlgebra I a
    localizationEvaluation I a s (p • z) =
      algebraMap R (Localization.Away (coefficientProduct I a s))
        (evaluation I (presentation I a p)) * localizationEvaluation I a s z := by
  let := presentationAlgebra I a
  exact LocalizedAlgebraEvaluation.evaluation_smul _ _ _ _ p z

def coefficientRestriction {s t : Finset J} (hst : s ⊆ t) :
    Localization.Away (coefficientProduct I a s) →+*
      Localization.Away (coefficientProduct I a t) :=
  IsLocalization.Away.lift (coefficientProduct I a s)
    (IsLocalization.Away.isUnit_of_dvd (coefficientProduct I a t) (by
      exact Finset.prod_dvd_prod_of_subset s t _ hst))

omit [Fintype J] [DecidableEq J] in
@[simp] theorem coefficientRestriction_algebraMap {s t : Finset J} (hst : s ⊆ t) (r : R) :
    coefficientRestriction I a hst (algebraMap R (Localization.Away (coefficientProduct I a s)) r) =
      algebraMap R (Localization.Away (coefficientProduct I a t)) r :=
  IsLocalization.Away.lift_eq _ _ _

omit [Fintype J] in
theorem localizationEvaluation_restriction {s t : Finset J} (hst : s ⊆ t)
    (z : LocalizationModule I a s) :
    letI := presentationAlgebra I a
    localizationEvaluation I a t
      (restriction (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s)
        (coverProduct MvPolynomial.X t)
        (coverProduct_dvd (grading (J := J) (R := R)) MvPolynomial.X variable_mem hst) z) =
      coefficientRestriction I a hst (localizationEvaluation I a s z) := by
  let := presentationAlgebra I a
  induction z using LocalizedModule.induction_on with
  | h m den =>
    obtain ⟨k, hk⟩ := den.property
    have hd : den = powerDenominator (coverProduct MvPolynomial.X s) k := Subtype.ext hk.symm
    subst den
    change localizationEvaluation I a t (restriction _ _ _ (fraction _ m k)) =
      coefficientRestriction I a hst (localizationEvaluation I a s (fraction _ m k))
    have hu : IsUnit (algebraMap R (Localization.Away (coefficientProduct I a t))
        (coefficientProduct I a s)) :=
      IsLocalization.Away.isUnit_of_dvd (coefficientProduct I a t) (by
        exact Finset.prod_dvd_prod_of_subset s t _ hst)
    apply (hu.pow k).mul_right_injective
    calc
      _ = localizationEvaluation I a t
          (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s ^ k •
            restriction _ _ _ (fraction _ m k)) := by
        rw [localizationEvaluation_smul, map_pow, map_pow,
          evaluation_presentation_product, map_pow]
      _ = localizationEvaluation I a t (fraction (coverProduct MvPolynomial.X t) m 0) := by
        rw [← map_smul, power_smul_fraction, restriction_fraction_zero]
      _ = algebraMap R (Localization.Away (coefficientProduct I a t)) (evaluation I m) := by
        rw [localizationEvaluation_fraction, powerDenominator_zero, IsLocalization.mk'_one]
      _ = _ := by
        have hspec := congrArg (coefficientRestriction I a hst)
          (IsLocalization.mk'_spec' (Localization.Away (coefficientProduct I a s))
            (evaluation I m) (powerDenominator (coefficientProduct I a s) k))
        rw [localizationEvaluation_fraction]
        simpa only [map_mul, coefficientRestriction_algebraMap, powerDenominator_val, map_pow]
          using hspec.symm

abbrev Piece (s : Finset J) (n : ℕ) :=
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  IntersectionPiece (grading (J := J) (R := R)) (integerPiece I)
    MvPolynomial.X variable_mem s n

def pieceEvaluation (s : Finset J) (n : ℕ) :
    Piece I a s n →+ Localization.Away (coefficientProduct I a s) := by
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  exact (localizationEvaluation I a s).comp (Piece I a s n).subtype

theorem pieceEvaluation_restriction {s t : Finset J} (hst : s ⊆ t) (n : ℕ)
    (z : Piece I a s n) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    pieceEvaluation I a t n (setRestriction (grading (J := J) (R := R)) (integerPiece I)
      MvPolynomial.X variable_mem hst n z) =
      coefficientRestriction I a hst (pieceEvaluation I a s n z) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  exact localizationEvaluation_restriction I a hst z.val

theorem pieceEvaluation_injective (s : Finset J) (n : ℕ) :
    Function.Injective (pieceEvaluation I a s n) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨k, m, hm, hrep⟩ := z.property
  have hm' : m ∈ piece I (n + k * s.card) := by
    change m ∈ integerPiece I (↑(n + k * s.card))
    simpa only [Nat.cast_add, Nat.cast_mul] using hm
  have hp : presentation I a (coverProduct MvPolynomial.X s) ∈ piece I s.card :=
    presentation_integer_mem I a
      (coverProduct_mem (grading (J := J) (R := R)) MvPolynomial.X variable_mem s)
  have heval : evaluation I m = (m : Polynomial R).coeff (n + k * s.card) :=
    evaluation_piece I ⟨m, hm'⟩
  have hep : evaluation I (presentation I a (coverProduct MvPolynomial.X s)) =
      (presentation I a (coverProduct MvPolynomial.X s) : Polynomial R).coeff s.card :=
    evaluation_piece I ⟨_, hp⟩
  change localizationEvaluation I a s z.val = 0 at hz
  rw [hrep, localizationEvaluation_fraction] at hz
  obtain ⟨⟨b, hb⟩, hbm⟩ := (IsLocalization.mk'_eq_zero_iff
    (M := Submonoid.powers (coefficientProduct I a s))
    (S := Localization.Away (coefficientProduct I a s)) _ _).mp hz
  obtain ⟨l, rfl⟩ := hb
  apply Subtype.ext
  change z.val = 0
  rw [hrep, fraction_eq_zero]
  refine ⟨l, ?_⟩
  change presentation I a (coverProduct MvPolynomial.X s ^ l) * m = 0
  rw [map_pow]
  apply Subtype.ext
  change (presentation I a (coverProduct MvPolynomial.X s) : Polynomial R) ^ l *
    (m : Polynomial R) = 0
  rw [(mem_piece I s.card _).mp hp, (mem_piece I (n + k * s.card) m).mp hm',
    Polynomial.monomial_pow, Polynomial.monomial_mul_monomial]
  rw [← hep, evaluation_presentation_product]
  rw [heval] at hbm
  simp only [hbm, map_zero]

end
end PiExponent.ReesLocalizedIntersections

end OAI
