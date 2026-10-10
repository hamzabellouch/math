import OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation
import OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent
import OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading

namespace OAI

namespace PiExponent.ReesGradedModule
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesPolynomialPresentation PiExponent.GradedPolynomialLaurent
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J] (I : Ideal R) (a : J → I)

abbrev integerPiece : ℤ → AddSubgroup (reesAlgebra I) :=
  NatToIntGrading.piece (piece I)

instance integerGradedRing : GradedRing (integerPiece I) where
  toGradedMonoid := NatToIntGrading.gradedMonoid (piece I)
  toDecomposition := NatToIntGrading.decomposition (piece I)

def ordinaryPowerEquivIntegerPiece (n : ℕ) : ↥(I ^ n : Ideal R) ≃+ integerPiece I (n : ℤ) :=
  (ReesPushdown.ordinaryPowerEquivPiece I n).toAddEquiv

theorem polynomial_negative_eq_zero (n : ℕ) (p : MvPolynomial J R)
    (hp : p ∈ grading (J := J) (R := R) (.negSucc n)) : p = 0 := by
  apply MvPolynomial.IsWeightedHomogeneous.eq_zero_of_no_monomials hp
  intro b hb
  have hnonneg : 0 ≤ Finsupp.weight (1 : J → ℤ) b := by
    rw [Finsupp.weight_eq_sum]
    exact Finset.sum_nonneg fun j _ => by simp
  omega

theorem presentation_integer_mem {d : ℤ} {p : MvPolynomial J R}
    (hp : p ∈ grading (J := J) (R := R) d) :
    presentation I a p ∈ integerPiece I d := by
  cases d with
  | ofNat n =>
      change presentation I a p ∈ piece I n
      apply presentation_homogeneous_mem I a
      change p ∈ MvPolynomial.weightedHomogeneousSubmodule R (1 : J → ℤ) (n : ℤ) at hp
      rw [GradedH0.integer_grading_eq_homogeneous (R := R) (ι := J) n] at hp
      exact hp
  | negSucc n =>
      rw [polynomial_negative_eq_zero n p hp, map_zero]
      exact zero_mem _

def gradedPresentation : grading (J := J) (R := R) →+*ᵍ integerPiece I where
  __ := (presentation I a).toRingHom
  map_mem := presentation_integer_mem I a

theorem presentation_degree_compatible (d : ℤ) (p : MvPolynomial J R) :
    presentation I a (DirectSum.decompose (grading (J := J) (R := R)) p d : MvPolynomial J R) =
      (DirectSum.decompose (integerPiece I) (presentation I a p) d : reesAlgebra I) :=
  (gradedPresentation I a).map_directSumDecompose

theorem gradedScalarAction :
    letI := presentationAlgebra I a
    SetLike.GradedSMul (grading (J := J) (R := R)) (integerPiece I) := by
  let := presentationAlgebra I a
  constructor
  intro i j p z hp hz
  change presentation I a p * z ∈ integerPiece I (i + j)
  exact SetLike.mul_mem_graded (presentation_integer_mem I a hp) hz

theorem finite_graded_module
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    letI := presentationAlgebra I a
    Module.Finite (MvPolynomial J R) (reesAlgebra I) ∧
      SetLike.GradedSMul (grading (J := J) (R := R)) (integerPiece I) := by
  exact ⟨finite_presented_module I a ha, gradedScalarAction I a⟩

end
end PiExponent.ReesGradedModule

end OAI
