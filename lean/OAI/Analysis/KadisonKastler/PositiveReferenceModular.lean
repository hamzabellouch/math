import OAI.Analysis.KadisonKastler.PositiveReferenceCone
import OAI.Analysis.KadisonKastler.PositiveConjugationUniqueness

namespace OAI

/-! # The polar conjugation is unchanged at positive cyclic references

The old quadratic cone supplies positivity at the new reference. The
proved uniqueness theorem then identifies its constructed conjugation.
-/

namespace KadisonKastler

noncomputable section

open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance positiveReferenceModularRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

omit [TopologicalSpace.SeparableSpace H] in
theorem positiveCone_quadratic_complex_nonneg
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ=ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ) (a : Algebra M) :
    0 ≤ inner ℂ η (modularQuadratic J a η) := by
  have hηJ := modularPositiveCone_fixed J hright ξ hξ hη
  have hQa := modularPositiveCone_fixed J hright ξ hξ
    (modularQuadratic_preserves_positiveCone J hJ hright ξ a hη)
  have hc := conjugateIsometry_inner J η (modularQuadratic J a η)
  rw [hηJ,hQa] at hc
  have him := congrArg Complex.im hc
  simp only [Complex.star_def,Complex.conj_im] at him
  constructor
  · exact positiveCone_quadratic_nonneg J hJ hright ξ hpos hη a
  · change (0 : ℝ)=(inner ℂ η (modularQuadratic J a η)).im
    linarith

theorem positiveCone_polar_conjugation
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hsep : Function.Injective (algebraVectorMap M η))
    (hcyc : DenseRange (algebraVectorMap M η)) :
    tomitaPolarConjugation J η hsep hcyc=J :=
  tomitaPolarConjugation_eq_of_quadratic_positive J hJ hright hleft η
    (modularPositiveCone_fixed J hright ξ hξ hη) hsep hcyc
    (positiveCone_quadratic_complex_nonneg J hJ hright ξ hξ hpos hη)

end

end KadisonKastler

end OAI
