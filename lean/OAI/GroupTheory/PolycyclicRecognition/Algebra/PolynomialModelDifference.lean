import OAI.GroupTheory.PolycyclicRecognition.Algebra.BasisPolynomialMaps
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialBilinearWords
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialExponentialCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentDifferenceDerivative

namespace OAI

/-! # Polynomial group differences in exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition
open Module
variable {L V : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {d e : ℕ} {b : Basis (Fin d) ℝ V} {c : Basis (Fin e) ℝ L}

omit [FiniteDimensional ℝ L] P in
theorem IsPolynomialInBasis.neg {f : V → L} (hf : IsPolynomialInBasis b c f) :
    IsPolynomialInBasis b c (fun x => -f x) := by
  have h := IsCoordinatePolynomial.neg hf
  simpa only [IsPolynomialInBasis, map_neg] using h

theorem IsPolynomialInBasis.mul {f g : V → L}
    (hf : IsPolynomialInBasis b c f) (hg : IsPolynomialInBasis b c g) :
    IsPolynomialInBasis b c (fun x => f x * g x) := by
  have hp := IsCoordinatePolynomial.pair hf hg
  have h := (coordinatePolynomial_dynkinProduct P.coefficients (basisBracket c)).comp hp
  change IsCoordinatePolynomial (fun x => c.equivFun (f (b.equivFun.symm x) *
    g (b.equivFun.symm x)))
  simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    basis_dynkinProduct, ← P.mul_eq] using h

theorem polynomial_model_difference (A : L →ₗ[ℝ] L) (b : Basis (Fin d) ℝ L) :
    IsPolynomialInBasis b b (fun x => A x * (-x)) :=
  (IsPolynomialInBasis.linear A).mul
    ((IsPolynomialInBasis.linear (LinearMap.id : L →ₗ[ℝ] L)).neg)

theorem nilpotent_linear_of_group_difference (A : L →ₗ[ℝ] L) (n : ℕ)
    (hn : ∀ x, (fun y => A y * (-y))^[n] x = 0) : IsNilpotent (A - 1) := by
  have hA := A.toContinuousLinearMap.hasFDerivAt (x := 0)
  have h := nilpotent_difference_fderiv P.one_eq_zero A
    hA.differentiableAt (map_zero A) n hn
  change IsNilpotent (fderiv ℝ A.toContinuousLinearMap 0 - ContinuousLinearMap.id ℝ L) at h
  rw [hA.fderiv] at h
  exact h.map ContinuousLinearMap.toLinearMapRingHom

end PolycyclicRecognition

end

end OAI
