import OAI.RepresentationTheory.RestrictedTilting.LatticeNumerator

namespace OAI

namespace FiberFunctorProof
universe u
variable (k : Type u) [Field k] [Infinite k]
variable (ι : Type u) [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))
variable (P : Matrix ι ι (Polynomial k))
variable (hP : ∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)))
variable (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d)
local notation "A" => MvPolynomial (Fin 2) k
local notation "N" => associatedSectionsSubmodule k ι ρ
local notation "h0" => associatedPolynomial_zero k ι ρ P hP
local notation "hadd" => associatedPolynomial_add k ι ρ P hP
local notation "Q" => planeGlobalTransition k P h0 hadd

include hd in
lemma planeGlobalTransition_inverse_denominator :
    ∀ v ∈ coordinateLattice (R := A), (MvPolynomial.X 0 * MvPolynomial.X 1 : A)^d •
      (Q).symm v ∈ coordinateLattice (R := A) := by
  intro v hv
  have h := polynomialAction_fraction_denominator P h0 hadd (1 : A)
    (MvPolynomial.X 0 * MvPolynomial.X 1) (planeFraction_product_ne_zero k) d hd v hv
  simpa only [map_one, one_mul, planeGlobalTransition, polynomialActionEquiv_symm, neg_neg] using h

noncomputable def associatedNumeratorLinear : N →ₗ[A] (ι → A) :=
  (latticeNumerator (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X_ne_zero 0)
    (planeCoordinates_relPrime k) Q d (planeGlobalTransition_denominator k P h0 hadd d hd)) ∘ₗ
    (associatedLatticeEquiv k ι ρ P hP).toLinearMap

noncomputable def associatedDenominatorLinear : (ι → A) →ₗ[A] N :=
  (associatedLatticeEquiv k ι ρ P hP).symm.toLinearMap ∘ₗ
    latticeDenominator (MvPolynomial.X 0) (MvPolynomial.X 1) Q d
      (planeGlobalTransition_inverse_denominator k ι ρ P hP d hd)

lemma associatedNumerator_denominator (v : ι → A) :
    associatedNumeratorLinear k ι ρ P hP d hd (associatedDenominatorLinear k ι ρ P hP d hd v) =
      (MvPolynomial.X 0 : A)^(d+d) • v := by
  change latticeNumerator (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X_ne_zero 0)
    (planeCoordinates_relPrime k) Q d (planeGlobalTransition_denominator k P h0 hadd d hd)
    ((associatedLatticeEquiv k ι ρ P hP)
      ((associatedLatticeEquiv k ι ρ P hP).symm (latticeDenominator (MvPolynomial.X 0) (MvPolynomial.X 1) Q d
        (planeGlobalTransition_inverse_denominator k ι ρ P hP d hd) v))) = _
  erw [LinearEquiv.apply_symm_apply]
  exact latticeNumerator_denominator (MvPolynomial.X 0) (MvPolynomial.X 1)
    (MvPolynomial.X_ne_zero 0) (planeCoordinates_relPrime k) Q d d
    (planeGlobalTransition_denominator k P h0 hadd d hd)
    (planeGlobalTransition_inverse_denominator k ι ρ P hP d hd) v

lemma associatedDenominator_numerator (f : N) :
    associatedDenominatorLinear k ι ρ P hP d hd (associatedNumeratorLinear k ι ρ P hP d hd f) =
      (MvPolynomial.X 0 : A)^(d+d) • f := by
  change (associatedLatticeEquiv k ι ρ P hP).symm
    (latticeDenominator (MvPolynomial.X 0) (MvPolynomial.X 1) Q d
        (planeGlobalTransition_inverse_denominator k ι ρ P hP d hd) (latticeNumerator (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X_ne_zero 0)
      (planeCoordinates_relPrime k) Q d (planeGlobalTransition_denominator k P h0 hadd d hd)
      (associatedLatticeEquiv k ι ρ P hP f))) = _
  erw [latticeDenominator_numerator, map_smul, LinearEquiv.symm_apply_apply]

lemma associatedNumeratorLinear_spec (f : N) (i : ι) :
    algebraMap A (planeCoordinateChart k 0) (associatedNumeratorLinear k ι ρ P hP d hd f i) =
      planeChartCoordinate k 0 0 ^ d * associatedXChart k ι ρ f i := by
  apply planeChartToFraction_injective k 0
  rw [planeChartToFraction_algebraMap, map_mul, map_pow,
    planeChartCoordinate, planeChartToFraction_algebraMap]
  have h := congrFun (latticeNumerator_coordinates (MvPolynomial.X 0) (MvPolynomial.X 1)
    (MvPolynomial.X_ne_zero 0) (planeCoordinates_relPrime k) Q d
    (planeGlobalTransition_denominator k P h0 hadd d hd)
    (associatedLatticeEquiv k ι ρ P hP f)) i
  change algebraMap A (planeFractionField k)
    (latticeNumerator (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X_ne_zero 0)
      (planeCoordinates_relPrime k) Q d (planeGlobalTransition_denominator k P h0 hadd d hd)
      (associatedLatticeEquiv k ι ρ P hP f) i) = _
  change algebraMap A (planeFractionField k) _ =
    (MvPolynomial.X 0 : A)^d • (associatedLatticeEquiv k ι ρ P hP f).val i at h
  simp only [Algebra.smul_def, map_pow] at h
  exact h
end FiberFunctorProof

end OAI
