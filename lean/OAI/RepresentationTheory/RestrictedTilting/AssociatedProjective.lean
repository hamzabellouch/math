import OAI.RepresentationTheory.RestrictedTilting.AssociatedNumerator
import OAI.RepresentationTheory.RestrictedTilting.LatticeLocalProjectivity

namespace OAI

namespace FiberFunctorProof
open scoped TensorProduct
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

include hP hd in
 

theorem associatedSections_projective : Module.Projective A N := by
  let : Module.Finite A N := associatedSections_finite k ι ρ P hP d hd
  let : Module.FinitePresentation A N := Module.finitePresentation_of_finite A N
  apply Module.projective_of_localization_maximal
  intro I hI
  let S := Localization.AtPrime I
  have localProj : Module.Projective S (S ⊗[A] N) := by
    by_cases hI0 : I = planeOriginIdeal k
    · subst I
      let := associatedStalk_free k ι ρ P hP d hd
      change Module.Projective (planeOriginRing k) ((planeOriginRing k) ⊗[A] N)
      exact Module.Projective.of_free
    · have hc : (MvPolynomial.X 0 : A) ∉ I ∨ (MvPolynomial.X 1 : A) ∉ I := by
        by_contra hn
        push Not at hn
        apply hI0
        symm
        apply (planeOriginIdeal_isMaximal k).eq_of_le hI.ne_top
        rw [planeOriginIdeal_eq_span]
        exact Ideal.span_le.mpr (by simpa [Set.insert_subset_iff, Set.singleton_subset_iff] using hn)
      rcases hc with hx | hy
      · have hu : IsUnit (algebraMap A S (MvPolynomial.X 0)) :=
          (IsLocalization.AtPrime.isUnit_to_map_iff S I _).mpr hx
        let : Module.Projective S (S ⊗[A] planeGlobalLattice k P h0 hadd) :=
          gluedLattice_projective_baseChange (S := S)
          (MvPolynomial.X 0 : A) (MvPolynomial.X 1) (MvPolynomial.X_ne_zero 0)
          (planeCoordinates_relPrime k) Q d d
          (planeGlobalTransition_denominator k P h0 hadd d hd)
          (planeGlobalTransition_inverse_denominator k ι ρ P hP d hd) hu
        exact Module.Projective.of_equiv (LinearEquiv.baseChange A S _ _ (associatedLatticeEquiv k ι ρ P hP).symm)
      · have hu : IsUnit (algebraMap A S (MvPolynomial.X 1)) :=
          (IsLocalization.AtPrime.isUnit_to_map_iff S I _).mpr hy
        have ha : ∀ v ∈ (coordinateLattice (R := A)),
            (MvPolynomial.X 1 * MvPolynomial.X 0 : A)^d • (Q).symm v ∈ coordinateLattice (R := A) := by
          rw [show (MvPolynomial.X 1 * MvPolynomial.X 0 : A) =
            MvPolynomial.X 0 * MvPolynomial.X 1 from mul_comm _ _]
          exact planeGlobalTransition_inverse_denominator k ι ρ P hP d hd
        have hb : ∀ v ∈ (coordinateLattice (R := A)),
            (MvPolynomial.X 1 * MvPolynomial.X 0 : A)^d • (Q).symm.symm v ∈ coordinateLattice (R := A) := by
          rw [show (MvPolynomial.X 1 * MvPolynomial.X 0 : A) =
            MvPolynomial.X 0 * MvPolynomial.X 1 from mul_comm _ _]
          exact planeGlobalTransition_denominator k P h0 hadd d hd
        let := gluedLattice_projective_baseChange (S := S)
          (MvPolynomial.X 1 : A) (MvPolynomial.X 0) (MvPolynomial.X_ne_zero 1)
          (planeCoordinates_relPrime k).symm (Q).symm d d ha hb hu
        exact Module.Projective.of_equiv
          (LinearEquiv.baseChange A S _ _
          (((associatedLatticeEquiv k ι ρ P hP).trans
            (latticeSwap (MvPolynomial.X 0) (MvPolynomial.X 1) Q)).symm))
  let := localProj
  exact Module.Projective.of_equiv
    (IsLocalizedModule.isBaseChange I.primeCompl S (LocalizedModule.mkLinearMap I.primeCompl N)).equiv
end FiberFunctorProof

end OAI
