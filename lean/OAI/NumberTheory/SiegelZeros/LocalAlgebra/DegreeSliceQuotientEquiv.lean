import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Hilbert.HomogeneousDeformation

namespace OAI

namespace SiegelZeros

section

section
section

open Polynomial

namespace WeightedTorusJets

end WeightedTorusJets

namespace WeightedTorusJets

open Ideal IsLocalRing Polynomial RingTheory.Sequence

end WeightedTorusJets

open Ideal RingTheory.Sequence IsLocalRing

namespace WeightedTorusJets

end WeightedTorusJets

namespace WeightedTorusJets

open Ideal RingTheory.Sequence IsLocalRing Polynomial

end WeightedTorusJets

open Ideal RingTheory.Sequence
open scoped Pointwise

namespace WeightedTorusJets

end WeightedTorusJets

open Ideal RingTheory.Sequence
open CategoryTheory Abelian

universe u

namespace WeightedTorusJets

end WeightedTorusJets

open scoped BigOperators

namespace WeightedTorusJets

end WeightedTorusJets

namespace WeightedTorusJets.Geometry

end WeightedTorusJets.Geometry

namespace WeightedTorusJets

universe uReg

theorem isRegular_generators_of_contains_regular_sequence {R : Type uReg} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R) (hI : I ≠ ⊤)
    (gs rs : List R) (hgs : Ideal.ofList gs = I) (hlen : rs.length = gs.length)
    (hmem : ∀ r ∈ rs, r ∈ I) (hreg : IsRegular R rs) : IsRegular R gs := by
  apply isRegular_of_exists_regular_sequence_in_ofList gs R _ rs hlen _ hreg
  · simpa only [hgs, Ideal.smul_eq_mul, Ideal.mul_top] using hI.lt_top
  · simpa only [hgs] using hmem

end WeightedTorusJets

namespace WeightedTorusJets
open IsLocalRing

end WeightedTorusJets
namespace WeightedTorusJets

end WeightedTorusJets

namespace WeightedTorusJets

end WeightedTorusJets

namespace WeightedTorusJets.Deformation

open Polynomial

end WeightedTorusJets.Deformation

namespace WeightedTorusJets.Deformation

end WeightedTorusJets.Deformation

namespace WeightedTorusJets.Deformation

open Polynomial

end WeightedTorusJets.Deformation

namespace WeightedTorusJets
open MvPolynomial
variable {σ R : Type*} [CommRing R]

end WeightedTorusJets

namespace WeightedTorusJets.Deformation

end WeightedTorusJets.Deformation

namespace WeightedTorusJets.Deformation

open RingTheory.Sequence
open scoped Pointwise

end WeightedTorusJets.Deformation

namespace WeightedTorusJets.Deformation

open Polynomial

end WeightedTorusJets.Deformation

namespace WeightedTorusJets.Deformation

open Polynomial

end WeightedTorusJets.Deformation

namespace WeightedTorusJets.Deformation

end WeightedTorusJets.Deformation

namespace WeightedTorusJets.Deformation

open Polynomial
open scoped Pointwise

end WeightedTorusJets.Deformation

end

section

open scoped BigOperators

namespace WeightedTorusJets

open MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S]

end WeightedTorusJets

open Module

namespace WeightedTorusJets

theorem homogeneousMonomialBasis_repr (σ R : Type*) [CommSemiring R] (n : ℕ)
    (p : MvPolynomial.homogeneousSubmodule σ R n) (m : {m : σ →₀ ℕ // m.degree = n}) :
    (homogeneousMonomialBasis σ R n).repr p m = (p : MvPolynomial σ R).coeff m := by
  rfl

theorem toMatrix_linearCombination_homogeneous
    {σ R κ : Type*} [CommSemiring R] [Fintype κ] [DecidableEq κ]
    (n : ℕ) [Fintype {m : σ →₀ ℕ // m.degree = n}]
    (p : κ → MvPolynomial.homogeneousSubmodule σ R n)
    (m : {m : σ →₀ ℕ // m.degree = n}) (j : κ) :
    LinearMap.toMatrix Finsupp.basisSingleOne (homogeneousMonomialBasis σ R n)
      (Finsupp.linearCombination R p) m j = (p j : MvPolynomial σ R).coeff m := by
  simp only [LinearMap.toMatrix_apply, Finsupp.coe_basisSingleOne,
    Finsupp.linearCombination_single, one_smul, homogeneousMonomialBasis_repr]

end WeightedTorusJets

open MvPolynomial

noncomputable section

namespace WeightedTorusJets.Geometry.GradedQuotient

variable {K σ : Type*} [Field K]

def degreeSliceQuotientEquiv (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    (homogeneousSubmodule σ K n ⧸
      (I.restrictScalars K).comap (homogeneousSubmodule σ K n).subtype) ≃ₗ[K]
      degreePiece I n :=
  (Submodule.quotEquivOfEq _ _ (ker_degreePresentation I n).symm).trans
    ((degreePresentation I n).quotKerEquivOfSurjective (degreePresentation_surjective I n))

def cokernelEquivDegreePiece {V : Type*} [AddCommGroup V] [Module K V]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) (m : V →ₗ[K] homogeneousSubmodule σ K n)
    (hrange : LinearMap.range m =
      (I.restrictScalars K).comap (homogeneousSubmodule σ K n).subtype) :
    (homogeneousSubmodule σ K n ⧸ LinearMap.range m) ≃ₗ[K] degreePiece I n :=
  (Submodule.quotEquivOfEq _ _ hrange).trans (degreeSliceQuotientEquiv I n)

end WeightedTorusJets.Geometry.GradedQuotient

namespace WeightedTorusJets.Geometry.GradedQuotient
variable {K σ : Type*} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

end WeightedTorusJets.Geometry.GradedQuotient

namespace WeightedTorusJets

open MvPolynomial

end WeightedTorusJets

namespace WeightedTorusJets

open MvPolynomial Geometry.GradedQuotient

end WeightedTorusJets

namespace WeightedTorusJets.Geometry

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

end WeightedTorusJets.Geometry

namespace WeightedTorusJets

open MvPolynomial

end WeightedTorusJets
namespace WeightedTorusJets

open MvPolynomial Geometry.GradedQuotient

end WeightedTorusJets

noncomputable section

open scoped BigOperators DirectSum
open MvPolynomial

namespace WeightedTorusJets.Geometry

attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial
open scoped DirectSum

variable {K σ : Type*} [Field K] [Finite σ]

open MvPolynomial

open MvPolynomial

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

end WeightedTorusJets.Geometry

namespace WeightedTorusJets

open MvPolynomial

end WeightedTorusJets

namespace WeightedTorusJets.Geometry

open MvPolynomial

theorem homogeneousComponent_mul_of_left_homogeneous {σ K : Type*} [CommRing K]
    {p q : MvPolynomial σ K} {m n : ℕ} (hp : p.IsHomogeneous m) :
    homogeneousComponent (m + n) (p * q) = p * homogeneousComponent n q := by
  induction q using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [homogeneousComponent_of_mem (hp.mul (isHomogeneous_monomial c rfl)),
        homogeneousComponent_of_mem (isHomogeneous_monomial c rfl)]
      simp only [Nat.add_left_cancel_iff]
      split_ifs <;> simp
  | add q r hq hr => simp only [mul_add, map_add, hq, hr]

theorem homogeneousComponent_mul_of_right_homogeneous {σ K : Type*} [CommRing K]
    {p q : MvPolynomial σ K} {m n : ℕ} (hq : q.IsHomogeneous n) :
    homogeneousComponent (m + n) (p * q) = homogeneousComponent m p * q := by
  rw [mul_comm p q, add_comm m n, homogeneousComponent_mul_of_left_homogeneous hq,
    mul_comm]

theorem homogeneousComponent_mul_eq_zero_of_lt {σ K : Type*} [CommRing K]
    {p q : MvPolynomial σ K} {m n : ℕ} (hq : q.IsHomogeneous n) (hmn : m < n) :
    homogeneousComponent m (p * q) = 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [homogeneousComponent_of_mem ((isHomogeneous_monomial c rfl).mul hq)]
      simp [show m ≠ d.degree + n by omega]
  | add p r hp hr => simp only [add_mul, map_add, hp, hr, add_zero]

end WeightedTorusJets.Geometry

open Module

end
end
end
end
end

end SiegelZeros

end OAI
