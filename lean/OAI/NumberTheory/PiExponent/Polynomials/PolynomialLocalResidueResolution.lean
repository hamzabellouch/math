import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Smooth.Basic

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

section LocalCoefficientField
variable {K R ι : Type*} [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]

def residueAlgHom : R →ₐ[K] IsLocalRing.ResidueField R :=
  { IsLocalRing.residue R with commutes' := fun _ => rfl }

theorem isUnit_aeval_of_residue_independent (x : ι → R)
    (hx : AlgebraicIndependent K (fun i => IsLocalRing.residue R (x i)))
    (f : MvPolynomial ι K) (hf : f ≠ 0) : IsUnit (MvPolynomial.aeval x f) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit (MvPolynomial.aeval x f)).mp
  intro hz
  apply hf
  apply hx.eq_zero_of_aeval_eq_zero
  have he := MvPolynomial.comp_aeval_apply (f := x) (residueAlgHom (K := K) (R := R)) f
  exact he.symm.trans hz

def rationalCoefficientMap (x : ι → R)
    (hx : AlgebraicIndependent K (fun i => IsLocalRing.residue R (x i))) :
    FractionRing (MvPolynomial ι K) →+* R :=
  IsLocalization.lift (M := nonZeroDivisors (MvPolynomial ι K))
    (S := FractionRing (MvPolynomial ι K)) (g := (MvPolynomial.aeval x).toRingHom)
    (fun f => isUnit_aeval_of_residue_independent x hx f (nonZeroDivisors.coe_ne_zero f))

@[simp] theorem rationalCoefficientMap_polynomial (x : ι → R)
    (hx : AlgebraicIndependent K (fun i => IsLocalRing.residue R (x i)))
    (f : MvPolynomial ι K) :
    rationalCoefficientMap x hx
      (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) f) =
        MvPolynomial.aeval x f :=
  IsLocalization.lift_eq _ _

theorem rationalCoefficientMap_injective (x : ι → R)
    (hx : AlgebraicIndependent K (fun i => IsLocalRing.residue R (x i))) :
    Function.Injective (rationalCoefficientMap x hx) :=
  (rationalCoefficientMap x hx).injective

theorem residue_rationalCoefficientMap_injective (x : ι → R)
    (hx : AlgebraicIndependent K (fun i => IsLocalRing.residue R (x i))) :
    Function.Injective ((IsLocalRing.residue R).comp (rationalCoefficientMap x hx)) :=
  ((IsLocalRing.residue R).comp (rationalCoefficientMap x hx)).injective

end LocalCoefficientField

variable (K : Type*) [Field K] (n : ℕ)
variable (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]

abbrev LocalPolynomialRing := Localization.AtPrime Q
abbrev LocalPolynomialResidue := Q.ResidueField

theorem actual_residue_field : LocalPolynomialResidue K n Q =
    IsLocalRing.ResidueField (LocalPolynomialRing K n Q) := rfl

def residueCoordinate (i : Fin n) : LocalPolynomialResidue K n Q :=
  algebraMap (MvPolynomial (Fin n) K) (LocalPolynomialResidue K n Q) (MvPolynomial.X i)

theorem localPolynomial_essFiniteType :
    Algebra.EssFiniteType K (LocalPolynomialRing K n Q) := by infer_instance

theorem localResidue_essFiniteType :
    Algebra.EssFiniteType K (LocalPolynomialResidue K n Q) := by
  exact Algebra.EssFiniteType.comp K (MvPolynomial (Fin n) K) _

theorem exists_separating_residue_basis [PerfectField K] :
    ∃ s : Finset (LocalPolynomialResidue K n Q),
      IsTranscendenceBasis K ((↑) : s → LocalPolynomialResidue K n Q) ∧
      Algebra.IsSeparable (IntermediateField.adjoin K (s : Set (LocalPolynomialResidue K n Q)))
        (LocalPolynomialResidue K n Q) := by
  let := localResidue_essFiniteType K n Q
  exact exists_isTranscendenceBasis_and_isSeparable_of_perfectField K _

theorem exists_local_lifts (s : Finset (LocalPolynomialResidue K n Q)) :
    ∃ x : s → LocalPolynomialRing K n Q,
      ∀ i, IsLocalRing.residue (LocalPolynomialRing K n Q) (x i) = (i : LocalPolynomialResidue K n Q) := by
  classical
  choose x hx using fun i : s =>
    IsLocalRing.residue_surjective (R := LocalPolynomialRing K n Q) (i : LocalPolynomialResidue K n Q)
  exact ⟨x, hx⟩

theorem residue_coordinate_equations
    (s : Finset (LocalPolynomialResidue K n Q))
    [Algebra.IsSeparable
      (IntermediateField.adjoin K (s : Set (LocalPolynomialResidue K n Q)))
      (LocalPolynomialResidue K n Q)] (i : Fin n) :
    let F := IntermediateField.adjoin K (s : Set (LocalPolynomialResidue K n Q))
    let a := residueCoordinate K n Q i
    (minpoly F a).Monic ∧ Polynomial.aeval a (minpoly F a) = 0 ∧
      Polynomial.aeval a (Polynomial.derivative (minpoly F a)) ≠ 0 := by
  dsimp only
  refine ⟨minpoly.monic (Algebra.IsSeparable.isIntegral _ _), minpoly.aeval _ _, ?_⟩
  exact (Algebra.IsSeparable.isSeparable _ _).aeval_derivative_ne_zero (minpoly.aeval _ _)

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
