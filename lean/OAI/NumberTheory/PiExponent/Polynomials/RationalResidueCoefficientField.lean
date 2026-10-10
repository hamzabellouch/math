import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalResidueResolution

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution
open scoped IntermediateField.algebraAdjoinAdjoin

variable {K R ι : Type*} [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
variable (x : ι → R)
variable (hx : AlgebraicIndependent K (fun i => IsLocalRing.residue R (x i)))

def rationalResidueEquiv : FractionRing (MvPolynomial ι K) ≃ₐ[K]
    IntermediateField.adjoin K (Set.range (fun i => IsLocalRing.residue R (x i))) :=
  IsFractionRing.algEquivOfAlgEquiv hx.aevalEquiv

@[simp] theorem rationalResidueEquiv_polynomial (f : MvPolynomial ι K) :
    ((rationalResidueEquiv x hx
      (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) f)) :
        IsLocalRing.ResidueField R) =
      MvPolynomial.aeval (fun i => IsLocalRing.residue R (x i)) f := by
  rw [rationalResidueEquiv, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  rfl

def residueCoefficientSection :
    IntermediateField.adjoin K (Set.range (fun i => IsLocalRing.residue R (x i))) →+* R :=
  (rationalCoefficientMap x hx).comp (rationalResidueEquiv x hx).symm.toRingHom

theorem residueCoefficientSection_residue :
    (IsLocalRing.residue R).comp (residueCoefficientSection x hx) =
      (IntermediateField.adjoin K
        (Set.range (fun i => IsLocalRing.residue R (x i)))).val.toRingHom := by
  have h : (IsLocalRing.residue R).comp (rationalCoefficientMap x hx) =
      ((IntermediateField.adjoin K
        (Set.range (fun i => IsLocalRing.residue R (x i)))).val.toRingHom).comp
          (rationalResidueEquiv x hx).toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial ι K))
    apply RingHom.ext
    intro f
    change IsLocalRing.residue R
      (rationalCoefficientMap x hx (algebraMap _ (FractionRing (MvPolynomial ι K)) f)) =
      ((rationalResidueEquiv x hx (algebraMap _ (FractionRing (MvPolynomial ι K)) f)) :
        IsLocalRing.ResidueField R)
    rw [rationalCoefficientMap_polynomial, rationalResidueEquiv_polynomial]
    exact MvPolynomial.comp_aeval_apply (f := x) (residueAlgHom (K := K) (R := R)) f
  apply RingHom.ext
  intro a
  have ha := RingHom.congr_fun h ((rationalResidueEquiv x hx).symm a)
  change IsLocalRing.residue R
    (rationalCoefficientMap x hx ((rationalResidueEquiv x hx).symm a)) = (a : IsLocalRing.ResidueField R)
  change IsLocalRing.residue R
    (rationalCoefficientMap x hx ((rationalResidueEquiv x hx).symm a)) =
      ((rationalResidueEquiv x hx ((rationalResidueEquiv x hx).symm a)) :
        IsLocalRing.ResidueField R) at ha
  rw [AlgEquiv.apply_symm_apply] at ha
  exact ha

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
