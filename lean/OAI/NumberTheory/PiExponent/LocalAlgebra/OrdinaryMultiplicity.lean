import OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor
import OAI.NumberTheory.PiExponent.Jets.PrimeTaylorCotangent

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryMultiplicity

open scoped BigOperators
open OrdinaryDerivatives DerivativeIdeals CommutingTaylor
open PiExponentApprox.TransverseMultiplicity

def polynomialTaylor (n k : ℕ) (B : Fin k → Fin n)
    (Q : Ideal (OrdinaryDerivatives.Polynomial n)) [Q.IsPrime] :
    OrdinaryDerivatives.Polynomial n →+* MvPowerSeries (Fin k) Q.ResidueField :=
  residueTaylorFin k (fun j => partialFrame n (B j))
    (algebraMap (OrdinaryDerivatives.Polynomial n) Q.ResidueField)

@[simp] theorem polynomialTaylor_constant (n k : ℕ) (B : Fin k → Fin n)
    (Q : Ideal (OrdinaryDerivatives.Polynomial n)) [Q.IsPrime] (p : OrdinaryDerivatives.Polynomial n) :
    MvPowerSeries.constantCoeff (polynomialTaylor n k B Q p) =
      algebraMap (Localization.AtPrime Q) Q.ResidueField
        (algebraMap (OrdinaryDerivatives.Polynomial n) (Localization.AtPrime Q) p) := by
  rw [← IsScalarTower.algebraMap_apply]
  exact constantCoeff_residueTaylorFin k _ _ p

def localTaylor (n k : ℕ) (B : Fin k → Fin n)
    (Q : Ideal (OrdinaryDerivatives.Polynomial n)) [Q.IsPrime] :
    Localization.AtPrime Q →+* MvPowerSeries (Fin k) Q.ResidueField :=
  localizedTaylorMap Q.primeCompl (polynomialTaylor n k B Q)
    (algebraMap (Localization.AtPrime Q) Q.ResidueField) (polynomialTaylor_constant n k B Q)

@[simp] theorem localTaylor_constant (n k : ℕ) (B : Fin k → Fin n)
    (Q : Ideal (OrdinaryDerivatives.Polynomial n)) [Q.IsPrime] (x : Localization.AtPrime Q) :
    MvPowerSeries.constantCoeff (localTaylor n k B Q x) =
      algebraMap (Localization.AtPrime Q) Q.ResidueField x :=
  RingHom.congr_fun (localizedTaylorMap_constant Q.primeCompl
    (polynomialTaylor n k B Q) (algebraMap (Localization.AtPrime Q) Q.ResidueField)
    (polynomialTaylor_constant n k B Q)) x

theorem localTaylor_firstCoefficient (n k : ℕ) (B : Fin k → Fin n)
    (Q : Ideal (OrdinaryDerivatives.Polynomial n)) [Q.IsPrime] (j : Fin k) (x : Localization.AtPrime Q) :
    MvPowerSeries.coeff (Finsupp.single j 1) (localTaylor n k B Q x) =
      primeLocalDirectional Q (Pi.basisFun Q.ResidueField _ (B j)) x := by
  apply prime_localizedTaylor_firstCoefficient Q (polynomialTaylor n k B Q)
    (polynomialTaylor_constant n k B Q) (fun j => Pi.basisFun Q.ResidueField _ (B j))
  intro l p
  change MvPowerSeries.coeff (Finsupp.single l 1)
    (residueTaylorFin k (fun j => partialFrame n (B j))
      (algebraMap (OrdinaryDerivatives.Polynomial n) Q.ResidueField) p) = _
  rw [coeff_single_residueTaylorFin]
  simp [Pi.basisFun_apply, Pi.single_apply, partialFrame_apply, primeResidueMap]

theorem prime_rectangular_length_lower (n k : ℕ)
    (Q : Ideal (OrdinaryDerivatives.Polynomial n)) [Q.IsPrime] (B : Fin k → Fin n)
    (hB : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField _ (B j))))
    (I : Ideal (OrdinaryDerivatives.Polynomial n)) (cost : Fin n → ℝ) (box : Fin k → ℕ) (delta : ℝ)
    (hbox : ∀ i, 2 ≤ box i) (hcost : ∀ i, 0 ≤ cost i)
    (hbudget : ∑ i, ((box i - 1 : ℕ) : ℝ) * cost (B i) ≤ delta)
    (hvanish : ∀ p ∈ I, ∀ l : List (Fin n),
      wordCost cost l ≤ delta → OrdinaryDerivatives.word n l p ∈ Q) :
    (∏ i, box i : ℕ) ≤
      Module.length (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ I.map
          (algebraMap (OrdinaryDerivatives.Polynomial n) (Localization.AtPrime Q))) := by
  have hCot := prime_rectangular_mapCotangent_surjective Q (localTaylor n k B Q)
    (localTaylor_constant n k B Q) (fun j => Pi.basisFun Q.ResidueField _ (B j)) hB
    (localTaylor_firstCoefficient n k B Q) box hbox
  have hP : IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≤
      RingHom.ker (algebraMap (Localization.AtPrime Q) Q.ResidueField) := by
    rw [show RingHom.ker (algebraMap (Localization.AtPrime Q) Q.ResidueField) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) from IsLocalRing.ker_residue]
  apply rectangularTaylor_length_lower box (rectangularPositive box hbox)
    (localTaylor n k B Q) (algebraMap (Localization.AtPrime Q) Q.ResidueField)
    IsLocalRing.residue_surjective (localTaylor_constant n k B Q)
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) _ hP hCot
  apply localizedTaylorMap_ideal_le Q.primeCompl (polynomialTaylor n k B Q)
    (algebraMap (Localization.AtPrime Q) Q.ResidueField) (polynomialTaylor_constant n k B Q)
  apply OrdinaryTaylor.ordinary_residueTaylor_ideal_le n k B
    (algebraMap (OrdinaryDerivatives.Polynomial n) Q.ResidueField) I cost box delta hcost hbudget
  intro p hp l hl
  exact Ideal.algebraMap_residueField_eq_zero.mpr (hvanish p hp l hl)

end PiExponent.OrdinaryMultiplicity
end

end OAI
