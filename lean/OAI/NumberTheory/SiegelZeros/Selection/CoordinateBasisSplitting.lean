import Mathlib.Logic.Equiv.Sum
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.AffineClosedPointLocalization
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.PrimeResidueAlgebraEquiv

namespace OAI

namespace SiegelZeros

section

noncomputable section
namespace WeightedTorusJets.PolynomialLocalResidueResolution

variable {n : ℕ} {T : Type*} (j : T → Fin n) (hj : Function.Injective j)

abbrev RemainingCoordinate := {i : Fin n // i ∉ Set.range j}

def coordinateIndexSplitting : RemainingCoordinate j ⊕ T ≃ Fin n := by
  classical
  exact (Equiv.sumCongr (Equiv.refl _) (Equiv.ofInjective j hj)).trans
    ((Equiv.sumComm _ _).trans (Equiv.sumCompl (fun i : Fin n => i ∈ Set.range j)))

@[simp] theorem coordinateIndexSplitting_inr (a : T) :
    coordinateIndexSplitting j hj (Sum.inr a) = j a := rfl

@[simp] theorem coordinateIndexSplitting_symm_selected (a : T) :
    (coordinateIndexSplitting j hj).symm (j a) = Sum.inr a := by
  rw [← coordinateIndexSplitting_inr j hj a, Equiv.symm_apply_apply]

def coordinateBasisRenaming (K : Type*) [Field K] : MvPolynomial (Fin n) K ≃ₐ[K]
    MvPolynomial (RemainingCoordinate j ⊕ T) K :=
  MvPolynomial.renameEquiv K (coordinateIndexSplitting j hj).symm

section Polynomial
variable (K : Type*) [Field K] (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]
variable (t : Set Q.ResidueField) (j : t → Fin n) (hj : Function.Injective j)
variable (hcoord : ∀ a, residueCoordinate K n Q (j a) = (a : Q.ResidueField))
variable (ht : IsTranscendenceBasis K ((↑) : t → Q.ResidueField))

abbrev coordinateSplitPrime := Q.map (coordinateBasisRenaming j hj K).toRingHom

include hcoord ht in

theorem coordinateSplitPrime_basis :
    IsTranscendenceBasis K
      (splitResidueBeta K (RemainingCoordinate j) t (coordinateSplitPrime K Q t j hj)) := by
  have hb := primeResidueAlgEquiv_transcendenceBasis
    (coordinateBasisRenaming j hj K) Q ((↑) : t → Q.ResidueField) ht
  have he : splitResidueBeta K (RemainingCoordinate j) t (coordinateSplitPrime K Q t j hj) =
      fun a : t => primeResidueAlgEquiv (coordinateBasisRenaming j hj K) Q (a : Q.ResidueField) := by
    funext a
    rw [← hcoord a]
    change algebraMap (MvPolynomial (RemainingCoordinate j ⊕ t) K)
      (coordinateSplitPrime K Q t j hj).ResidueField (MvPolynomial.X (Sum.inr a)) =
      primeResidueAlgEquiv (coordinateBasisRenaming j hj K) Q
        (algebraMap (MvPolynomial (Fin n) K) Q.ResidueField (MvPolynomial.X (j a)))
    rw [primeResidueAlgEquiv_algebraMap]
    change algebraMap _ (coordinateSplitPrime K Q t j hj).ResidueField (MvPolynomial.X (Sum.inr a)) =
      algebraMap _ (coordinateSplitPrime K Q t j hj).ResidueField
        (MvPolynomial.rename (coordinateIndexSplitting j hj).symm (MvPolynomial.X (j a)))
    rw [MvPolynomial.rename_X, coordinateIndexSplitting_symm_selected]
  rw [he]
  exact hb

def coordinateBasisLocalEquiv : Localization.AtPrime Q ≃+*
    Localization.AtPrime (coordinateSplitPrime K Q t j hj) :=
  SiegelZeros.W23.atPrimeEquivOfRingEquiv (coordinateBasisRenaming j hj K).toRingEquiv Q

def coordinateBasisClosedPointEquiv : Localization.AtPrime Q ≃+*
    Localization.AtPrime
      (closedPolynomialIdeal K (RemainingCoordinate j) t (coordinateSplitPrime K Q t j hj)
        (coordinateSplitPrime_basis K Q t j hj hcoord ht)) :=
  (coordinateBasisLocalEquiv K Q t j hj).trans
    (polynomialPrimeClosedPointEquiv K (RemainingCoordinate j) t
      (coordinateSplitPrime K Q t j hj)
      (coordinateSplitPrime_basis K Q t j hj hcoord ht))

end Polynomial
end WeightedTorusJets.PolynomialLocalResidueResolution

end

end

end SiegelZeros

end OAI
