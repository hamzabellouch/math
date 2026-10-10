import OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting
import OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParametersTransport
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialMaximalHeight

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable (K : Type*) [Field K] (n : ℕ)
variable (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]

theorem exists_regularParameters_actual_height :
    ∃ h : ℕ, Q.height = (h : ℕ∞) ∧
      ∃ xs : List (Localization.AtPrime Q),
        xs.length = h ∧ RingTheory.Sequence.IsRegular (Localization.AtPrime Q) xs ∧
        Ideal.ofList xs = IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
  classical
  obtain ⟨t, j, htfinite, hj, hcoord, ht⟩ := exists_coordinate_basis_indices K n Q
  let A := RemainingCoordinate j
  let F := SplitCoefficientField K t
  let Qs := coordinateSplitPrime K Q t j hj
  let hB := coordinateSplitPrime_basis K Q t j hj hcoord ht
  let m₀ := closedPolynomialIdeal K A t Qs hB
  let : m₀.IsMaximal := closedPolynomialIdeal_isMaximal K A t Qs hB
  let e₀ : Localization.AtPrime Q ≃+* Localization.AtPrime m₀ :=
    coordinateBasisClosedPointEquiv K Q t j hj hcoord ht
  let h := Fintype.card A
  let eFin : MvPolynomial A F ≃ₐ[F] MvPolynomial (Fin h) F :=
    MvPolynomial.renameEquiv F (Fintype.equivFin A)
  let m : Ideal (MvPolynomial (Fin h) F) := m₀.map eFin.toRingHom
  let : m.IsMaximal := (inferInstance : m₀.IsMaximal).map_bijective eFin.toRingHom eFin.bijective
  let e : Localization.AtPrime Q ≃+* Localization.AtPrime m :=
    e₀.trans (PiExponentSiegel.W23.atPrimeEquivOfRingEquiv eFin.toRingEquiv m₀)
  have hheight : Q.height = (h : ℕ∞) := by
    have he := ringKrullDim_eq_of_ringEquiv e
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q),
      IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m),
      PiExponentSiegelAux.W09.polynomialMaximal_height F h m] at he
    exact WithBot.coe_injective he
  refine ⟨h, hheight, ?_⟩
  exact PiExponentSiegel.W10.TriangularLocalParameters.polynomialMaximal_regularParameters_of_ringEquiv
    h F m e

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
