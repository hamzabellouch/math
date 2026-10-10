import OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization
import OAI.NumberTheory.PiExponent.LocalAlgebra.AffinePrimeDimensionBridge
import OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting
import OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientPrimeResidueBasis

namespace OAI

noncomputable section
namespace PiExponentJets.W24
open PiExponentSiegel.W23 PiExponentSiegelAux.W09
open PiExponentJets.PolynomialLocalResidueResolution

section Equivalence
variable {A B : Type*} [CommRing A] [CommRing B]

local instance imagePrime_isPrime (e : A ≃+* B) (Q : Ideal A) [Q.IsPrime] :
    (Q.map e.toRingHom).IsPrime := Ideal.map_isPrime_of_equiv e

theorem ringEquiv_localizedIdeal_map (e : A ≃+* B)
    (P Q : Ideal A) [Q.IsPrime] :
    (parameterLocalizedIdeal P Q).map (atPrimeEquivOfRingEquiv e Q).toRingHom =
      parameterLocalizedIdeal (P.map e.toRingHom) (Q.map e.toRingHom) := by
  unfold parameterLocalizedIdeal
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro a
  exact atPrimeEquivOfRingEquiv_algebraMap e Q a

def ringEquiv_localQuotient (e : A ≃+* B) (P Q : Ideal A) [Q.IsPrime] :
    (Localization.AtPrime Q ⧸ parameterLocalizedIdeal P Q) ≃+*
      (Localization.AtPrime (Q.map e.toRingHom) ⧸
        parameterLocalizedIdeal (P.map e.toRingHom) (Q.map e.toRingHom)) :=
  Ideal.quotientEquiv _ _ (atPrimeEquivOfRingEquiv e Q)
    (ringEquiv_localizedIdeal_map e P Q).symm

end Equivalence

section Split
variable (k α β : Type*) [Field k] [Finite α] [Finite β]
variable (P Q : Ideal (SplitPolynomial k α β)) [P.IsPrime] [Q.IsPrime]

theorem split_polynomial_prime_pair_local_dimension
    (hPQ : P ≤ Q)
    (hB : IsTranscendenceBasis k (splitResidueBeta k α β Q)) :
    ringKrullDim (Localization.AtPrime Q ⧸ parameterLocalizedIdeal P Q) +
      ringKrullDim (SplitPolynomial k α β ⧸ Q) =
        ringKrullDim (SplitPolynomial k α β ⧸ P) := by
  let C := FractionCoefficientPolynomial k α β ⧸ affineMappedIdeal k α β P
  let q := quotientParameterPrime P Q hPQ
  let m := quotientParameterPrime (affineMappedIdeal k α β P)
    (closedPolynomialIdeal k α β Q hB)
    (affineMappedIdeal_le_closedPoint k α β Q hB P hPQ)
  let := affineCoefficientAlgebra k α β
  let := affineQuotientAlgebra k α β P
  let := affineQuotient_scalarTower k α β P
  let := affineQuotient_faithfulSMul k α β Q hB P hPQ
  let := affineQuotient_isDomain k α β Q hB P hPQ
  let := affineQuotient_finiteType k α β P
  let := affineQuotient_isLocalization k α β Q hB P hPQ
  let b : β → q.ResidueField :=
    fun i => quotientPrimeResidueAlgEquiv (k := k) P Q hPQ (splitResidueBeta k α β Q i)
  have hb : IsTranscendenceBasis k b :=
    quotientPrimeResidueAlgEquiv_basis P Q hPQ (splitResidueBeta k α β Q) hB
  have hd := affine_prime_dimension_of_closedPoint_presentation k
    (SplitPolynomial k α β ⧸ P) β C q b hb
    ((coefficientDenominators k α β).map (Ideal.Quotient.mk P)) m
    (affineClosedQuotientLocalEquiv k α β Q hB P hPQ)
  have hlocal := (localizationQuotientParametersEquiv P Q hPQ).ringKrullDim
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
    (quotientParameterPrime P Q hPQ) (Localization.AtPrime (quotientParameterPrime P Q hPQ))] at hlocal
  have hquot := @ringKrullDim_eq_of_ringEquiv
    ((SplitPolynomial k α β ⧸ P) ⧸ Q.map (Ideal.Quotient.mk P))
    (SplitPolynomial k α β ⧸ Q)
    (inferInstance : CommRing ((SplitPolynomial k α β ⧸ P) ⧸
      Q.map (Ideal.Quotient.mk P))).toCommSemiring
    (inferInstance : CommRing (SplitPolynomial k α β ⧸ Q)).toCommSemiring
    (DoubleQuot.quotQuotEquivQuotOfLE hPQ)
  change ringKrullDim ((SplitPolynomial k α β ⧸ P) ⧸ q) =
    ringKrullDim (SplitPolynomial k α β ⧸ Q) at hquot
  rw [← hlocal, hquot] at hd
  exact hd

end Split

section FinVariables
variable (k : Type*) [Field k] (n : ℕ)
variable (P Q : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime] [Q.IsPrime]

theorem fin_polynomial_prime_pair_local_dimension (hPQ : P ≤ Q) :
    ringKrullDim (Localization.AtPrime Q ⧸ parameterLocalizedIdeal P Q) +
      ringKrullDim (MvPolynomial (Fin n) k ⧸ Q) =
        ringKrullDim (MvPolynomial (Fin n) k ⧸ P) := by
  classical
  obtain ⟨t, j, hfin, hj, hcoord, ht⟩ := exists_coordinate_basis_indices k n Q
  let : Finite t := hfin.to_subtype
  let e := coordinateBasisRenaming j hj k
  let P' := P.map e.toRingHom
  let Q' := Q.map e.toRingHom
  have : P'.IsPrime := Ideal.map_isPrime_of_equiv e
  have : Q'.IsPrime := Ideal.map_isPrime_of_equiv e
  have hpq : P' ≤ Q' := Ideal.map_mono hPQ
  have hb : IsTranscendenceBasis k (splitResidueBeta k (RemainingCoordinate j) t Q') :=
    coordinateSplitPrime_basis k Q t j hj hcoord ht
  have hd := split_polynomial_prime_pair_local_dimension k (RemainingCoordinate j) t P' Q' hpq hb
  have hl := (ringEquiv_localQuotient e.toRingEquiv P Q).ringKrullDim
  have hp := (Ideal.quotientEquiv P P' e.toRingEquiv rfl).ringKrullDim
  have hq := (Ideal.quotientEquiv Q Q' e.toRingEquiv rfl).ringKrullDim
  rw [← hl, ← hp, ← hq] at hd
  exact hd

end FinVariables

variable (k σ : Type*) [Field k] [Finite σ]
variable (P Q : Ideal (MvPolynomial σ k)) [P.IsPrime] [Q.IsPrime]

theorem polynomial_prime_pair_local_dimension (hPQ : P ≤ Q) :
    ringKrullDim (Localization.AtPrime Q ⧸ parameterLocalizedIdeal P Q) +
      ringKrullDim (MvPolynomial σ k ⧸ Q) = ringKrullDim (MvPolynomial σ k ⧸ P) := by
  classical
  let := Fintype.ofFinite σ
  let e : MvPolynomial σ k ≃ₐ[k] MvPolynomial (Fin (Fintype.card σ)) k :=
    MvPolynomial.renameEquiv k (Fintype.equivFin σ)
  let P' := P.map e.toRingHom
  let Q' := Q.map e.toRingHom
  have : P'.IsPrime := Ideal.map_isPrime_of_equiv e
  have : Q'.IsPrime := Ideal.map_isPrime_of_equiv e
  have hd := fin_polynomial_prime_pair_local_dimension k (Fintype.card σ) P' Q'
    (Ideal.map_mono hPQ)
  have hl := (ringEquiv_localQuotient e.toRingEquiv P Q).ringKrullDim
  have hp := (Ideal.quotientEquiv P P' e.toRingEquiv rfl).ringKrullDim
  have hq := (Ideal.quotientEquiv Q Q' e.toRingEquiv rfl).ringKrullDim
  rw [← hl, ← hp, ← hq] at hd
  exact hd

theorem polynomial_prime_pair_dimension (hPQ : P ≤ Q) :
    ((Q.map (Ideal.Quotient.mk P)).height : WithBot ℕ∞) +
      ringKrullDim (MvPolynomial σ k ⧸ Q) = ringKrullDim (MvPolynomial σ k ⧸ P) := by
  have hd := polynomial_prime_pair_local_dimension k σ P Q hPQ
  have hl := (localizationQuotientParametersEquiv P Q hPQ).ringKrullDim
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
    (quotientParameterPrime P Q hPQ) (Localization.AtPrime (quotientParameterPrime P Q hPQ))] at hl
  rw [hl] at hd
  exact hd


end PiExponentJets.W24

end

end OAI
