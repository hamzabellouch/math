import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.AffineResidueTranscendence
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.PolynomialLocalRegularParameters
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.QuotientPrimeResidueBasis

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W24

open scoped nonZeroDivisors

section QuotientDimension

variable {R : Type*} [CommRing R]

theorem proper_prime_cut_dimension_succ_le
    (P Q : Ideal R) [P.IsPrime] (f : R)
    (hfP : f ∉ P) (hPQ : P ≤ Q) (hfQ : f ∈ Q) :
    ringKrullDim (R ⧸ Q) + 1 ≤ ringKrullDim (R ⧸ P) := by
  let g : (R ⧸ P) →+* (R ⧸ Q) := Ideal.Quotient.factor hPQ
  have hf0 : Ideal.Quotient.mk P f ≠ 0 := by
    exact fun h => hfP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hreg : Ideal.Quotient.mk P f ∈ (R ⧸ P)⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hf0
  apply ringKrullDim_succ_le_of_surjective g (Ideal.Quotient.factor_surjective hPQ) hreg
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hfQ

theorem proper_prime_cut_dimension_le
    (P Q : Ideal R) [P.IsPrime] (f : R)
    (hfP : f ∉ P) (hPQ : P ≤ Q) (hfQ : f ∈ Q)
    (s : ℕ) (hdim : ringKrullDim (R ⧸ P) = (s : WithBot ℕ∞) + 2) :
    ringKrullDim (R ⧸ Q) ≤ (s : WithBot ℕ∞) + 1 := by
  apply ENat.WithBot.add_le_add_one_right_iff.mp
  have h := proper_prime_cut_dimension_succ_le P Q f hfP hPQ hfQ
  simpa only [hdim, add_assoc, one_add_one_eq_two] using h

end QuotientDimension

section MinimalPrimeHeight

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

theorem proper_prime_cut_relative_height_eq_one
    (P Q : Ideal R) [P.IsPrime] (f : R) (hfP : f ∉ P)
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    (Q.map (Ideal.Quotient.mk P)).height = 1 := by
  have : Q.IsPrime := hQ.1.1
  have hPQ : P ≤ Q := le_sup_left.trans hQ.1.2
  have hfQ : f ∈ Q :=
    (Ideal.span_singleton_le_iff_mem Q).mp (le_sup_right.trans hQ.1.2)
  have : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
      rwa [Ideal.mk_ker])
  have hne : Q.map (Ideal.Quotient.mk P) ≠ ⊥ := by
    intro h
    have hQP : Q ≤ P := by
      simpa only [Ideal.mk_ker] using
        (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk P)).mp h
    exact hfP (hQP hfQ)
  have hlo : 1 ≤ (Q.map (Ideal.Quotient.mk P)).height := by
    have hlt : (⊥ : Ideal (R ⧸ P)) < Q.map (Ideal.Quotient.mk P) :=
      bot_lt_iff_ne_bot.mpr hne
    have h := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    simpa only [Ideal.height_bot, zero_add] using h
  exact le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes hQ) hlo

theorem proper_prime_cut_relative_local_dimension
    (P Q : Ideal R) [P.IsPrime] (f : R) (hfP : f ∉ P)
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    letI : Q.IsPrime := hQ.1.1
    letI : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact le_sup_left.trans hQ.1.2)
    ringKrullDim (Localization.AtPrime (Q.map (Ideal.Quotient.mk P))) = 1 := by
  let : Q.IsPrime := hQ.1.1
  let : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact le_sup_left.trans hQ.1.2)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
      (Q.map (Ideal.Quotient.mk P))
      (Localization.AtPrime (Q.map (Ideal.Quotient.mk P))),
    proper_prime_cut_relative_height_eq_one P Q f hfP hQ]
  rfl

omit [IsNoetherianRing R] in
theorem minimal_proper_prime_cut_dimension_le
    (P Q : Ideal R) [P.IsPrime] (f : R) (hfP : f ∉ P)
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes)
    (s : ℕ) (hdim : ringKrullDim (R ⧸ P) = (s : WithBot ℕ∞) + 2) :
    ringKrullDim (R ⧸ Q) ≤ (s : WithBot ℕ∞) + 1 :=
  proper_prime_cut_dimension_le P Q f hfP (le_sup_left.trans hQ.1.2)
    ((Ideal.span_singleton_le_iff_mem Q).mp (le_sup_right.trans hQ.1.2)) s hdim

end MinimalPrimeHeight

end WeightedTorusJets.W24

end

section

namespace WeightedTorusJets.W29

section GoingDownHeight

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Algebra.HasGoingDown A B]

theorem under_height_le_of_goingDown (P : Ideal B) [P.IsPrime] :
    (P.under A).height ≤ P.height := by
  rw [PrimeSpectrum.height_eq_orderHeight (⟨P.under A, inferInstance⟩ : PrimeSpectrum A),
    PrimeSpectrum.height_eq_orderHeight (⟨P, inferInstance⟩ : PrimeSpectrum B)]
  apply Order.height_le
  intro l hl
  let : P.LiesOver l.last.asIdeal := ⟨congrArg PrimeSpectrum.asIdeal hl⟩
  obtain ⟨L, hlen, hlast, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
  have h : (L.length : ℕ∞) ≤ Order.height (⟨P, inferInstance⟩ : PrimeSpectrum B) :=
    Order.length_le_height (le_of_eq hlast)
  simpa only [hlen] using h

end GoingDownHeight

section ClosedPoint

variable (k B : Type*) [Field k] [CommRing B] [IsDomain B]
  [Algebra k B] [Algebra.FiniteType k B]

include k

theorem affineDomain_maximal_height (m : Ideal B) [m.IsMaximal] :
    (m.height : WithBot ℕ∞) = ringKrullDim B := by
  obtain ⟨d, g, hg, hfin, hdim⟩ := W24.exists_finite_normalization_with_dimension k B
  let A := MvPolynomial (Fin d) k
  let : Algebra A B := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hfin.to_isIntegral⟩
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hg
  have : IsIntegrallyClosed A := inferInstance
  have : Algebra.HasGoingDown A B := inferInstance
  let p : Ideal A := m.under A
  have : p.IsMaximal := by
    dsimp [p]
    infer_instance
  have hp : p.height = (d : ℕ∞) :=
    SiegelZerosAwei.W09.polynomialMaximal_height k d p
  have hlo : (d : ℕ∞) ≤ m.height := by
    rw [← hp]
    exact under_height_le_of_goingDown m
  apply le_antisymm
  · exact Ideal.height_le_ringKrullDim_of_ne_top
      (Ideal.IsMaximal.ne_top (inferInstance : m.IsMaximal))
  · rw [hdim]
    exact WithBot.coe_le_coe.mpr hlo

theorem closedPoint_local_dimension (m : Ideal B) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = ringKrullDim B := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
  exact affineDomain_maximal_height k B m

end ClosedPoint

end WeightedTorusJets.W29

end

section

noncomputable section
namespace WeightedTorusJets.W24

theorem affine_prime_dimension_of_closedPoint_presentation
    (k B β C : Type*) [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] [Finite β]
    [CommRing C] [IsDomain C] [Algebra k C] [Algebra B C]
    [Algebra (FractionRing (MvPolynomial β k)) C]
    [IsScalarTower k B C]
    [IsScalarTower k (FractionRing (MvPolynomial β k)) C]
    [FaithfulSMul B C]
    [Algebra.FiniteType (FractionRing (MvPolynomial β k)) C]
    (q : Ideal B) [q.IsPrime]
    (b : β → q.ResidueField) (hb : IsTranscendenceBasis k b)
    (M : Submonoid B) [IsLocalization M C]
    (m : Ideal C) [m.IsMaximal]
    (e : Localization.AtPrime q ≃+* Localization.AtPrime m) :
    (q.height : WithBot ℕ∞) + ringKrullDim (B ⧸ q) = ringKrullDim B := by
  have he : (q.height : WithBot ℕ∞) = ringKrullDim C := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q),
      e.ringKrullDim, W29.closedPoint_local_dimension (FractionRing (MvPolynomial β k)) C m]
  have hd := coefficient_localization_dimension k (FractionRing (MvPolynomial β k)) B C M
    (rational_coefficient_trdeg_lt_aleph0 k β)
  rw [coefficient_trdeg_eq_prime_quotient_dimension k B β q b hb] at hd
  exact he.symm ▸ hd

end WeightedTorusJets.W24

end

end

section

noncomputable section
namespace WeightedTorusJets.W24
open SiegelZeros.W23 SiegelZerosAwei.W09
open WeightedTorusJets.PolynomialLocalResidueResolution

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

section ArbitraryFiniteVariables
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

end ArbitraryFiniteVariables

end WeightedTorusJets.W24

end

end

section

namespace WeightedTorusJets.W24

variable (k σ : Type*) [Field k] [Finite σ]

theorem minimal_prime_hypersurface_dimension
    (P Q : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (f : MvPolynomial σ k) (hfP : f ∉ P)
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes)
    (s : ℕ)
    (hdim : ringKrullDim (MvPolynomial σ k ⧸ P) = ((s + 2 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (MvPolynomial σ k ⧸ Q) = ((s + 1 : ℕ) : WithBot ℕ∞) := by
  let : Q.IsPrime := hQ.1.1
  have hd := polynomial_prime_pair_dimension k σ P Q (le_sup_left.trans hQ.1.2)
  rw [proper_prime_cut_relative_height_eq_one P Q f hfP hQ] at hd
  have he : ringKrullDim (MvPolynomial σ k ⧸ Q) + 1 =
      ((s + 1 : ℕ) : WithBot ℕ∞) + 1 := by
    calc
      ringKrullDim (MvPolynomial σ k ⧸ Q) + 1 =
          1 + ringKrullDim (MvPolynomial σ k ⧸ Q) := add_comm _ _
      _ = ringKrullDim (MvPolynomial σ k ⧸ P) := hd
      _ = ((s + 2 : ℕ) : WithBot ℕ∞) := hdim
      _ = ((s + 1 : ℕ) : WithBot ℕ∞) + 1 := by
        rw [show s + 2 = (s + 1) + 1 by omega, Nat.cast_add, Nat.cast_one]
  exact ENat.WithBot.add_one_cancel.mp he

end WeightedTorusJets.W24

end

end SiegelZeros

end OAI
