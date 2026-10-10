import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDimension
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialMaximalHeight

namespace OAI

namespace PiExponentJets.W29

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
    PiExponentSiegelAux.W09.polynomialMaximal_height k d p
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

end PiExponentJets.W29

end OAI
