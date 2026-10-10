import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Localization.LocalizationLocalization
import OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLengthEquivalence

namespace OAI

namespace PiExponentJets.W22

variable {A : Type*} [CommRing A]

noncomputable def localPrimeTowerEquiv
    (Q : Ideal A) [Q.IsPrime] (p : Ideal (Localization.AtPrime Q)) [p.IsPrime] :
    Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q))) ≃ₐ[A]
      Localization.AtPrime p :=
  IsLocalization.localizationLocalizationAtPrimeIsoLocalization Q.primeCompl p

@[simp] theorem localPrimeTowerEquiv_algebraMap
    (Q : Ideal A) [Q.IsPrime] (p : Ideal (Localization.AtPrime Q)) [p.IsPrime] (a : A) :
    localPrimeTowerEquiv Q p
      (algebraMap A (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q)))) a) =
      algebraMap A (Localization.AtPrime p) a :=
  (localPrimeTowerEquiv Q p).commutes a

theorem localPrimeTower_map_ideal
    (Q : Ideal A) [Q.IsPrime] (p : Ideal (Localization.AtPrime Q)) [p.IsPrime] (I : Ideal A) :
    (I.map (algebraMap A (Localization.AtPrime Q))).map
      (algebraMap (Localization.AtPrime Q) (Localization.AtPrime p)) =
    (I.map (algebraMap A
      (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q)))))).map
        (localPrimeTowerEquiv Q p).toRingEquiv.toRingHom := by
  have he : (localPrimeTowerEquiv Q p).toRingEquiv.toRingHom.comp
      (algebraMap A (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q))))) =
      algebraMap A (Localization.AtPrime p) := by
    ext a
    exact localPrimeTowerEquiv_algebraMap Q p a
  rw [Ideal.map_map, Ideal.map_map, he,
    ← IsScalarTower.algebraMap_eq A (Localization.AtPrime Q) (Localization.AtPrime p)]

theorem localPrimeTower_quotient_length
    (Q : Ideal A) [Q.IsPrime] (p : Ideal (Localization.AtPrime Q)) [p.IsPrime] (I : Ideal A) :
    Module.length (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q))))
      (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q))) ⧸
        I.map (algebraMap A
          (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q)))))) =
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ (I.map (algebraMap A (Localization.AtPrime Q))).map
        (algebraMap (Localization.AtPrime Q) (Localization.AtPrime p))) :=
  quotient_length_eq_of_ringEquiv (localPrimeTowerEquiv Q p).toRingEquiv _ _
    (localPrimeTower_map_ideal Q p I)

end PiExponentJets.W22

end OAI
