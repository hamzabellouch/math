import Mathlib.RingTheory.Localization.AtPrime.Basic
import OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLengthEquivalence

namespace OAI

namespace PiExponentJets.W22

variable {R S : Type*} [CommRing R] [CommRing S]

theorem primeCompl_map_eq_of_comap
    (e : R ≃+* S) (P : Ideal R) (Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    (hPQ : P = Q.comap e.toRingHom) :
    P.primeCompl.map e.toMonoidHom = Q.primeCompl := by
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    change e r ∉ Q
    intro h
    apply hr
    rw [hPQ]
    exact h
  · intro hx
    change x ∉ Q at hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    change e.symm x ∉ P
    rw [hPQ]
    change e (e.symm x) ∉ Q
    simpa only [e.apply_symm_apply] using hx

noncomputable def primeLocalizationEquiv
    (e : R ≃+* S) (P : Ideal R) (Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    (hPQ : P = Q.comap e.toRingHom) :
    Localization.AtPrime P ≃+* Localization.AtPrime Q :=
  IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime P) (Localization.AtPrime Q)
    e (primeCompl_map_eq_of_comap e P Q hPQ)

theorem primeLocalizationEquiv_map_ideal
    (e : R ≃+* S) (P : Ideal R) (Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    (hPQ : P = Q.comap e.toRingHom) (I : Ideal R) :
    (I.map (algebraMap R (Localization.AtPrime P))).map
      (primeLocalizationEquiv e P Q hPQ).toRingHom =
    (I.map e.toRingHom).map (algebraMap S (Localization.AtPrime Q)) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  ext r
  exact IsLocalization.ringEquivOfRingEquiv_eq
    (primeCompl_map_eq_of_comap e P Q hPQ) r

theorem localized_quotient_length_eq_of_ringEquiv
    (e : R ≃+* S) (P : Ideal R) (Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    (hPQ : P = Q.comap e.toRingHom) (I : Ideal R) :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))) =
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ (I.map e.toRingHom).map
        (algebraMap S (Localization.AtPrime Q))) :=
  quotient_length_eq_of_ringEquiv (primeLocalizationEquiv e P Q hPQ)
    (I.map (algebraMap R (Localization.AtPrime P)))
    ((I.map e.toRingHom).map (algebraMap S (Localization.AtPrime Q)))
    (primeLocalizationEquiv_map_ideal e P Q hPQ I).symm

end PiExponentJets.W22

end OAI
