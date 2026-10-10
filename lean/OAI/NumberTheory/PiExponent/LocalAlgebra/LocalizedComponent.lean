import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

namespace OAI

namespace PiExponentJets.W22

variable {R : Type*} [CommRing R]

theorem radical_mem_minimalPrimes (I : Ideal R) [I.radical.IsPrime] :
    I.radical ∈ I.minimalPrimes := by
  rw [← Ideal.radical_minimalPrimes, Ideal.minimalPrimes_eq_subsingleton_self]
  exact Set.mem_singleton _

theorem mem_minimalPrimes_of_localized_radical
    (I P : Ideal R) [P.IsPrime]
    (hrad : (I.map (algebraMap R (Localization.AtPrime P))).radical =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    P ∈ I.minimalPrimes := by
  have hp : (I.map (algebraMap R (Localization.AtPrime P))).radical.IsPrime := by
    rw [hrad]
    infer_instance
  let := hp
  have hm := radical_mem_minimalPrimes (I.map (algebraMap R (Localization.AtPrime P)))
  rw [hrad, IsLocalization.minimalPrimes_map P.primeCompl (Localization.AtPrime P)] at hm
  change (IsLocalRing.maximalIdeal (Localization.AtPrime P)).comap
    (algebraMap R (Localization.AtPrime P)) ∈ I.minimalPrimes at hm
  simpa only [Localization.AtPrime.under_maximalIdeal] using hm

end PiExponentJets.W22

end OAI
