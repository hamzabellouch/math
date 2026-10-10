import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

namespace OAI

namespace SiegelZeros


namespace WeightedTorusJets.W22

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

end WeightedTorusJets.W22



namespace WeightedTorusJets.W22

variable {R : Type*} [CommRing R]

theorem localized_radical_eq_maximal_of_mem_minimalPrimes
    (I P : Ideal R) [P.IsPrime] (hP : P ∈ I.minimalPrimes) :
    (I.map (algebraMap R (Localization.AtPrime P))).radical =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  have hreverse : P.map (algebraMap R (Localization.AtPrime P)) ≤
      (I.map (algebraMap R (Localization.AtPrime P))).radical := by
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro q ⟨hqI, hq⟩
    obtain ⟨hqprime, hqP⟩ :=
      ((IsLocalization.AtPrime.orderIsoOfPrime (Localization.AtPrime P) P) ⟨q, hq⟩).2
    rw [Ideal.map_le_iff_le_comap] at hqI ⊢
    exact hP.2 ⟨hqprime, hqI⟩ hqP
  have hmprime : (IsLocalRing.maximalIdeal (Localization.AtPrime P)).IsPrime := inferInstance
  apply le_antisymm
  · apply hmprime.radical_le_iff.mpr
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hP.1.2
  · simpa only [Localization.AtPrime.map_eq_maximalIdeal] using hreverse

end WeightedTorusJets.W22


end SiegelZeros

end OAI
