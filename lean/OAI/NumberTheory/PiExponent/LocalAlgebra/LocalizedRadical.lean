import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedComponent

namespace OAI

namespace PiExponentJets.W22

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

end PiExponentJets.W22

end OAI
