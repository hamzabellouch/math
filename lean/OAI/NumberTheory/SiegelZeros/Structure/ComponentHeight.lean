import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.LocalizedRadical

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W22

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

theorem height_le_card_of_localized_radical_span
    (s : Finset R) (P : Ideal R) [P.IsPrime]
    (hrad : ((Ideal.span (s : Set R)).map
      (algebraMap R (Localization.AtPrime P))).radical =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    P.height ≤ s.card :=
  Ideal.height_le_card_of_mem_minimalPrimes_span_finset
    (mem_minimalPrimes_of_localized_radical (Ideal.span (s : Set R)) P hrad)

theorem height_le_card_of_mem_minimalPrimes_range
    {ι : Type*} [Fintype ι] (g : ι → R) (P : Ideal R)
    (hP : P ∈ (Ideal.span (Set.range g)).minimalPrimes) :
    P.height ≤ Fintype.card ι := by
  classical
  have hspan : (↑(Finset.univ.image g) : Set R) = Set.range g := by
    simp
  have hheight : P.height ≤ (Finset.univ.image g).card :=
    Ideal.height_le_card_of_mem_minimalPrimes_span_finset (by simpa [hspan] using hP)
  exact hheight.trans (by exact_mod_cast Finset.card_image_le (s := Finset.univ) (f := g))

end WeightedTorusJets.W22

end

end SiegelZeros

end OAI
