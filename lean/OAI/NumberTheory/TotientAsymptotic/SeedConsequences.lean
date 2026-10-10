import OAI.NumberTheory.TotientAsymptotic.SeedMinimum
import OAI.NumberTheory.TotientAsymptotic.ConditionalCompanion

namespace OAI

noncomputable section
open scoped Topology
namespace TotientAsymptotic

/-- The arithmetic seed assertion requires no published hypothesis. -/
theorem seeds_one_two : ∀ k∈({1,2} : Finset ℕ),
    ∃ d : ℕ, IsTotient d ∧ k*d<ell d :=
  companion_seeds_one_two seed_isTotient seed_least_preimage

/-- The k=1,2 weighted conclusions after discharging the finite seed input. -/
theorem companion_one_two_without_seed_input_of_structure (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) (hconc : FordCoordinateConcentrationInput)
    (hppt : ∀ d : ℕ, IsTotient d → PPTBoundedFiberPropagation d) :
    ∀ k∈({1,2} : Finset ℕ), ∃ c : ℝ, 0<c ∧
      ∀ s∈Set.Ico (0 : ℝ) 1, c≤A (fk k) s :=
  conditional_companion_one_two_of_structure hscale hstruct hpnt hbox hren hmertens h26 h51 hconc
    hppt seed_isTotient seed_least_preimage


/-- The original published-input interface remains available. -/
theorem companion_one_two_without_seed_input (hscale : FordScaleBounds)
    (h10 : FordTheorem10Input) (h16 : FordTheorem16Input) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) (hconc : FordCoordinateConcentrationInput)
    (hppt : ∀ d : ℕ, IsTotient d → PPTBoundedFiberPropagation d) :
    ∀ k∈({1,2} : Finset ℕ), ∃ c : ℝ, 0<c ∧
      ∀ s∈Set.Ico (0 : ℝ) 1, c≤A (fk k) s :=
  companion_one_two_without_seed_input_of_structure hscale (extractedStructureInput_of_ford hscale h10 h16) hpnt hbox hren hmertens h26 h51 hconc hppt

end TotientAsymptotic

end

end OAI
