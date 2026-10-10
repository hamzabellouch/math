import OAI.NumberTheory.TotientAsymptotic.FordInputs
import OAI.NumberTheory.TotientAsymptotic.PPTFixedBandLimit

namespace OAI

/-! Asymptotic counting and least-preimage interval theorems. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem totient_asymptotic_formula
    :
    TendstoUniformlyOn (fun H => AH H (fun _ => 1)) (A (fun _ => 1))
      atTop (Set.Ico (0 : ℝ) 1) ∧
    (∃ cMinus cPlus : ℝ, 0 < cMinus ∧ ∀ s ∈ Set.Ico (0 : ℝ) 1,
      cMinus ≤ A (fun _ => 1) s ∧ A (fun _ => 1) s ≤ cPlus) ∧
    Tendsto (fun x => V x/mainTerm x) atTop (nhds 1) ∧
    ∀ c : ℝ, 0 < c → Tendsto (fun x => V (c*x)/V x) atTop (nhds c) :=
  conditional_main_theorem_of_structure fordScaleBounds extractedStructureInput primeNumberTheoremInput fordUnitPrimeBoxInput
    fordRenewalInput mertensProductInput fordLemma26Input fordLemma51Input fordCoordinateConcentrationInput

theorem weighted_totient_asymptotic
    (k : ℕ) (hk : 1≤k) :
    TendstoUniformlyOn (fun H => AH H (fk k)) (A (fk k)) atTop (Set.Ico (0 : ℝ) 1) ∧
    Tendsto (fun x => normalizedCount (N k) x-A (fk k) (theta x)) atTop (nhds 0) ∧
    ((∃ d : ℕ, IsTotient d ∧ k*d<ell d) →
      ∃ cMinus cPlus : ℝ, 0<cMinus ∧ 0<cPlus ∧
        (∀ s∈Set.Ico (0 : ℝ) 1, cMinus≤A (fk k) s ∧ A (fk k) s≤cPlus) ∧
        Tendsto (fun x => N k x/(tupleNormalization x*A (fk k) (theta x))) atTop (nhds 1) ∧
        ∀ᶠ x : ℝ in atTop, (cMinus/cPlus)*V x≤N k x ∧ N k x≤V x) ∧
    ((¬∃ d : ℕ, IsTotient d ∧ k*d<ell d) →
      (∀ x : ℝ, 0<x → N k x=0) ∧ (∀ s∈Set.Ico (0 : ℝ) 1, A (fk k) s=0)) :=
  conditional_companion_theorem_of_structure fordScaleBounds extractedStructureInput primeNumberTheoremInput fordUnitPrimeBoxInput
    fordRenewalInput mertensProductInput fordLemma26Input fordLemma51Input fordCoordinateConcentrationInput pptBoundedFiberPropagation k hk

theorem weighted_totient_one_two
    :
    ∀ k∈({1,2} : Finset ℕ), ∃ c : ℝ, 0<c ∧
      ∀ s∈Set.Ico (0 : ℝ) 1, c≤A (fk k) s :=
  companion_one_two_without_seed_input_of_structure fordScaleBounds extractedStructureInput primeNumberTheoremInput fordUnitPrimeBoxInput
    fordRenewalInput mertensProductInput fordLemma26Input fordLemma51Input fordCoordinateConcentrationInput pptBoundedFiberPropagation

theorem coefficient_nonnegative (H : ℕ) {s : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) : 0 ≤ AH H (fun _ => 1) s :=
  AH_nonneg H hs (fun _ => 1) (fun _ _ => ⟨zero_le_one, le_rfl⟩)

end TotientAsymptotic

end

end OAI
