import OAI.NumberTheory.TotientAsymptotic.FordStructureCount
import OAI.NumberTheory.TotientAsymptotic.FiberPropagationInput
import OAI.NumberTheory.TotientAsymptotic.CollisionInput
import OAI.NumberTheory.TotientAsymptotic.NormalityInput
import OAI.NumberTheory.TotientAsymptotic.RenewalInput
import OAI.NumberTheory.TotientAsymptotic.ConcentrationInput
import OAI.NumberTheory.TotientAsymptotic.ConditionalMain
import OAI.NumberTheory.TotientAsymptotic.SeedConsequences
import OAI.NumberTheory.TotientAsymptotic.PrimeNumberTheorem
import OAI.NumberTheory.TotientAsymptotic.MertensProduct
import OAI.NumberTheory.TotientAsymptotic.PrimeBoxInput

namespace OAI

/-! Totient asymptotics from structural, sieve, prime-counting, and renewal estimates. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem main_from_ford_inputs (h10 : FordTheorem10Input)
    :
    TendstoUniformlyOn (fun H => AH H (fun _ => 1)) (A (fun _ => 1))
      atTop (Set.Ico (0 : ℝ) 1) ∧
    (∃ cMinus cPlus : ℝ, 0 < cMinus ∧ ∀ s ∈ Set.Ico (0 : ℝ) 1,
      cMinus ≤ A (fun _ => 1) s ∧ A (fun _ => 1) s ≤ cPlus) ∧
    Tendsto (fun x => V x/mainTerm x) atTop (nhds 1) ∧
    ∀ c : ℝ, 0 < c → Tendsto (fun x => V (c*x)/V x) atTop (nhds c) :=
  conditional_main_theorem fordScaleBounds h10 (fordTheorem16_of_scale fordScaleBounds) primeNumberTheoremInput fordUnitPrimeBoxInput
    fordRenewalInput mertensProductInput fordLemma26Input fordLemma51Input fordCoordinateConcentrationInput

theorem companion_from_ford_inputs (h10 : FordTheorem10Input)
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
  conditional_companion_theorem fordScaleBounds h10 (fordTheorem16_of_scale fordScaleBounds) primeNumberTheoremInput fordUnitPrimeBoxInput
    fordRenewalInput mertensProductInput fordLemma26Input fordLemma51Input fordCoordinateConcentrationInput pptBoundedFiberPropagation k hk

theorem companion_one_two_from_ford_inputs (h10 : FordTheorem10Input)
    :
    ∀ k∈({1,2} : Finset ℕ), ∃ c : ℝ, 0<c ∧
      ∀ s∈Set.Ico (0 : ℝ) 1, c≤A (fk k) s :=
  companion_one_two_without_seed_input fordScaleBounds h10 (fordTheorem16_of_scale fordScaleBounds) primeNumberTheoremInput fordUnitPrimeBoxInput
    fordRenewalInput mertensProductInput fordLemma26Input fordLemma51Input fordCoordinateConcentrationInput pptBoundedFiberPropagation

end TotientAsymptotic

end

end OAI
