import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCoefficientParameters

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators
open Filter

theorem kernelCoefficient_actual_package_eventually (c : ℝ) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ (Z : ℕ) (P : Finset ℕ),
      T/2 ≤ Real.log Z → commonCenterCutoff Z ≤ P.card →
      (∀ p ∈ P, Nat.Prime p) → (∀ p ∈ P, Odd p) →
      ∀ H : ℕ, (∀ p ∈ P, p ≤ H) →
      ∀ ε : ℕ → ℤ, (∀ p ∈ P, ε p = -1 ∨ ε p = 1) →
      let k := evenMomentParameter (parameterX T) Z
      (∀ s, kernelCoefficient P ε k s ≠ 0 →
        0 < s ∧ Squarefree s ∧ Odd s ∧ s ≤ H^k ∧ s.primeFactors.card = k) ∧
      (∑ s ∈ kernelCoefficientInterval (H^k), ‖kernelCoefficient P ε k s‖^2) ≤
        (k.factorial : ℝ)/(P.card : ℝ)^k ∧
      (∀ u : ℤ, c ≤ |signAverage P (fun p => ε p*jacobiSym u p)| →
        c^k/2 ≤ ‖∑ s ∈ kernelCoefficientInterval (H^k),
          kernelCoefficient P ε k s*(jacobiSym u s : ℂ)‖) := by
  filter_upwards [eventually_kernel_population_inputs c hc] with T hparams
  intro Z P hZl hPJ hP ho H hH ε hε
  dsimp only
  have hp := hparams Z P.card hZl hPJ
  refine ⟨fun s hs => kernelCoefficient_support_properties hP ho hH ε hs,
    kernelCoefficient_interval_energy_le hP ho hp.2.2.1 hH ε hε _, ?_⟩
  intro u hu
  rw [kernelCoefficient_character_sum_eq_on_superset ε _ u
    (primeProductSamples_subset_kernelCoefficientInterval hP ho hH)]
  exact kernelCoefficient_character_sum_lower_of_scale hP hp.2.2.1 ε hε
    hp.1 hp.2.1 u hc hu hp.2.2.2.2.2

end Ostmann.QuadraticCenter

end

end OAI
