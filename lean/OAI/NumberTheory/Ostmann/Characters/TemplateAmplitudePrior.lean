import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudePriorSources

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

theorem scheduledPrimePrior_cmean (k j : ℕ) (hj : j < k) (width : Role → ℕ) {Q : ℕ}
    (E₀ : (schedule k 0).Constituent width → Finset (PrimeUpTo Q))
    (hE₀ : ∀ i, 0 < primeShellMass (E₀ i))
    (F : ((schedule k j).Constituent width → PrimeUpTo Q) → ℂ) :
    (scheduledPrimePrior k j width E₀ hE₀).cmean F =
      (outsidePrimePrior (schedule k j) j width (scheduledPrimeShells k width E₀ j)
        (scheduledPrimeShells_positive k width E₀ hE₀ j)).cmean (fun y =>
      (pivotPrimePrior k j hj width (scheduledPrimeShells k width E₀ j)
        (scheduledPrimeShells_positive k width E₀ hE₀ j)).cmean (fun w =>
      (copiedPrimePrior (schedule k j) j width (scheduledPrimeShells k width E₀ j)
        (scheduledPrimeShells_positive k width E₀ hE₀ j)).cmean (fun h =>
        F (scheduledSample k j hj width w h y)))) :=
  scheduled_constituentPrimePrior_cmean k j hj width (scheduledPrimeShells k width E₀ j)
    (scheduledPrimeShells_positive k width E₀ hE₀ j) F

end Ostmann.Characters.Template

end

end OAI
