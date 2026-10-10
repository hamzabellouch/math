import OAI.NumberTheory.JointDickman.Amplification.RationalThresholds
import OAI.NumberTheory.JointDickman.Amplification.Ordering

namespace OAI

/-!
# The joint Dickman law from analytic estimates

The hypotheses express short-interval cancellation, character-distance bounds,
sieve estimates, and the finite-bin Dickman distribution.
-/
namespace JointDickman
open PublishedInputs

section
variable
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceInput) (hFord : FordUpperSieveInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hM : PrimeReciprocalMertensInput) (hMP : PrimeProductMertensInput)
    (hMV : MultiplicativeExponentialInput)
    (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    (hBill : FiniteBinDistributionInput)

include hMR hMRT hKMT hFord hSD hSW hM hMP hMV hMC hBill

theorem jointDickmanLaw_of_published : JointDickmanLaw :=
  jointDickmanLaw_of_rational_fixedScale
    (rationalFixedScaleLaw_of_published hMR hMRT hKMT hFord hSD hSW hM hMP hMV hMC hBill)

theorem increasingOrderLaw_of_published : IncreasingOrderLaw :=
  increasingOrderLaw_of_jointDickmanLaw
    (jointDickmanLaw_of_published hMR hMRT hKMT hFord hSD hSW hM hMP hMV hMC hBill)

theorem decreasingOrderLaw_of_published : DecreasingOrderLaw :=
  decreasingOrderLaw_of_jointDickmanLaw
    (jointDickmanLaw_of_published hMR hMRT hKMT hFord hSD hSW hM hMP hMV hMC hBill)

theorem main_results_of_published :
    JointDickmanLaw ∧ IncreasingOrderLaw ∧ DecreasingOrderLaw :=
  ⟨jointDickmanLaw_of_published hMR hMRT hKMT hFord hSD hSW hM hMP hMV hMC hBill,
    increasingOrderLaw_of_published hMR hMRT hKMT hFord hSD hSW hM hMP hMV hMC hBill,
    decreasingOrderLaw_of_published hMR hMRT hKMT hFord hSD hSW hM hMP hMV hMC hBill⟩

end
end JointDickman

end OAI
