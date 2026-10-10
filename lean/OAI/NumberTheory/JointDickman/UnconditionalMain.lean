import OAI.NumberTheory.JointDickman.Amplification.RationalThresholdsDischarge
import OAI.NumberTheory.JointDickman.DischargedMain

namespace OAI

/-!
# The joint Dickman law and both strict ordering densities

The joint distribution follows from character-distance divergence, upper sieves,
Selberg–Delange estimates, concentration, and finite-bin Dickman distributions.
-/
namespace JointDickman

theorem rationalFixedScaleLaw_unconditional : RationalFixedScaleLaw :=
  rationalFixedScaleLaw_of_distance_divergence_proved characterDistanceDivergence
    fordUpperSieveInput squarefreeSelbergDelangeInput squarefreeCharacterEstimateInput
    primeReciprocalMertensInput primeProductMertensInput
    (fun _ M => finiteMcDiarmidInput M) finiteBinDistributionInput

theorem jointDickmanLaw_unconditional : JointDickmanLaw :=
  jointDickmanLaw_of_rational_fixedScale rationalFixedScaleLaw_unconditional

theorem increasingOrderLaw_unconditional : IncreasingOrderLaw :=
  increasingOrderLaw_of_jointDickmanLaw jointDickmanLaw_unconditional

theorem decreasingOrderLaw_unconditional : DecreasingOrderLaw :=
  decreasingOrderLaw_of_jointDickmanLaw jointDickmanLaw_unconditional

theorem main_results_unconditional :
    JointDickmanLaw ∧ IncreasingOrderLaw ∧ DecreasingOrderLaw :=
  ⟨jointDickmanLaw_unconditional,increasingOrderLaw_unconditional,decreasingOrderLaw_unconditional⟩

end JointDickman

end OAI
