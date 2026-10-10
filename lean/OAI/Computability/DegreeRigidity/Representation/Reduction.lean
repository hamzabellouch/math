import OAI.Computability.DegreeRigidity.Computability.CutArithmetic
import OAI.Computability.DegreeRigidity.Computability.EffectiveRecovery

namespace OAI

namespace TuringRigidity

theorem main_of_three_obligations (hrep : BorelRepresentation)
    (hcover : IrrationalDegreeCoverage) (havoid : CategoryAvoidance) : MainTheorem :=
  main_of_obligations hrep cut_arithmetic hcover four_value_recovery havoid

end TuringRigidity

end OAI
