import OAI.Computability.DegreeRigidity.Representation.CategoryMain
import OAI.Computability.DegreeRigidity.Computability.DegreeCoverage

namespace OAI

namespace TuringRigidity

theorem main_of_representation (hrep : BorelRepresentation) : MainTheorem :=
  main_of_two_obligations hrep irrational_degree_coverage

end TuringRigidity

end OAI
