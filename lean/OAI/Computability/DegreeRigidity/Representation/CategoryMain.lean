import OAI.Computability.DegreeRigidity.Representation.Reduction
import OAI.Computability.DegreeRigidity.Representation.CategoryAvoidance

namespace OAI

namespace TuringRigidity

theorem inverse_le_realDegree_of_representation (hrep : BorelRepresentation)
    (π : Degree ≃o Degree) (t : ℝ) (ht : Irrational t) (ht0 : 0 < t) (ht1 : t < 1) :
    π.symm (realDegree t) ≤ realDegree t :=
  inverse_le_realDegree_of_obligations hrep cut_arithmetic four_value_recovery
    CategorySearch.category_avoidance π t ht ht0 ht1

theorem main_of_two_obligations (hrep : BorelRepresentation)
    (hcover : IrrationalDegreeCoverage) : MainTheorem :=
  main_of_three_obligations hrep hcover CategorySearch.category_avoidance

end TuringRigidity

end OAI
