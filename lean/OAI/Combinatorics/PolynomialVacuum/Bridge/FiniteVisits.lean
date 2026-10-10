import OAI.Combinatorics.PolynomialVacuum.Bridge.VisitNestingComparison
import OAI.Combinatorics.HoneycombCorridor.VisitRecursion

namespace OAI

namespace PolynomialVacuumBridge.Corridor

 

theorem finite_visits : FiniteVisitsTheorem := by
  refine ⟨finite_visit_recursion,recursion_coefficients_positive,visitMass_ge_three,
    visitMass_mono,?_,?_⟩
  · refine ⟨visitLowerConstant,visitUpperConstant,visit_constants_positive.1,
      visit_constants_positive.2,?_⟩
    intro D v hD hv
    exact visitMass_incident_comparison D v hD hv
  · intro D v hD _
    exact ⟨visitMass_excursion_lower D hD v,visitMass_excursion_upper D v⟩

end PolynomialVacuumBridge.Corridor

end OAI
