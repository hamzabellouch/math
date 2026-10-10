import OAI.Combinatorics.Ramsey.CycleClique.Construction.TriangleFacts

namespace OAI

namespace CycleClique.Construction
/-- The excluded pair in the cycle–clique formula has Ramsey number six. -/
theorem triangle_ramsey : IsRamseyNumber 3 3 6 :=
  isRamseyNumber_of_upper_lower triangle_upper triangle_lower

end CycleClique.Construction

end OAI
