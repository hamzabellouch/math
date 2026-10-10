import Mathlib
import OAI.Geometry.HyperbolicGroups.CompactLocalCATGeometric

namespace OAI

section


/-! All existential clauses use
the same selected finite complex and the same actual fundamental group. -/
noncomputable section
namespace HyperbolicObstruction
universe u

theorem main : MainStatement.{u} := by
  obtain ⟨K,x,C,hconn,hasph,_,hC,hfill,hno,hhyp⟩ :=
    IncidenceTemplate.exists_finite_aspherical_hyperbolic_noAction.{u}
  refine ⟨K,x,C,hconn,hasph,hC,hfill,hno,hhyp,?_⟩
  intro L he
  exact homotopy_incompatibleLocalCATNegOne x hno he.some

end HyperbolicObstruction
end
end










end OAI
