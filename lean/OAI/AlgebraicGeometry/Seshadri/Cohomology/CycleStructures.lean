import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.PlaneCechLinear

namespace OAI


                                         
section
namespace MaximalSeshadri.PlaneCech
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
instance cyclesAddCommGroup (A B C : Submodule K M) : AddCommGroup (cycles A B C) :=
  Submodule.addCommGroup _
instance cyclesModule (A B C : Submodule K M) : Module K (cycles A B C) :=
  Submodule.module _
instance cyclesHasQuotient (A B C : Submodule K M) :
    HasQuotient (cycles A B C) (Submodule K (cycles A B C)) :=
  Submodule.hasQuotient
end MaximalSeshadri.PlaneCech

end



end OAI
