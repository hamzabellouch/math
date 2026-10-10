import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

namespace OAI

noncomputable section

namespace InvariantRotation.AffiliatedTransport

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

def domainImage (H : E →ₗ.[𝕜] E) (p : Submodule 𝕜 E) : Submodule 𝕜 E :=
  (p.comap H.domain.subtype).map H.toFun

def transported (H : E →ₗ.[𝕜] E) (p : Submodule 𝕜 E) : Submodule 𝕜 E :=
  (domainImage H p).topologicalClosure

variable [CompleteSpace E]

instance transported_hasOrthogonalProjection
    (H : E →ₗ.[𝕜] E) (p : Submodule 𝕜 E) :
    (transported H p).HasOrthogonalProjection := by
  let : IsClosed (transported H p : Set E) :=
    Submodule.isClosed_topologicalClosure _
  infer_instance

end InvariantRotation.AffiliatedTransport

end

end OAI
