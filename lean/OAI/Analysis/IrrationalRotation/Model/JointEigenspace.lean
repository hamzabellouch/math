import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

noncomputable section
namespace Invariant233

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

def jointEigenspace (D : ι → H →L[ℂ] H) (ev : ι → ℂ) : Submodule ℂ H :=
  ⨅ i, Module.End.eigenspace (D i).toLinearMap (ev i)

instance isClosed_jointEigenspace (D : ι → H →L[ℂ] H) (ev : ι → ℂ) :
    IsClosed (jointEigenspace D ev : Set H) := by
  unfold jointEigenspace
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun i => ContinuousLinearMap.isClosed_eigenspace (D i) (ev i)

def jointEigenprojection (D : ι → H →L[ℂ] H) (ev : ι → ℂ) : H →L[ℂ] H :=
  (jointEigenspace D ev).starProjection

end Invariant233

end

end OAI
