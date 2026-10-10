import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveFiberInverse

namespace OAI

/-! Conjugation of the finite primitive operator by tensor coordinates. -/
noncomputable section
open scoped BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance conjugateFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance conjugateFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {ι : Type*} [Fintype ι]

lemma completedPrimitiveOperator_conjugate (e f : TensorFiber →L[ℝ] TensorFiber)
    (q : ι → TensorFiber →L[ℝ] ℝ) (w : ι → ℝ)
    (v v' : ι → Plane →L[ℝ] ℝ)
    (hef : ∀ H, e (f H) = H)
    (hf : ∀ H, tensorSymmetrizer (f H) = f (tensorSymmetrizer H))
    (hv : ∀ a, e ((v a).smulRight (v a)) = (v' a).smulRight (v' a)) :
    e.comp ((completedPrimitiveOperator q w v).comp f) =
      completedPrimitiveOperator (fun a => (q a).comp f) w v' := by
  apply ContinuousLinearMap.ext
  intro H
  simp only [ContinuousLinearMap.comp_apply,completedPrimitiveOperator_apply,
    finitePrimitiveOperator_apply,map_sub,map_add,map_sum,map_smul,hf,hef,hv]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
