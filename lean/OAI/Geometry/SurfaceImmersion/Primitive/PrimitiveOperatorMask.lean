import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveFiberInverse

namespace OAI

/-! Inactive primitive entries may be replaced before estimating the
finite operator; their cutoff is exactly zero. -/
noncomputable section
open Set
open scoped BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance maskFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance maskFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {ι : Type*} [Fintype ι]

lemma completedPrimitiveOperator_mask
    (q : ι → TensorFiber →L[ℝ] ℝ) (w : ι → ℝ)
    (v v₀ : ι → Plane →L[ℝ] ℝ) (S : Set ι) [DecidablePred (· ∈ S)]
    (hz : ∀ a, a ∉ S → w a = 0) :
    completedPrimitiveOperator q w v =
      completedPrimitiveOperator (fun a => if a ∈ S then q a else 0) w
        (fun a => if a ∈ S then v a else v₀ a) := by
  apply ContinuousLinearMap.ext
  intro H
  simp only [completedPrimitiveOperator_apply,finitePrimitiveOperator_apply]
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ S
  · simp only [ha,ite_true]
  · simp only [ha,ite_false,hz a ha,zero_pow (by decide : 2 ≠ 0),zero_mul,zero_smul]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
