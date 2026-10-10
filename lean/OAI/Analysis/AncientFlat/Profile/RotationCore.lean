import Mathlib

namespace OAI
noncomputable section
open Set Filter
open scoped ZeroAtInfty BoundedContinuousFunction
namespace FlatSymmetry
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
def rotMap (R : V ≃ₗᵢ[ℝ] V) : C(V,V) := ⟨R,R.continuous⟩
def rotate (R : V ≃ₗᵢ[ℝ] V) : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ) :=
  (ZeroAtInftyContinuousMap.compLinearMap (R := ℂ) R.toHomeomorph.toCocompactMap).mkContinuous 1
    (fun f => by
      change ‖f.toBCF.compContinuous (rotMap R)‖≤1*‖f.toBCF‖
      simpa only [one_mul] using f.toBCF.norm_compContinuous_le (rotMap R))
@[simp] lemma rotate_apply (R : V ≃ₗᵢ[ℝ] V) (f : C₀(V,ℂ)) (x : V) :
    rotate R f x=f (R x) := rfl
end FlatSymmetry

end

end OAI
